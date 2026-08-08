#!/usr/bin/env python3
"""Gate G1: bind the audit to one clean Git tree and pinned toolchain."""
from __future__ import annotations

import json
import os
import platform
import re
import subprocess
import tomllib
from datetime import date
from pathlib import Path

from audit_common import EVIDENCE, ROOT, checked_output, die, sha256, write_json


def main() -> int:
    contract = json.loads((ROOT / "audit/release-contract.json").read_text())
    commit = checked_output("git", "rev-parse", "HEAD")
    tree = checked_output("git", "rev-parse", "HEAD^{tree}")
    parents = checked_output("git", "show", "-s", "--format=%P", "HEAD").split()
    expected = os.environ.get("AUDITED_SHA", commit)
    if not re.fullmatch(r"[0-9a-f]{40}", expected):
        die(f"AUDITED_SHA is not an exact 40-hex commit: {expected!r}")
    if commit != expected:
        die(f"checkout HEAD {commit} != AUDITED_SHA {expected}")
    expected_parent = os.environ.get("EXPECTED_PARENT_SHA", "")
    if expected_parent:
        if not re.fullmatch(r"[0-9a-f]{40}", expected_parent):
            die("EXPECTED_PARENT_SHA is not an exact 40-hex commit")
        if not parents or parents[0] != expected_parent:
            die(
                f"first parent {parents[0] if parents else '<none>'} != "
                f"EXPECTED_PARENT_SHA {expected_parent}"
            )
    dirty = checked_output("git", "status", "--porcelain", "--untracked-files=all")
    if dirty:
        die("checkout has tracked changes or nonignored untracked files before the audit")

    pins = contract["toolchain"]
    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    if toolchain != pins["lean_toolchain"]:
        die("lean-toolchain differs from the immutable release contract")
    match = re.fullmatch(r"leanprover/lean4:v([0-9]+\.[0-9]+\.[0-9]+)", toolchain)
    if not match:
        die(f"lean-toolchain is not an exact Lean release: {toolchain}")
    pinned_lean = match.group(1)
    if pinned_lean != pins["lean_version"]:
        die("Lean version differs from the immutable release contract")
    lean_version = checked_output("lean", "--version")
    lake_version = checked_output("lake", "--version")
    if f"version {pinned_lean}" not in lean_version:
        die(f"active Lean differs from lean-toolchain: {lean_version}")

    lakefile = tomllib.loads((ROOT / "lakefile.toml").read_text(encoding="utf-8"))
    requires = lakefile.get("require", [])
    mathlib_inputs = [entry for entry in requires if entry.get("name") == "mathlib"]
    if len(mathlib_inputs) != 1:
        die("lakefile.toml must contain exactly one Mathlib requirement")
    expected_mathlib_input = pins["mathlib_input_revision"]
    if expected_mathlib_input != f"v{pinned_lean}":
        die("contracted Mathlib input tag does not match the Lean release")
    if mathlib_inputs[0].get("git") != pins["mathlib_url"]:
        die("Mathlib URL differs from the immutable release contract")
    if mathlib_inputs[0].get("rev") != expected_mathlib_input:
        die("Mathlib input tag does not match the pinned Lean release")

    lake_manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    resolved_dependencies: list[dict[str, str]] = []
    for package in lake_manifest.get("packages", []):
        revision = str(package.get("rev", ""))
        if package.get("type") != "git" or not re.fullmatch(r"[0-9a-f]{40}", revision):
            die(f"dependency {package.get('name')} lacks an immutable Git revision")
        resolved_dependencies.append(
            {
                "name": str(package.get("name", "")),
                "url": str(package.get("url", "")),
                "input_revision": str(package.get("inputRev", "")),
                "commit": revision,
            }
        )
    mathlib_packages = [
        package for package in lake_manifest.get("packages", [])
        if package.get("name") == "mathlib"
    ]
    if len(mathlib_packages) != 1:
        die("lake-manifest.json must contain exactly one Mathlib package")
    mathlib = mathlib_packages[0]
    if mathlib.get("url") != pins["mathlib_url"]:
        die("resolved Mathlib URL differs from the immutable release contract")
    if mathlib.get("inputRev") != expected_mathlib_input:
        die("resolved Mathlib input tag differs from lakefile.toml")
    if mathlib.get("rev") != pins["mathlib_commit"]:
        die("resolved Mathlib commit differs from the immutable release contract")

    action_pins: list[dict[str, str]] = []
    workflow_paths = sorted(
        {
            *(ROOT / ".github/workflows").glob("*.yml"),
            *(ROOT / ".github/workflows").glob("*.yaml"),
        }
    )
    for workflow in workflow_paths:
        text = workflow.read_text(encoding="utf-8")
        for action, ref in re.findall(r"uses:\s*([^@\s]+)@([^\s#]+)", text):
            if not re.fullmatch(r"[0-9a-f]{40}", ref):
                die(f"mutable Action ref in {workflow.relative_to(ROOT)}: {action}@{ref}")
            action_pins.append({"action": action, "sha": ref})

    release = contract["release"]
    if not re.fullmatch(r"[0-9]+\.[0-9]+\.[0-9]+", release["version"]):
        die("release contract version is not a plain semantic version")
    if release["tag"] != f"v{release['version']}":
        die("release contract tag does not equal v<version>")
    expected_tagger = {
        "name": "github-actions[bot]",
        "email": "41898282+github-actions[bot]@users.noreply.github.com",
        "date_source": "target_committer_timestamp",
    }
    if release.get("tagger") != expected_tagger:
        die("release tagger policy differs from the immutable v2 contract")
    try:
        date.fromisoformat(release["date"])
    except (TypeError, ValueError):
        die("release contract date is not an ISO calendar date")
    package_version = str(lakefile.get("version", ""))
    if package_version != release["version"]:
        die(f"lakefile version {package_version} != contract {release['version']}")
    expected_notes_path = f".release/v{release['version']}.md"
    if release.get("notes") != expected_notes_path:
        die(f"release notes path must be {expected_notes_path}")
    notes = ROOT / release["notes"]
    if not notes.is_file() or not notes.read_text(encoding="utf-8").strip():
        die(f"missing or empty release notes: {notes.relative_to(ROOT)}")
    citation = (ROOT / "CITATION.cff").read_text(encoding="utf-8")
    if not re.search(
        rf"^version:\s*['\"]?{re.escape(release['version'])}['\"]?\s*$",
        citation,
        re.MULTILINE,
    ):
        die("CITATION.cff version differs from the release contract")
    if not re.search(
        rf"^date-released:\s*['\"]?{re.escape(release['date'])}['\"]?\s*$",
        citation,
        re.MULTILINE,
    ):
        die("CITATION.cff release date differs from the release contract")
    zenodo = json.loads((ROOT / ".zenodo.json").read_text(encoding="utf-8"))
    if str(zenodo.get("version")) != release["version"]:
        die(".zenodo.json version differs from the release contract")
    if str(zenodo.get("publication_date")) != release["date"]:
        die(".zenodo.json publication date differs from the release contract")

    upstream_id = os.environ.get("UPSTREAM_AUDIT_RUN_ID", "")
    if upstream_id:
        publication_expectations = {
            "UPSTREAM_AUDIT_HEAD_SHA": commit,
            "UPSTREAM_AUDIT_STATUS": "completed",
            "UPSTREAM_AUDIT_CONCLUSION": "success",
            "UPSTREAM_AUDIT_EVENT": "push",
            "UPSTREAM_AUDIT_HEAD_BRANCH": "main",
            "UPSTREAM_AUDIT_WORKFLOW_PATH": ".github/workflows/lean-audit.yml",
        }
        if not re.fullmatch(r"[0-9]+", upstream_id):
            die("UPSTREAM_AUDIT_RUN_ID is not numeric")
        for variable, wanted in publication_expectations.items():
            if os.environ.get(variable, "") != wanted:
                die(f"publication evidence {variable} differs from {wanted!r}")
        for variable in ("UPSTREAM_AUDIT_RUN_ATTEMPT", "UPSTREAM_AUDIT_WORKFLOW_ID"):
            if not re.fullmatch(r"[0-9]+", os.environ.get(variable, "")):
                die(f"publication evidence {variable} is not numeric")
        for variable in ("UPSTREAM_AUDIT_CREATED_AT", "UPSTREAM_AUDIT_UPDATED_AT"):
            if not os.environ.get(variable, ""):
                die(f"publication evidence {variable} is empty")
        if os.environ.get("GITHUB_WORKFLOW_SHA", "") != commit:
            die("publisher workflow definition SHA differs from the audited commit")
        if os.environ.get("GITHUB_SHA", "") != commit:
            die("publisher dispatch SHA differs from the audited commit")
        if os.environ.get("GITHUB_REF", "") != "refs/heads/main":
            die("publisher was not dispatched from refs/heads/main")
        for variable in ("GITHUB_RUN_ID", "GITHUB_RUN_ATTEMPT"):
            if not re.fullmatch(r"[0-9]+", os.environ.get(variable, "")):
                die(f"publisher evidence {variable} is not numeric")
        if os.environ.get("GITHUB_JOB", "") != "audit":
            die("seven-gate publisher audit did not run in the read-only audit job")
        repository = os.environ.get("GITHUB_REPOSITORY", "")
        if not re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repository):
            die("publisher repository identity is empty or malformed")
        publisher_name = f"publish-v{release['version']}.yml"
        wanted_workflow_ref = (
            f"{repository}/.github/workflows/{publisher_name}@refs/heads/main"
        )
        if os.environ.get("GITHUB_WORKFLOW_REF", "") != wanted_workflow_ref:
            die(f"publisher workflow ref is not {publisher_name} on main")
        wanted_upstream_url = (
            f"{os.environ.get('GITHUB_SERVER_URL', 'https://github.com')}/"
            f"{repository}/actions/runs/{upstream_id}"
        )
        if os.environ.get("UPSTREAM_AUDIT_URL", "") != wanted_upstream_url:
            die("upstream audit URL differs from its run identity")

    result = {
        "schema": "org.green-frame.revision-identity/v2",
        "commit": commit,
        "tree": tree,
        "parents": parents,
        "tracked_file_count": len(
            checked_output("git", "ls-tree", "-r", "--name-only", "HEAD").splitlines()
        ),
        "release": release,
        "toolchain": {
            "lean_toolchain": toolchain,
            "lean_version": lean_version,
            "lake_version": lake_version,
            "mathlib_input": mathlib["inputRev"],
            "mathlib_commit": mathlib["rev"],
            "resolved_dependencies": resolved_dependencies,
            "lake_manifest_sha256": sha256(ROOT / "lake-manifest.json"),
        },
        "actions": action_pins,
        "runtime": {
            "python": platform.python_version(),
            "system": platform.system(),
            "machine": platform.machine(),
        },
        "github": {
            "repository": os.environ.get("GITHUB_REPOSITORY", ""),
            "run_id": os.environ.get("GITHUB_RUN_ID", ""),
            "run_attempt": os.environ.get("GITHUB_RUN_ATTEMPT", ""),
            "workflow": os.environ.get("GITHUB_WORKFLOW", ""),
            "workflow_ref": os.environ.get("GITHUB_WORKFLOW_REF", ""),
            "workflow_sha": os.environ.get("GITHUB_WORKFLOW_SHA", ""),
            "github_sha": os.environ.get("GITHUB_SHA", ""),
            "event_name": os.environ.get("GITHUB_EVENT_NAME", ""),
            "ref": os.environ.get("GITHUB_REF", ""),
            "job": os.environ.get("GITHUB_JOB", ""),
            "runner_os": os.environ.get("RUNNER_OS", ""),
            "runner_arch": os.environ.get("RUNNER_ARCH", ""),
            "runner_image_os": os.environ.get("ImageOS", ""),
            "runner_image_version": os.environ.get("ImageVersion", ""),
            "expected_parent_sha": os.environ.get("EXPECTED_PARENT_SHA", ""),
            "upstream_audit_run_id": upstream_id,
            "upstream_audit": {
                "head_sha": os.environ.get("UPSTREAM_AUDIT_HEAD_SHA", ""),
                "status": os.environ.get("UPSTREAM_AUDIT_STATUS", ""),
                "conclusion": os.environ.get("UPSTREAM_AUDIT_CONCLUSION", ""),
                "event": os.environ.get("UPSTREAM_AUDIT_EVENT", ""),
                "head_branch": os.environ.get("UPSTREAM_AUDIT_HEAD_BRANCH", ""),
                "workflow_path": os.environ.get("UPSTREAM_AUDIT_WORKFLOW_PATH", ""),
                "run_attempt": os.environ.get("UPSTREAM_AUDIT_RUN_ATTEMPT", ""),
                "workflow_id": os.environ.get("UPSTREAM_AUDIT_WORKFLOW_ID", ""),
                "created_at": os.environ.get("UPSTREAM_AUDIT_CREATED_AT", ""),
                "updated_at": os.environ.get("UPSTREAM_AUDIT_UPDATED_AT", ""),
                "url": os.environ.get("UPSTREAM_AUDIT_URL", ""),
            },
        },
    }
    write_json(EVIDENCE / "revision-identity.json", result)
    print(
        f"PASS G1: commit={commit}; tree={tree}; Lean={pinned_lean}; "
        f"Mathlib={mathlib['rev']}; Action pins={len(action_pins)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
