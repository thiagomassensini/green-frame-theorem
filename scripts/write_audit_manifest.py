#!/usr/bin/env python3
"""Create the run-bound, exact-tree audit manifest after all seven gates pass."""
from __future__ import annotations

import json
import os

from audit_common import EVIDENCE, ROOT, die, sha256, write_json


def read(name: str) -> dict:
    return json.loads((EVIDENCE / name).read_text(encoding="utf-8"))


def main() -> int:
    gates = read("gates.json")
    contract = json.loads((ROOT / "audit/release-contract.json").read_text())
    expected_gate_ids = contract["audit"]["gate_ids"]
    gate_records = gates.get("gates", [])
    if (
        gates.get("count") != len(expected_gate_ids)
        or len(gate_records) != len(expected_gate_ids)
        or [gate.get("id") for gate in gate_records] != expected_gate_ids
        or any(gate.get("status") != "PASS" for gate in gate_records)
    ):
        die("audit manifest requires exactly seven PASS gates")
    revision = read("revision-identity.json")
    consistency = read("evidence-consistency.json")
    graph = read("reachable-import-graph.json")
    sources = read("source-provenance.json")
    axioms = read("axiom-report.json")
    inventory = read("repository-inventory.json")
    if (revision["commit"], revision["tree"]) != (
        consistency["commit"], consistency["tree"]
    ):
        die("manifest inputs disagree on Git identity")

    evidence_hashes: dict[str, str] = {}
    for path in sorted(EVIDENCE.rglob("*")):
        if path.is_file() and path.name not in {
            "audit-manifest.json",
            "audit-manifest.json.tmp",
        }:
            evidence_hashes[path.relative_to(ROOT).as_posix()] = sha256(path)

    github = revision["github"]
    server = os.environ.get("GITHUB_SERVER_URL", "https://github.com")
    repository = github.get("repository", "")
    run_id = github.get("run_id", "")
    run_url = (
        f"{server}/{repository}/actions/runs/{run_id}"
        if repository and run_id else ""
    )
    upstream = github.get("upstream_audit_run_id", "")
    upstream_url = (
        f"{server}/{repository}/actions/runs/{upstream}"
        if repository and upstream else ""
    )
    manifest = {
        "schema": "org.green-frame.audit-manifest/v2",
        "release": contract["release"],
        "git": {
            "commit": revision["commit"],
            "tree": revision["tree"],
            "parents": revision["parents"],
            "tracked_file_count": revision["tracked_file_count"],
        },
        "toolchain": revision["toolchain"],
        "execution": {
            **github,
            "run_url": run_url,
            "upstream_audit_run_url": upstream_url,
        },
        "counts": consistency["counts"],
        "trust": {
            "allowed_axioms": consistency["allowed_axioms"],
            "used_axioms": consistency["used_axioms"],
            "exact_axiom_report_count": axioms["count"],
            "exact_axiom_report_sha256": sha256(EVIDENCE / "axiom-report.json"),
        },
        "closure": {
            "root_module": graph["root"],
            "reachable_module_count": graph["reachable_module_count"],
            "unreachable_modules": graph["unreachable_modules"],
            "research_input_count": sources["count"],
            "documentation_file_count": inventory["counts"]["documentation_files"],
        },
        "identity_sha256": consistency["identity_sha256"],
        "research_inputs": sources["files"],
        "gates": gates["gates"],
        "evidence_sha256": evidence_hashes,
    }
    write_json(EVIDENCE / "audit-manifest.json", manifest)
    print(
        f"PASS: audit manifest commit={revision['commit']} tree={revision['tree']} "
        f"run={run_id or 'non-GitHub'}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
