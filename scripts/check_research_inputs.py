#!/usr/bin/env python3
"""Gate G3: verify the exact 16-file research corpus byte-for-byte."""
from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

from audit_common import EVIDENCE, ROOT, checked_output, die, sha256, write_json


def main() -> int:
    contract = json.loads((ROOT / "audit/release-contract.json").read_text())
    settings = contract["research"]
    manifest_path = ROOT / settings["manifest"]
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    entries = manifest.get("files", [])
    if manifest.get("count") != len(entries):
        die("research source manifest count differs from its entries")
    if len(entries) != settings["expected_count"]:
        die(
            f"research input count {len(entries)} != contract "
            f"{settings['expected_count']}"
        )
    names = [entry["name"] for entry in entries]
    if names != sorted(names) or len(names) != len(set(names)):
        die("research source manifest names must be unique and sorted")
    for entry in entries:
        name = entry["name"]
        if Path(name).name != name or name in {".", ".."}:
            die(f"research input name must be one plain filename: {name!r}")
        if not re.fullmatch(r"[0-9a-f]{64}", entry.get("sha256", "")):
            die(f"invalid SHA-256 for research input {entry.get('name')}")

    input_dir = ROOT / settings["directory"]
    if not input_dir.is_dir() or input_dir.is_symlink():
        die(f"research input directory is missing or unsafe: {input_dir}")
    actual_entries = sorted(input_dir.iterdir(), key=lambda path: path.name)
    actual_names = [path.name for path in actual_entries]
    if actual_names != names:
        die(
            "research input directory entries differ from manifest; "
            f"unexpected={sorted(set(actual_names) - set(names))}; "
            f"missing={sorted(set(names) - set(actual_names))}"
        )
    all_tracked = set(checked_output("git", "ls-files").splitlines())
    required_tracked = {
        settings["manifest"],
        "research/SOURCE_MANIFEST.md",
        "scripts/materialize_source.py",
    }
    missing_required = sorted(required_tracked - all_tracked)
    if missing_required:
        die(f"source-audit files are not tracked by Git: {missing_required}")
    tracked = set(checked_output("git", "ls-files", settings["directory"]).splitlines())
    expected_tracked = {
        (Path(settings["directory"]) / name).as_posix() for name in names
    }
    if tracked != expected_tracked:
        die(
            "research input Git tracking differs from the exact source manifest; "
            f"unexpected={sorted(tracked - expected_tracked)}; "
            f"missing={sorted(expected_tracked - tracked)}"
        )
    verified: list[dict[str, str]] = []
    for entry in entries:
        path = input_dir / entry["name"]
        if path.is_symlink():
            die(f"research input must not be a symlink: {entry['name']}")
        if not path.is_file():
            die(f"research input must be a regular file: {entry['name']}")
        actual = sha256(path)
        if actual != entry["sha256"]:
            die(f"research input digest mismatch: {entry['name']} -> {actual}")
        verified.append({"name": entry["name"], "sha256": actual})

    human_manifest = (ROOT / "research/SOURCE_MANIFEST.md").read_text(encoding="utf-8")
    for entry in entries:
        if human_manifest.count(f"`{entry['name']}`") != 1:
            die(f"human source manifest does not name {entry['name']} exactly once")
        if human_manifest.count(f"`{entry['sha256']}`") != 1:
            die(f"human source manifest does not contain digest for {entry['name']}")

    subprocess.run(
        [sys.executable, str(ROOT / "scripts/materialize_source.py")],
        cwd=ROOT,
        check=True,
    )
    primary = input_dir / settings["primary"]
    materialized = ROOT / settings["materialized_copy"]
    if materialized.read_bytes() != primary.read_bytes():
        die("materialized primary paper differs byte-for-byte from research input")

    result = {
        "schema": "org.green-frame.source-provenance/v2",
        "count": len(verified),
        "files": verified,
        "primary": {
            "name": settings["primary"],
            "sha256": sha256(primary),
            "materialized_copy": settings["materialized_copy"],
        },
        "manifest_sha256": sha256(manifest_path),
    }
    write_json(EVIDENCE / "source-provenance.json", result)
    print(
        f"PASS G3: {len(verified)}/{settings['expected_count']} exact research inputs; "
        f"primary={result['primary']['sha256']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
