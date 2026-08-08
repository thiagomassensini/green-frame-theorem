#!/usr/bin/env python3
"""Materialize the primary paper directly from its byte-preserved research input."""
from __future__ import annotations

import json

from audit_common import ROOT, die, sha256


def main() -> int:
    contract = json.loads((ROOT / "audit/release-contract.json").read_text())
    research = contract["research"]
    source = ROOT / research["directory"] / research["primary"]
    destination = ROOT / research["materialized_copy"]
    manifest = json.loads((ROOT / research["manifest"]).read_text())
    matches = [
        entry for entry in manifest.get("files", [])
        if entry.get("name") == research["primary"]
    ]
    if len(matches) != 1:
        die("primary paper must occur exactly once in the source manifest")
    expected = matches[0].get("sha256")
    observed = sha256(source)
    if observed != expected:
        die(f"primary paper digest {observed} differs from manifest {expected}")
    raw = source.read_bytes()
    destination.parent.mkdir(parents=True, exist_ok=True)
    temporary = destination.with_suffix(destination.suffix + ".tmp")
    temporary.write_bytes(raw)
    temporary.replace(destination)
    if destination.read_bytes() != raw:
        die("materialized primary paper differs byte-for-byte from its input")
    print(
        f"PASS: materialized {destination.relative_to(ROOT)}; "
        f"bytes={len(raw)}; sha256={observed}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
