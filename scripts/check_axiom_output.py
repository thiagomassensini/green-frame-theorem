#!/usr/bin/env python3
"""Reject any registered theorem axiom outside Lean's standard trusted allowlist."""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ALLOWED = {"propext", "Quot.sound", "Classical.choice"}
ROOT = Path(__file__).resolve().parents[1]


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: check_axiom_output.py AXIOM_LOG", file=sys.stderr)
        return 2
    registry = json.loads((ROOT / "audit/theorem-registry.json").read_text())
    expected = len(registry["theorems"])
    text = Path(sys.argv[1]).read_text(encoding="utf-8")
    no_axiom_reports = len(re.findall(r" does not depend on any axioms", text))
    blocks = re.findall(r" depends on axioms:\s*\[([^\]]*)\]", text)
    report_count = no_axiom_reports + len(blocks)
    if report_count != expected:
        print(f"ERROR: expected {expected} axiom reports, found {report_count}", file=sys.stderr)
        return 1
    used: set[str] = set()
    for block in blocks:
        used.update(item.strip() for item in block.split(",") if item.strip())
    forbidden = used - ALLOWED
    if forbidden:
        print(f"ERROR: forbidden axioms: {sorted(forbidden)}", file=sys.stderr)
        return 1
    print(
        f"PASS: {expected} axiom reports; used={sorted(used)}; "
        f"allowlist={sorted(ALLOWED)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
