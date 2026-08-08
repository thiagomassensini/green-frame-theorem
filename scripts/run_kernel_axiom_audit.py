#!/usr/bin/env python3
"""Run GreenFrame/Audit.lean and preserve its complete combined output."""
from __future__ import annotations

import subprocess
import sys

from audit_common import ROOT


def main() -> int:
    output = ROOT / "audit/axioms.txt"
    result = subprocess.run(
        ["lake", "env", "lean", "GreenFrame/Audit.lean"],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    output.write_bytes(result.stdout)
    sys.stdout.buffer.write(result.stdout)
    sys.stdout.buffer.flush()
    if result.returncode != 0:
        return result.returncode
    return subprocess.run(
        [
            sys.executable,
            "scripts/check_axiom_output.py",
            "audit/axioms.txt",
            "--output",
            "audit/evidence/axiom-report.json",
        ],
        cwd=ROOT,
    ).returncode


if __name__ == "__main__":
    raise SystemExit(main())
