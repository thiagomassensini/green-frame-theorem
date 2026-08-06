#!/usr/bin/env python3
"""Verify the preserved paper specification byte-for-byte by SHA-256."""
from __future__ import annotations

import hashlib
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EXPECTED = "366dfa007002c1d3dbf2eb7c283c13c1b35233647163753ee39e45dd0645c3f4"
PATH = ROOT / "docs/90_PAPER_SPECIFICATION.md"
actual = hashlib.sha256(PATH.read_bytes()).hexdigest()
if actual != EXPECTED:
    print(f"ERROR: source specification digest changed: {actual}", file=sys.stderr)
    raise SystemExit(1)
print(f"PASS: source specification SHA-256 {actual}")
