#!/usr/bin/env python3
"""Reconstruct the byte-preserved paper specification from tracked chunks."""
from __future__ import annotations

import base64
import gzip
import hashlib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE_DIR = ROOT / "docs/source"
OUTPUT = ROOT / "docs/90_PAPER_SPECIFICATION.md"
EXPECTED_SHA256 = "366dfa007002c1d3dbf2eb7c283c13c1b35233647163753ee39e45dd0645c3f4"
EXPECTED_SIZE = 50630

parts = sorted(SOURCE_DIR.glob("TEOREMA_FRAME_GREEN_TODAS_AS_BASES.md.gz.b64.*"))
if len(parts) != 3:
    raise SystemExit(f"ERROR: expected 3 source chunks, found {len(parts)}")
payload = "".join(part.read_text(encoding="ascii").strip() for part in parts)
raw = gzip.decompress(base64.b64decode(payload, validate=True))
actual_sha256 = hashlib.sha256(raw).hexdigest()
if len(raw) != EXPECTED_SIZE:
    raise SystemExit(f"ERROR: source size {len(raw)} != {EXPECTED_SIZE}")
if actual_sha256 != EXPECTED_SHA256:
    raise SystemExit(
        f"ERROR: source SHA-256 {actual_sha256} != {EXPECTED_SHA256}"
    )
OUTPUT.write_bytes(raw)
print(
    f"PASS: materialized {OUTPUT.relative_to(ROOT)}; "
    f"bytes={len(raw)}; sha256={actual_sha256}"
)
