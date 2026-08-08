#!/usr/bin/env python3
"""Check that the v1.0.1 maintenance release is internally consistent."""
from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
VERSION = "1.0.1"
TAG = f"v{VERSION}"
RELEASE_DATE = "2026-08-08"
LEAN_SOURCE_DIGEST = "a14126454631de32f6b51a316f74d8ee97b410f7ac28896f17bc383206ad2ec1"
CLAIM_LEDGER_DIGEST = "600d86b4fda635d1e72ab8ed4f0d822d24e66cbd114892c8aaf572c83a7c6c75"


def fail(message: str) -> None:
    print(f"ERROR: {message}", file=sys.stderr)
    raise SystemExit(1)


def require(condition: bool, message: str) -> None:
    if not condition:
        fail(message)


def read(relative: str) -> str:
    return (ROOT / relative).read_text(encoding="utf-8")


def main() -> int:
    lake = read("lakefile.toml")
    require(
        re.search(rf'^version = "{re.escape(VERSION)}"$', lake, re.MULTILINE)
        is not None,
        "Lake package version does not match v1.0.1",
    )

    citation = read("CITATION.cff")
    require(
        re.search(rf"^version: {re.escape(VERSION)}$", citation, re.MULTILINE)
        is not None,
        "CITATION.cff version does not match v1.0.1",
    )
    require(
        re.search(
            rf"^date-released: {re.escape(RELEASE_DATE)}$", citation, re.MULTILINE
        )
        is not None,
        "CITATION.cff release date does not match the publication date",
    )

    zenodo = json.loads(read(".zenodo.json"))
    require(zenodo.get("version") == VERSION, ".zenodo.json version mismatch")

    readme = read("README.md")
    require(TAG in readme, "README does not document v1.0.1")

    notes = read(".release/v1.0.1.md")
    require(
        notes.startswith("# Green Frame Theorem v1.0.1\n"),
        "v1.0.1 release notes have the wrong title",
    )
    require(
        "no new mathematical or spectral claim" in notes,
        "v1.0.1 release notes do not state the semantic firewall",
    )

    ledger = read("audit/CLAIM_LEDGER.md")
    require(
        hashlib.sha256(ledger.encode("utf-8")).hexdigest() == CLAIM_LEDGER_DIGEST,
        "claim ledger text differs from the independently reviewed v1.0.1 boundary",
    )
    coverage_rows = []
    for line in ledger.splitlines():
        if not line.startswith("| ABGF-"):
            continue
        cells = [cell.strip() for cell in line.strip("|").split("|")]
        require(len(cells) == 5, f"malformed claim-ledger row: {line}")
        coverage_rows.append((cells[0], cells[3]))
    expected_coverage = {
        "ABGF-AR-001": "SOURCE_BOUNDARY",
        "ABGF-AR-002": "KERNEL_PARTIAL",
        "ABGF-AR-003": "SOURCE_BOUNDARY",
        "ABGF-AN-001": "KERNEL_INTERFACE_ONLY",
        "ABGF-AN-002": "SOURCE_BOUNDARY",
        "ABGF-GR-001": "KERNEL_EXACT",
        "ABGF-GR-002": "KERNEL_PARTIAL",
        "ABGF-GR-003": "SOURCE_BOUNDARY",
        "ABGF-GR-004": "KERNEL_PARTIAL",
        "ABGF-FR-001": "KERNEL_ABSTRACT",
        "ABGF-FR-002": "KERNEL_PARTIAL",
        "ABGF-FR-003": "KERNEL_INTERFACE_ONLY",
        "ABGF-PO-001": "SOURCE_BOUNDARY",
        "ABGF-PO-002": "SOURCE_BOUNDARY",
        "ABGF-PO-003": "KERNEL_ABSTRACT",
        "ABGF-PO-004": "KERNEL_ABSTRACT",
        "ABGF-BK-001": "KERNEL_PARTIAL",
        "ABGF-BK-002": "SOURCE_BOUNDARY",
        "ABGF-FS-001": "KERNEL_PARTIAL",
        "ABGF-FS-002": "SOURCE_BOUNDARY",
        "ABGF-FS-003": "SOURCE_BOUNDARY",
        "ABGF-FS-004": "FUTURE_LAYER",
        "ABGF-WEYL-001": "FUTURE_LAYER",
    }
    require(
        len(coverage_rows) == len(dict(coverage_rows)),
        "claim ledger contains a duplicate paper ID",
    )
    require(
        dict(coverage_rows) == expected_coverage,
        "claim ledger ID-to-coverage mapping differs from the audited boundary",
    )

    publisher = read(".github/workflows/publish-v1.0.1.yml")
    required_publisher_fragments = (
        "publish-v1.0.1-trigger",
        "TAG: v1.0.1",
        ".release/TRIGGER_v1.0.1.md",
        "steps.target.outputs.sha",
        "--prefix=green-frame-theorem-v1.0.1/",
        "--draft",
        "--draft=false",
        "gh release download",
        "sha256sum --check SHA256SUMS.txt",
    )
    for fragment in required_publisher_fragments:
        require(fragment in publisher, f"publisher is missing: {fragment}")
    require(
        "workflow_dispatch" not in publisher,
        "publisher must be tied to the exact trigger commit, not manual dispatch",
    )

    lean_paths = [
        ROOT / "GreenFrame.lean",
        *sorted((ROOT / "GreenFrame").rglob("*.lean")),
    ]
    lean_digest = hashlib.sha256()
    for path in lean_paths:
        relative = path.relative_to(ROOT).as_posix()
        lean_digest.update(relative.encode("utf-8"))
        lean_digest.update(b"\0")
        lean_digest.update(path.read_bytes())
        lean_digest.update(b"\0")
    require(
        lean_digest.hexdigest() == LEAN_SOURCE_DIGEST,
        "Lean source digest differs from the audited v1.0.0 core",
    )

    print(
        "PASS: v1.0.1 metadata, exact 23-claim conservative ledger, "
        "maintenance-only Lean diff, and draft-first publisher"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
