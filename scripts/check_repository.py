#!/usr/bin/env python3
"""Static trust and public-registry audit for the Green Frame Lean repository."""
from __future__ import annotations

import json
import re
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN_FILES = sorted(
    path
    for path in ROOT.rglob("*.lean")
    if ".lake" not in path.parts and "build" not in path.parts
)
FORBIDDEN = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "custom axiom": re.compile(r"^\s*(?:private\s+)?axiom\s+", re.MULTILINE),
    "custom constant": re.compile(r"^\s*(?:private\s+)?constants?\s+", re.MULTILINE),
    "partial": re.compile(r"^\s*(?:private\s+)?partial\s+", re.MULTILINE),
    "unsafe": re.compile(r"^\s*(?:private\s+)?unsafe\s+", re.MULTILINE),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "Lean.ofReduceBool": re.compile(r"\bLean\.ofReduceBool\b"),
}


def fail(message: str) -> None:
    print(f"ERROR: {message}", file=sys.stderr)
    raise SystemExit(1)


def main() -> int:
    if not LEAN_FILES:
        fail("no Lean sources found")
    for path in LEAN_FILES:
        text = path.read_text(encoding="utf-8")
        for label, pattern in FORBIDDEN.items():
            if pattern.search(text):
                fail(f"{label} found in {path.relative_to(ROOT)}")
        if "\t" in text:
            fail(f"tab found in {path.relative_to(ROOT)}")
        for number, line in enumerate(text.splitlines(), start=1):
            if line.rstrip() != line:
                fail(f"trailing whitespace in {path.relative_to(ROOT)}:{number}")

    registry = json.loads((ROOT / "audit/theorem-registry.json").read_text())
    entries = registry["theorems"]
    declared_count = registry.get("count")
    if declared_count != len(entries):
        fail(f"registry count field {declared_count} != {len(entries)} entries")
    ids = [entry["id"] for entry in entries]
    names = [entry["name"] for entry in entries]
    qualified = [entry["qualified"] for entry in entries]
    if len(ids) != len(set(ids)):
        fail("duplicate theorem registry IDs")
    if len(qualified) != len(set(qualified)):
        fail("duplicate qualified theorem names")

    declarations: list[str] = []
    for path in LEAN_FILES:
        if path.name == "Audit.lean":
            continue
        declarations.extend(
            re.findall(
                r"^theorem\s+(?:[A-Za-z0-9_]+\.)*([A-Za-z0-9_]+)",
                path.read_text(),
                re.MULTILINE,
            )
        )
    expected_ids = [f"GF-{i:03d}" for i in range(1, len(entries) + 1)]
    if ids != expected_ids:
        fail("theorem registry IDs are not sequential and ordered")
    actual = Counter(declarations)
    expected = Counter(names)
    if actual != expected:
        unregistered = sorted((actual - expected).elements())
        stale = sorted((expected - actual).elements())
        fail(f"registry mismatch; unregistered={unregistered}, stale={stale}")

    audit_text = (ROOT / "GreenFrame/Audit.lean").read_text()
    audit_names = re.findall(r"^#print axioms\s+([A-Za-z0-9_.]+)", audit_text, re.MULTILINE)
    if audit_names != qualified:
        fail("Audit.lean #print axioms order/content differs from theorem registry")

    public_root = (ROOT / "GreenFrame.lean").read_text()
    if "import GreenFrame.PublicAPI" not in public_root:
        fail("GreenFrame.lean does not import GreenFrame.PublicAPI")

    print(
        f"PASS: {len(LEAN_FILES)} project Lean files; {len(entries)} registered theorems; "
        "no placeholders or project axioms"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
