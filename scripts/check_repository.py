#!/usr/bin/env python3
"""Static trust audit for the Green Frame Lean repository."""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN_FILES = sorted(ROOT.rglob("*.lean"))
FORBIDDEN = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "custom axiom": re.compile(r"^\s*axiom\s+", re.MULTILINE),
    "unsafe": re.compile(r"^\s*unsafe\s+", re.MULTILINE),
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
    expected = {entry["name"] for entry in registry["theorems"]}
    declarations: list[str] = []
    for path in LEAN_FILES:
        if path.name == "Audit.lean":
            continue
        declarations.extend(
            re.findall(r"^theorem\s+([A-Za-z0-9_]+)", path.read_text(), re.MULTILINE)
        )
    actual = set(declarations)
    if len(declarations) != 41:
        fail(f"expected 41 theorem declarations, found {len(declarations)}")
    if actual != expected:
        fail(f"registry mismatch; missing={sorted(actual-expected)}, stale={sorted(expected-actual)}")

    public_root = (ROOT / "GreenFrame.lean").read_text()
    if "import GreenFrame.PublicAPI" not in public_root:
        fail("GreenFrame.lean does not import GreenFrame.PublicAPI")

    print(f"PASS: {len(LEAN_FILES)} Lean files; 41 registered theorems; no placeholders or project axioms")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
