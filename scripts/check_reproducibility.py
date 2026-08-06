#!/usr/bin/env python3
"""Verify exact Lean, Mathlib, and GitHub Action pins."""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def die(message: str) -> None:
    print(f"ERROR: {message}", file=sys.stderr)
    raise SystemExit(1)


def main() -> int:
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    if toolchain != "leanprover/lean4:v4.32.0":
        die(f"unexpected toolchain: {toolchain}")
    lake = (ROOT / "lakefile.toml").read_text()
    if 'rev = "v4.32.0"' not in lake or 'name = "mathlib"' not in lake:
        die("Mathlib v4.32.0 is not pinned")
    workflow_text = "\n".join(
        path.read_text() for path in sorted((ROOT / ".github/workflows").glob("*.yml"))
    )
    action_refs = re.findall(r"uses:\s*[^@\s]+@([^\s#]+)", workflow_text)
    unpinned = [ref for ref in action_refs if not re.fullmatch(r"[0-9a-f]{40}", ref)]
    if unpinned:
        die(f"unpinned GitHub Action refs: {unpinned}")
    print("PASS: Lean v4.32.0, Mathlib v4.32.0, and immutable Action SHAs")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
