#!/usr/bin/env python3
"""Validate the exact identity and allowlisted axioms of every public theorem."""
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

from audit_common import EVIDENCE, ROOT, die, sha256, write_json

REPORT = re.compile(
    r"^'(?P<name>[^'\n]+)'\s+(?:"
    r"(?P<none>does not depend on any axioms)"
    r"|depends on axioms:\s*\[(?P<axioms>.*?)\])\s*$",
    re.MULTILINE | re.DOTALL,
)
AXIOM_NAME = re.compile(r"[A-Za-z0-9_.']+")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("axiom_log", type=Path)
    parser.add_argument(
        "--output", type=Path, default=EVIDENCE / "axiom-report.json"
    )
    args = parser.parse_args()

    registry = json.loads((ROOT / "audit/theorem-registry.json").read_text())
    entries = registry["theorems"]
    allowlist_path = ROOT / "audit/axiom-allowlist.json"
    allowlist = json.loads(allowlist_path.read_text())
    allowed_names = allowlist.get("allowed", [])
    if allowed_names != sorted(set(allowed_names)):
        die("axiom allowlist must be unique and sorted")
    allowed = set(allowed_names)

    text = args.axiom_log.read_text(encoding="utf-8")
    parsed: list[tuple[str, list[str]]] = []
    for match in REPORT.finditer(text):
        raw = match.group("axioms")
        axioms = [] if raw is None else AXIOM_NAME.findall(raw)
        parsed.append((match.group("name"), axioms))

    expected_names = [entry["qualified"] for entry in entries]
    observed_names = [name for name, _ in parsed]
    if observed_names != expected_names:
        missing = sorted(set(expected_names) - set(observed_names))
        unexpected = sorted(set(observed_names) - set(expected_names))
        duplicates = sorted(
            name for name in set(observed_names) if observed_names.count(name) > 1
        )
        first_difference = next(
            (
                index
                for index, pair in enumerate(zip(expected_names, observed_names))
                if pair[0] != pair[1]
            ),
            min(len(expected_names), len(observed_names)),
        )
        die(
            "axiom report identities/order differ from registry; "
            f"first_difference={first_difference}; missing={missing}; "
            f"unexpected={unexpected}; duplicates={duplicates}"
        )

    reports: list[dict[str, object]] = []
    used: set[str] = set()
    for entry, (qualified, axioms) in zip(entries, parsed, strict=True):
        forbidden = sorted(set(axioms) - allowed)
        if forbidden:
            die(f"forbidden axioms for {qualified}: {forbidden}")
        used.update(axioms)
        reports.append(
            {
                "id": entry["id"],
                "name": entry["name"],
                "qualified": qualified,
                "axioms": sorted(set(axioms)),
            }
        )

    result = {
        "schema": "org.green-frame.kernel-axiom-report/v2",
        "count": len(reports),
        "allowed_axioms": allowed_names,
        "used_axioms": sorted(used),
        "axiom_log_sha256": sha256(args.axiom_log),
        "reports": reports,
    }
    write_json(args.output, result)
    print(
        f"PASS G6: {len(reports)}/{len(entries)} named axiom reports; "
        f"used={sorted(used)}; allowlist={allowed_names}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
