#!/usr/bin/env python3
"""Run the seven v2 gates, then manifest and package their evidence."""
from __future__ import annotations

import json
import shutil
import subprocess
import sys
from pathlib import Path

from audit_common import EVIDENCE, ROOT, write_json

GATES = [
    ("G1", "revision-identity", [sys.executable, "scripts/check_revision_identity.py"]),
    ("G2", "repository-trust", [sys.executable, "scripts/check_repository.py"]),
    ("G3", "research-integrity", [sys.executable, "scripts/check_research_inputs.py"]),
    ("G4", "reachable-imports", [sys.executable, "scripts/check_reachable_imports.py"]),
    ("G5", "lean-build-wfail", ["lake", "build", "--wfail", "GreenFrame"]),
    ("G6", "kernel-axioms", [sys.executable, "scripts/run_kernel_axiom_audit.py"]),
    ("G7", "evidence-closure", [sys.executable, "scripts/check_evidence_consistency.py"]),
]


def write_gate_state(results: list[dict[str, object]], final: bool) -> None:
    value = {
        "schema": "org.green-frame.audit-gates/v2",
        "count": len(results),
        "gates": results,
    }
    write_json(EVIDENCE / ("gates.json" if final else "gates.partial.json"), value)


def run_gate(identifier: str, slug: str, command: list[str]) -> int:
    log = EVIDENCE / f"{identifier.lower()}-{slug}.log"
    print(f"=== {identifier}: {slug} ===", flush=True)
    with log.open("w", encoding="utf-8") as output:
        process = subprocess.Popen(
            command,
            cwd=ROOT,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            bufsize=1,
        )
        assert process.stdout is not None
        for line in process.stdout:
            print(line, end="", flush=True)
            output.write(line)
        return process.wait()


def main() -> int:
    contract = json.loads((ROOT / "audit/release-contract.json").read_text())
    expected_ids = contract["audit"]["gate_ids"]
    if [identifier for identifier, _, _ in GATES] != expected_ids:
        print("ERROR: orchestrator gates differ from release contract", file=sys.stderr)
        return 1
    (ROOT / "audit/axioms.txt").unlink(missing_ok=True)
    dist = ROOT / "dist"
    if dist.exists():
        shutil.rmtree(dist)
    if EVIDENCE.exists():
        shutil.rmtree(EVIDENCE)
    EVIDENCE.mkdir(parents=True)

    results: list[dict[str, object]] = []
    for identifier, slug, command in GATES:
        if identifier == "G7":
            write_gate_state(results, final=False)
        status = run_gate(identifier, slug, command)
        results.append(
            {
                "id": identifier,
                "name": slug,
                "status": "PASS" if status == 0 else "FAIL",
                "exit_code": status,
                "command": command,
                "log": f"audit/evidence/{identifier.lower()}-{slug}.log",
            }
        )
        if status != 0:
            for pending_id, pending_slug, pending_command in GATES[len(results):]:
                results.append(
                    {
                        "id": pending_id,
                        "name": pending_slug,
                        "status": "NOT_RUN",
                        "exit_code": None,
                        "command": pending_command,
                        "log": None,
                    }
                )
            write_gate_state(results, final=True)
            print(f"ERROR: {identifier} failed", file=sys.stderr)
            return status

    write_gate_state(results, final=True)
    for command in (
        [sys.executable, "scripts/write_audit_manifest.py"],
        [sys.executable, "scripts/build_release_bundle.py"],
    ):
        subprocess.run(command, cwd=ROOT, check=True)
    print("PASS: 7/7 audit gates and release packaging completed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
