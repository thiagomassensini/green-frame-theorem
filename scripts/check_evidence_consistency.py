#!/usr/bin/env python3
"""Gate G7: cross-check every independently produced audit identity/count."""
from __future__ import annotations

import json

from audit_common import EVIDENCE, ROOT, checked_output, die, sha256, write_json


def read(name: str) -> dict:
    path = EVIDENCE / name
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        die(f"missing or invalid G7 input {name}: {error}")


def main() -> int:
    contract = json.loads((ROOT / "audit/release-contract.json").read_text())
    registry_path = ROOT / contract["audit"]["theorem_registry"]
    registry = json.loads(registry_path.read_text())
    claim_path = ROOT / contract["audit"]["claim_ledger"]
    claim_ledger = json.loads(claim_path.read_text())
    claim_contract = contract["claims"]
    revision = read("revision-identity.json")
    inventory = read("repository-inventory.json")
    sources = read("source-provenance.json")
    graph = read("reachable-import-graph.json")
    axioms = read("axiom-report.json")
    partial = read("gates.partial.json")

    first_six = contract["audit"]["gate_ids"][:6]
    if partial.get("count") != len(first_six):
        die(f"G7 received wrong preceding gate count: {partial.get('count')}")
    observed_first_six = [gate["id"] for gate in partial.get("gates", [])]
    if observed_first_six != first_six:
        die(f"G7 received wrong preceding gates: {observed_first_six}")
    if any(gate.get("status") != "PASS" for gate in partial["gates"]):
        die("G7 cannot close evidence while an earlier gate is not PASS")

    commit = checked_output("git", "rev-parse", "HEAD")
    tree = checked_output("git", "rev-parse", "HEAD^{tree}")
    dirty = checked_output("git", "status", "--porcelain", "--untracked-files=all")
    if dirty:
        die("checkout changed or gained nonignored files while the gates were running")
    if (revision["commit"], revision["tree"]) != (commit, tree):
        die("revision identity no longer matches the checked-out Git object")

    theorem_count = len(registry["theorems"])
    if registry.get("count") != theorem_count:
        die("G7 theorem registry count is stale")
    if theorem_count != claim_contract["registry_count"]:
        die("G7 theorem registry count differs from the release contract")
    if axioms.get("count") != len(axioms.get("reports", [])):
        die("G7 axiom report count is stale")
    count_values = {
        "registry": registry.get("count"),
        "repository": inventory["counts"]["public_theorems"],
        "axiom_queries": inventory["counts"]["axiom_queries"],
        "axiom_reports": axioms["count"],
    }
    if set(count_values.values()) != {theorem_count}:
        die(f"public theorem counts disagree: {count_values}")
    registry_identities = [
        (entry["id"], entry["name"], entry["qualified"])
        for entry in registry["theorems"]
    ]
    axiom_identities = [
        (report["id"], report["name"], report["qualified"])
        for report in axioms["reports"]
    ]
    if axiom_identities != registry_identities:
        die("G7 exact axiom IDs/names differ from theorem registry")
    if inventory["theorem_registry_sha256"] != sha256(registry_path):
        die("repository inventory theorem-registry digest is stale")
    if inventory["claim_ledger_sha256"] != sha256(claim_path):
        die("repository inventory claim-ledger digest is stale")
    if sha256(claim_path) != claim_contract["ledger_sha256"]:
        die("G7 claim ledger bytes differ from the release contract digest")
    if claim_ledger.get("schema") != claim_contract["ledger_schema"]:
        die("G7 claim ledger schema differs from the release contract")
    if claim_ledger.get("registry_count") != theorem_count:
        die("G7 claim ledger registry_count differs from the theorem registry")
    if claim_ledger.get("coefficient_split") != claim_contract["coefficient_split"]:
        die("G7 claim ledger coefficient split differs from the release contract")
    if (
        claim_ledger.get("canonical_bulk_witness")
        != claim_contract["canonical_bulk_witness"]
    ):
        die("G7 claim ledger bulk witness differs from the release contract")
    if claim_ledger.get("count") != len(claim_ledger.get("claims", [])):
        die("G7 claim ledger count is stale")
    if inventory["counts"]["paper_claims"] != claim_ledger["count"]:
        die("G7 claim count differs from the repository inventory")
    observed_claim_statuses: dict[str, int] = {}
    for claim in claim_ledger["claims"]:
        status = claim["status"]
        observed_claim_statuses[status] = observed_claim_statuses.get(status, 0) + 1
    if inventory["claim_status_counts"] != dict(sorted(observed_claim_statuses.items())):
        die("G7 claim status counts differ from the repository inventory")
    if observed_claim_statuses != claim_contract["status_counts"]:
        die("G7 claim status counts differ from the exact release contract")
    if claim_ledger.get("status_counts") != claim_contract["status_counts"]:
        die("G7 claim ledger status_counts summary differs from the release contract")
    expected_claim_counts = contract["claims"]["expected_counts"]
    observed_claim_counts = {
        "paper": inventory["counts"]["paper_claims"],
        "kernel": inventory["counts"]["kernel_claims"],
        "conditional": inventory["counts"]["conditional_claims"],
        "open": inventory["counts"]["open_claims"],
        "future": inventory["counts"]["future_claims"],
    }
    if observed_claim_counts != expected_claim_counts:
        die(
            "G7 claim counts differ from the contracted release boundary: "
            f"expected={expected_claim_counts}; observed={observed_claim_counts}"
        )
    if axioms["axiom_log_sha256"] != sha256(ROOT / "audit/axioms.txt"):
        die("canonical axiom report does not match the preserved raw Lean log")

    source_manifest = json.loads(
        (ROOT / contract["research"]["manifest"]).read_text(encoding="utf-8")
    )
    source_counts = {
        "contract": contract["research"]["expected_count"],
        "manifest": source_manifest["count"],
        "verified": sources["count"],
    }
    if len(set(source_counts.values())) != 1:
        die(f"research input counts disagree: {source_counts}")
    if sources["count"] != len(sources.get("files", [])):
        die("source provenance count differs from its file records")
    if sources.get("files") != source_manifest.get("files"):
        die("source provenance identities/digests differ from the versioned manifest")
    primary_name = contract["research"]["primary"]
    primary_records = [
        entry for entry in source_manifest["files"] if entry["name"] == primary_name
    ]
    if len(primary_records) != 1 or sources.get("primary", {}).get("sha256") != primary_records[0]["sha256"]:
        die("primary paper identity/digest differs across source evidence")
    if sources["manifest_sha256"] != sha256(ROOT / contract["research"]["manifest"]):
        die("source provenance report does not match its versioned manifest")

    graph_paths = {
        module["path"] for module in graph["reachable_modules"]
    }
    if graph["reachable_module_count"] != len(graph["reachable_modules"]):
        die("reachable import graph count differs from its module records")
    excluded_paths = {
        module.replace(".", "/") + ".lean"
        for module in graph["excluded_harness_modules"]
    }
    inventory_paths = {entry["path"] for entry in inventory["lean_files"]}
    if graph_paths | excluded_paths != inventory_paths:
        die(
            "reachable graph plus explicit audit harnesses does not equal the "
            "complete Lean inventory"
        )
    if graph["unreachable_modules"]:
        die(f"unreachable modules remain: {graph['unreachable_modules']}")
    inventory_hashes = {
        entry["path"]: entry["sha256"] for entry in inventory["lean_files"]
    }
    graph_hashes = {
        entry["path"]: entry["sha256"] for entry in graph["reachable_modules"]
    }
    for path, digest in graph_hashes.items():
        if inventory_hashes.get(path) != digest:
            die(f"Lean source digest disagreement for {path}")

    allowlist = json.loads(
        (ROOT / contract["audit"]["axiom_allowlist"]).read_text(encoding="utf-8")
    )["allowed"]
    if axioms["allowed_axioms"] != allowlist:
        die("axiom report allowlist differs from the versioned policy")
    if set(axioms.get("used_axioms", [])) - set(allowlist):
        die("axiom report records an axiom outside the versioned allowlist")

    result = {
        "schema": "org.green-frame.evidence-consistency/v2",
        "commit": commit,
        "tree": tree,
        "counts": {
            "gates": len(contract["audit"]["gate_ids"]),
            "lean_files": inventory["counts"]["lean_files"],
            "reachable_modules": graph["reachable_module_count"],
            "public_theorems": theorem_count,
            "axiom_reports": axioms["count"],
            "documentation_files": inventory["counts"]["documentation_files"],
            "research_inputs": sources["count"],
            "paper_claims": inventory["counts"]["paper_claims"],
            "kernel_claims": inventory["counts"]["kernel_claims"],
            "conditional_claims": inventory["counts"]["conditional_claims"],
            "open_claims": inventory["counts"]["open_claims"],
            "future_claims": inventory["counts"]["future_claims"],
        },
        "used_axioms": axioms["used_axioms"],
        "allowed_axioms": allowlist,
        "identity_sha256": {
            "theorem_registry": sha256(registry_path),
            "claim_ledger": sha256(claim_path),
            "source_manifest": sha256(ROOT / contract["research"]["manifest"]),
            "axiom_log": axioms["axiom_log_sha256"],
        },
    }
    write_json(EVIDENCE / "evidence-consistency.json", result)
    counts = result["counts"]
    print(
        "PASS G7: evidence closed; "
        f"gates={counts['gates']}; modules={counts['reachable_modules']}; "
        f"theorems={counts['public_theorems']}; axioms={counts['axiom_reports']}; "
        f"docs={counts['documentation_files']}; inputs={counts['research_inputs']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
