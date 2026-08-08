#!/usr/bin/env python3
"""Gate G2: static trust scan, registry closure, and documentation inventory."""
from __future__ import annotations

import json
import re
from collections import Counter
from pathlib import Path

from audit_common import EVIDENCE, ROOT, checked_output, die, sha256, write_json

FORBIDDEN = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "custom axiom": re.compile(
        r"^\s*(?:@\[[^\n]*\]\s*)*(?:private\s+)?axiom\s+", re.MULTILINE
    ),
    "custom constant": re.compile(
        r"^\s*(?:@\[[^\n]*\]\s*)*(?:private\s+)?constants?\s+", re.MULTILINE
    ),
    "partial": re.compile(
        r"^\s*(?:@\[[^\n]*\]\s*)*(?:private\s+)?partial\s+", re.MULTILINE
    ),
    "unsafe": re.compile(
        r"^\s*(?:@\[[^\n]*\]\s*)*(?:private\s+)?unsafe\s+", re.MULTILINE
    ),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "Lean.ofReduceBool": re.compile(r"\bLean\.ofReduceBool\b"),
}
PUBLIC_THEOREM = re.compile(
    r"^\s*(?:@\[[^\n]*\]\s*)*(?!private\s+)"
    r"(?:(?:noncomputable|protected|nonrec)\s+)*(?:theorem|lemma)\s+([A-Za-z0-9_.']+)",
    re.MULTILINE,
)
CLAIM_ROW = re.compile(
    r"^\|\s*`?(?P<id>ABGF-[A-Z]+-[0-9]{3})`?\s*\|(?P<body>[^\n]*)$",
    re.MULTILINE,
)
FINAL_CLAIM_STATUS = re.compile(
    r"\b(?:KERNEL_CHECKED|CONDITIONAL|OPEN|FUTURE_LAYER)\b"
)
THEOREM_LEDGER_ROW = re.compile(
    r"^\|\s*`?(?P<id>GF-[0-9]{3,})`?\s*\|\s*"
    r"`?(?P<qualified>[A-Za-z0-9_.']+)`?\s*\|",
    re.MULTILINE,
)
PLACEHOLDER = re.compile(r"\b(?:REPLACE(?:\s+ME)?|TODO|TBD)\b", re.IGNORECASE)
EDITORIAL_MARKERS = re.compile(
    r"(?:Lean v1\.0\.0 target|KERNEL_TARGET|PENDING_REMOTE_CI|"
    r"(?i:\beditorial draft\b)|(?:Do not publish|DO NOT PUBLISH)|"
    r"(?i:\bprospective release text\b|\bstaging materialization\b|"
    r"\bfinal-shaped\b|\bprojected GF-[0-9]+ closure\b)|"
    r"\bREPLACE(?:\s+ME|\s+WITH|_[A-Z0-9_]+)?\b|\bTODO\b|\bTBD\b)",
)


def tracked_markdown() -> list[Path]:
    names = checked_output("git", "ls-files", "*.md").splitlines()
    return [
        ROOT / name for name in names
        if not name.startswith("research/inputs/")
        and name != "docs/90_PAPER_SPECIFICATION.md"
    ]


def main() -> int:
    contract = json.loads((ROOT / "audit/release-contract.json").read_text())
    audit_file = ROOT / contract["lean"]["audit_file"]
    lean_files = sorted(
        path for path in ROOT.rglob("*.lean")
        if ".lake" not in path.parts and "build" not in path.parts
    )
    if not lean_files:
        die("no project Lean sources found")
    tracked_files = set(checked_output("git", "ls-files").splitlines())
    critical_tracked = {
        contract["lean"]["root_file"],
        contract["lean"]["audit_file"],
        "GreenFrame/PublicAPI.lean",
        "audit/release-contract.json",
        contract["audit"]["theorem_registry"],
        contract["audit"]["claim_ledger"],
        contract["audit"]["axiom_allowlist"],
        "audit/THEOREM_REGISTRY.md",
        "audit/CLAIM_LEDGER.md",
    }
    missing_critical = sorted(critical_tracked - tracked_files)
    if missing_critical:
        die(f"audit-critical repository files are not tracked: {missing_critical}")
    untracked_lean = [
        path.relative_to(ROOT).as_posix()
        for path in lean_files
        if path.relative_to(ROOT).as_posix() not in tracked_files
    ]
    if untracked_lean:
        die(f"project Lean sources are not tracked by Git: {untracked_lean}")

    declarations: list[str] = []
    scanned: list[dict[str, str]] = []
    for path in lean_files:
        if path.is_symlink() or not path.is_file():
            die(f"project Lean source is not a regular file: {path.relative_to(ROOT)}")
        text = path.read_text(encoding="utf-8")
        for label, pattern in FORBIDDEN.items():
            if pattern.search(text):
                die(f"{label} found in {path.relative_to(ROOT)}")
        if "\t" in text:
            die(f"tab found in {path.relative_to(ROOT)}")
        for number, line in enumerate(text.splitlines(), start=1):
            if line.rstrip() != line:
                die(f"trailing whitespace in {path.relative_to(ROOT)}:{number}")
        if path != audit_file:
            declarations.extend(
                name.rsplit(".", 1)[-1] for name in PUBLIC_THEOREM.findall(text)
            )
        scanned.append(
            {"path": path.relative_to(ROOT).as_posix(), "sha256": sha256(path)}
        )

    registry_path = ROOT / "audit/theorem-registry.json"
    registry = json.loads(registry_path.read_text(encoding="utf-8"))
    entries = registry.get("theorems", [])
    if registry.get("count") != len(entries):
        die("theorem registry count field differs from its entries")
    ids = [entry["id"] for entry in entries]
    names = [entry["name"] for entry in entries]
    qualified = [entry["qualified"] for entry in entries]
    if ids != [f"GF-{index:03d}" for index in range(1, len(entries) + 1)]:
        die("theorem registry IDs are not sequential and ordered")
    if len(qualified) != len(set(qualified)):
        die("duplicate qualified theorem name in registry")
    root_prefix = contract["lean"]["root_module"] + "."
    for entry in entries:
        if entry["qualified"].rsplit(".", maxsplit=1)[-1] != entry["name"]:
            die(f"qualified registry name has wrong basename: {entry}")
        if not entry["qualified"].startswith(root_prefix):
            die(f"registry theorem is outside the public root namespace: {entry}")
    actual = Counter(declarations)
    expected = Counter(names)
    if actual != expected:
        die(
            "theorem registry mismatch; "
            f"unregistered={sorted((actual - expected).elements())}; "
            f"stale={sorted((expected - actual).elements())}"
        )

    claim_path = ROOT / contract["audit"]["claim_ledger"]
    claim_ledger = json.loads(claim_path.read_text(encoding="utf-8"))
    claims = claim_ledger.get("claims", [])
    claim_contract = contract["claims"]
    expected_claim_ids = contract["claims"]["expected_ids"]
    claim_ids = [claim.get("id") for claim in claims]
    if claim_ledger.get("schema") != claim_contract["ledger_schema"]:
        die("claim ledger schema differs from the release contract")
    if sha256(claim_path) != claim_contract["ledger_sha256"]:
        die("claim ledger bytes differ from the release contract digest")
    if (
        claim_ledger.get("registry_count") != claim_contract["registry_count"]
        or len(entries) != claim_contract["registry_count"]
    ):
        die("claim ledger/registry theorem count differs from the release contract")
    if claim_ledger.get("coefficient_split") != claim_contract["coefficient_split"]:
        die("claim ledger coefficient split differs from the release contract")
    if (
        claim_ledger.get("canonical_bulk_witness")
        != claim_contract["canonical_bulk_witness"]
    ):
        die("claim ledger canonical bulk witness differs from the release contract")
    if claim_ledger.get("release") != contract["release"]["version"]:
        die("claim ledger release differs from the release contract")
    if claim_ledger.get("count") != len(claims) or claim_ids != expected_claim_ids:
        die("claim ledger count/order differs from the 23-claim release contract")
    if len(claim_ids) != len(set(claim_ids)):
        die("duplicate paper claim ID in claim ledger")

    registry_ids = {entry["id"] for entry in entries}
    kernel_ids = set(contract["claims"]["kernel_required"])
    conditional_ids = set(contract["claims"]["conditional_required"])
    open_ids = set(contract["claims"]["open_required"])
    future_ids = set(contract["claims"]["future_required"])
    claim_categories = (kernel_ids, conditional_ids, open_ids, future_ids)
    if set().union(*claim_categories) != set(expected_claim_ids):
        die("claim contract categories do not partition the expected claim IDs")
    if sum(len(category) for category in claim_categories) != len(expected_claim_ids):
        die("claim contract categories overlap")
    expected_claim_counts = contract["claims"]["expected_counts"]
    observed_category_counts = {
        "paper": len(expected_claim_ids),
        "kernel": len(kernel_ids),
        "conditional": len(conditional_ids),
        "open": len(open_ids),
        "future": len(future_ids),
    }
    if expected_claim_counts != observed_category_counts:
        die(
            "claim contract category counts differ from the release boundary: "
            f"expected={expected_claim_counts}; observed={observed_category_counts}"
        )
    kernel_statuses = set(contract["claims"]["kernel_statuses"])
    status_counts: Counter[str] = Counter()
    for claim in claims:
        identifier = claim["id"]
        status = claim.get("status")
        evidence = claim.get("theorem_ids", [])
        if not isinstance(claim.get("claim"), str) or not claim["claim"].strip():
            die(f"claim ledger entry lacks a nonempty claim statement: {identifier}")
        if PLACEHOLDER.search(claim["claim"]):
            die(f"claim ledger entry retains a placeholder: {identifier}")
        if (
            not isinstance(evidence, list)
            or any(not isinstance(item, str) for item in evidence)
            or evidence != list(dict.fromkeys(evidence))
        ):
            die(f"claim theorem IDs must be a unique ordered list: {identifier}")
        if any(not re.fullmatch(r"GF-[0-9]{3,}", item) for item in evidence):
            die(f"claim theorem ID has invalid syntax: {identifier}")
        unknown_evidence = sorted(set(evidence) - registry_ids)
        if unknown_evidence:
            die(f"claim {identifier} cites unknown theorem IDs: {unknown_evidence}")
        if identifier in kernel_ids:
            if status not in kernel_statuses or not evidence:
                die(f"kernel-required claim is not backed by named theorems: {identifier}")
        elif identifier in conditional_ids:
            if status != "CONDITIONAL" or not evidence:
                die(f"conditional claim lacks a named implication theorem: {identifier}")
            if not isinstance(claim.get("conditions"), str) or not claim["conditions"].strip():
                die(f"conditional claim does not state its unproved hypotheses: {identifier}")
            if PLACEHOLDER.search(claim["conditions"]):
                die(f"conditional claim retains placeholder hypotheses: {identifier}")
        elif identifier in open_ids:
            if status != "OPEN" or evidence:
                die(f"open claim must remain OPEN without theorem mapping: {identifier}")
            if not isinstance(claim.get("reason"), str) or not claim["reason"].strip():
                die(f"open claim does not state why it remains open: {identifier}")
            if PLACEHOLDER.search(claim["reason"]):
                die(f"open claim retains a placeholder reason: {identifier}")
        elif identifier in future_ids:
            if status != "FUTURE_LAYER" or evidence:
                die(
                    "future claim must remain FUTURE_LAYER without theorem mapping: "
                    f"{identifier}"
                )
        else:
            die(f"claim is outside the contracted status partition: {identifier}")
        status_counts[status] += 1

    expected_status_counts = claim_contract["status_counts"]
    observed_status_counts = dict(status_counts)
    if observed_status_counts != expected_status_counts:
        die(
            "claim status counts differ from the exact release contract: "
            f"expected={expected_status_counts}; observed={observed_status_counts}"
        )
    if claim_ledger.get("status_counts") != expected_status_counts:
        die("claim ledger status_counts summary differs from the release contract")

    claim_markdown = (ROOT / "audit/CLAIM_LEDGER.md").read_text(encoding="utf-8")
    markdown_rows = list(CLAIM_ROW.finditer(claim_markdown))
    markdown_claim_ids = [match.group("id") for match in markdown_rows]
    if markdown_claim_ids != expected_claim_ids:
        die("CLAIM_LEDGER.md table does not list the exact 23 claims in contract order")
    for claim, row in zip(claims, markdown_rows, strict=True):
        body = row.group("body")
        if claim["claim"] not in body:
            die(f"CLAIM_LEDGER.md claim text differs for {claim['id']}")
        markdown_statuses = FINAL_CLAIM_STATUS.findall(body)
        if markdown_statuses != [claim["status"]]:
            die(
                f"CLAIM_LEDGER.md status differs for {claim['id']}: "
                f"{markdown_statuses}"
            )
        markdown_theorems = re.findall(r"GF-[0-9]{3,}", body)
        if markdown_theorems != claim["theorem_ids"]:
            die(
                f"CLAIM_LEDGER.md theorem mapping differs for {claim['id']}: "
                f"{markdown_theorems}"
            )
        if claim["status"] == "CONDITIONAL" and claim["conditions"] not in body:
            die(f"CLAIM_LEDGER.md omits exact conditions for {claim['id']}")
        if claim["status"] == "OPEN" and claim["reason"] not in body:
            die(f"CLAIM_LEDGER.md omits the exact open reason for {claim['id']}")

    theorem_markdown_path = ROOT / "audit/THEOREM_REGISTRY.md"
    theorem_markdown = theorem_markdown_path.read_text(encoding="utf-8")
    headline_counts = re.findall(
        r"contains exactly \*\*(?P<count>[0-9]+)\*\* named Lean theorems",
        theorem_markdown,
    )
    if headline_counts != [str(len(entries))]:
        die("THEOREM_REGISTRY.md headline count differs from the JSON registry")
    theorem_rows = list(THEOREM_LEDGER_ROW.finditer(theorem_markdown))
    markdown_registry = [
        (row.group("id"), row.group("qualified")) for row in theorem_rows
    ]
    expected_markdown_registry = [
        (entry["id"], entry["qualified"]) for entry in entries
    ]
    if markdown_registry != expected_markdown_registry:
        die("THEOREM_REGISTRY.md identities/order differ from the JSON registry")

    audit_names = re.findall(
        r"^#print axioms\s+([A-Za-z0-9_.']+)\s*$",
        audit_file.read_text(encoding="utf-8"),
        re.MULTILINE,
    )
    if audit_names != qualified:
        die("Audit.lean #print axioms order/content differs from registry")
    if "import GreenFrame.PublicAPI" not in (ROOT / "GreenFrame.lean").read_text():
        die("GreenFrame.lean does not import GreenFrame.PublicAPI")
    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    stale_readme_phrases = (
        "core into 41 named theorems",
        "kernel axiom report for all 41 public theorems",
    )
    if any(phrase in readme for phrase in stale_readme_phrases):
        die("README.md retains the historical fixed 41-theorem inventory")

    docs = tracked_markdown()
    doc_names = {path.relative_to(ROOT).as_posix() for path in docs}
    missing = sorted(set(contract["documentation"]["required"]) - doc_names)
    if missing:
        die(f"required documentation missing from Git: {missing}")
    documentation: list[dict[str, str]] = []
    for path in docs:
        if path.is_symlink() or not path.is_file():
            die(f"documentation is not a regular file: {path.relative_to(ROOT)}")
        raw = path.read_bytes()
        if not raw:
            die(f"empty documentation file: {path.relative_to(ROOT)}")
        try:
            text = raw.decode("utf-8")
        except UnicodeDecodeError as error:
            die(f"non-UTF-8 documentation {path.relative_to(ROOT)}: {error}")
        if re.search(r"^(?:<<<<<<<|=======|>>>>>>>)", text, re.MULTILINE):
            die(f"unresolved merge marker in {path.relative_to(ROOT)}")
        marker = EDITORIAL_MARKERS.search(text)
        if marker:
            die(
                f"pre-release editorial marker {marker.group(0)!r} in "
                f"{path.relative_to(ROOT)}"
            )
        documentation.append(
            {"path": path.relative_to(ROOT).as_posix(), "sha256": sha256(path)}
        )

    result = {
        "schema": "org.green-frame.repository-inventory/v2",
        "counts": {
            "lean_files": len(lean_files),
            "public_theorems": len(entries),
            "axiom_queries": len(audit_names),
            "documentation_files": len(docs),
            "paper_claims": len(claims),
            "kernel_claims": sum(status_counts[name] for name in kernel_statuses),
            "conditional_claims": status_counts["CONDITIONAL"],
            "open_claims": status_counts["OPEN"],
            "future_claims": status_counts["FUTURE_LAYER"],
        },
        "lean_files": scanned,
        "documentation": documentation,
        "theorem_registry_sha256": sha256(registry_path),
        "claim_ledger_sha256": sha256(claim_path),
        "claim_status_counts": dict(sorted(status_counts.items())),
        "audit_file_sha256": sha256(audit_file),
    }
    write_json(EVIDENCE / "repository-inventory.json", result)
    counts = result["counts"]
    print(
        "PASS G2: "
        f"Lean files={counts['lean_files']}; public theorems={counts['public_theorems']}; "
        f"axiom queries={counts['axiom_queries']}; docs={counts['documentation_files']}; "
        f"claims={counts['kernel_claims']} kernel + "
        f"{counts['conditional_claims']} conditional + "
        f"{counts['open_claims']} open + {counts['future_claims']} future; "
        "zero trust escapes"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
