#!/usr/bin/env python3
"""Gate G4: prove every project library module is reachable from GreenFrame."""
from __future__ import annotations

import json
import re
from pathlib import Path

from audit_common import EVIDENCE, ROOT, die, sha256, write_json

IMPORT = re.compile(r"^\s*import\s+([A-Za-z0-9_.']+)\s*(?:--.*)?$", re.MULTILINE)


def module_name(path: Path) -> str:
    relative = path.relative_to(ROOT).with_suffix("")
    return ".".join(relative.parts)


def main() -> int:
    contract = json.loads((ROOT / "audit/release-contract.json").read_text())
    lean = contract["lean"]
    root_module = lean["root_module"]
    root_path = ROOT / lean["root_file"]
    excluded = set(lean["excluded_library_modules"])

    candidates = [root_path, *sorted((ROOT / "GreenFrame").rglob("*.lean"))]
    index: dict[str, Path] = {}
    for path in candidates:
        name = module_name(path)
        if name in index:
            die(f"duplicate project module name: {name}")
        index[name] = path
    if root_module not in index:
        die(f"root module is missing: {root_module}")
    unknown_exclusions = excluded - set(index)
    if unknown_exclusions:
        die(f"excluded modules do not exist: {sorted(unknown_exclusions)}")

    imports: dict[str, list[str]] = {}
    external: dict[str, list[str]] = {}
    for name, path in index.items():
        imported = IMPORT.findall(path.read_text(encoding="utf-8"))
        missing_project = sorted(
            target for target in imported
            if target.startswith("GreenFrame.") and target not in index
        )
        if missing_project:
            die(f"{name} imports missing project modules: {missing_project}")
        imports[name] = [target for target in imported if target in index]
        external[name] = [target for target in imported if target not in index]

    visiting: set[str] = set()
    visited: set[str] = set()
    order: list[str] = []

    def visit(name: str) -> None:
        if name in visiting:
            die(f"project import cycle reaches {name}")
        if name in visited:
            return
        visiting.add(name)
        for target in imports[name]:
            if target not in excluded:
                visit(target)
        visiting.remove(name)
        visited.add(name)
        order.append(name)

    visit(root_module)
    library_modules = set(index) - excluded
    unreachable = sorted(library_modules - visited)
    if unreachable:
        die(f"library modules unreachable from {root_module}: {unreachable}")
    audit_module = module_name(ROOT / lean["audit_file"])
    if imports.get(audit_module) != [root_module] or external.get(audit_module) != []:
        die(f"audit harness {audit_module} must import only {root_module}")

    modules = [
        {
            "module": name,
            "path": index[name].relative_to(ROOT).as_posix(),
            "sha256": sha256(index[name]),
            "project_imports": imports[name],
            "external_imports": external[name],
        }
        for name in sorted(visited)
    ]
    edges = sorted(
        (
            {"from": source, "to": target}
            for source in visited
            for target in imports[source]
            if target in visited
        ),
        key=lambda edge: (edge["from"], edge["to"]),
    )
    result = {
        "schema": "org.green-frame.reachable-import-graph/v2",
        "root": root_module,
        "reachable_module_count": len(visited),
        "reachable_modules": modules,
        "project_edges": edges,
        "topological_dependencies_first": order,
        "excluded_harness_modules": sorted(excluded),
        "unreachable_modules": unreachable,
    }
    write_json(EVIDENCE / "reachable-import-graph.json", result)
    print(
        f"PASS G4: {len(visited)}/{len(library_modules)} library modules reachable; "
        f"project import edges={len(edges)}; unreachable=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
