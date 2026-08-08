#!/usr/bin/env python3
"""Build deterministic source and run-bound audit archives plus checksums."""
from __future__ import annotations

import gzip
import json
import shutil
import subprocess
import tarfile
import tempfile
from pathlib import Path

from audit_common import EVIDENCE, ROOT, checked_output, die, sha256


def gzip_without_timestamp(source: Path, destination: Path) -> None:
    with source.open("rb") as raw, destination.open("wb") as target:
        with gzip.GzipFile(filename="", mode="wb", fileobj=target, mtime=0) as zipped:
            shutil.copyfileobj(raw, zipped)


def add_file(archive: tarfile.TarFile, path: Path, arcname: str) -> None:
    info = archive.gettarinfo(str(path), arcname=arcname)
    info.uid = 0
    info.gid = 0
    info.uname = "root"
    info.gname = "root"
    info.mtime = 0
    info.mode = 0o644
    with path.open("rb") as source:
        archive.addfile(info, source)


def main() -> int:
    contract = json.loads((ROOT / "audit/release-contract.json").read_text())
    version = contract["release"]["version"]
    prefix = f"green-frame-theorem-v{version}"
    dist = ROOT / "dist"
    if dist.exists():
        shutil.rmtree(dist)
    dist.mkdir()

    manifest_path = EVIDENCE / "audit-manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    commit = checked_output("git", "rev-parse", "HEAD")
    tree = checked_output("git", "rev-parse", "HEAD^{tree}")
    dirty = checked_output("git", "status", "--porcelain", "--untracked-files=all")
    if dirty:
        die("checkout changed or gained nonignored files before packaging")
    if (manifest["git"]["commit"], manifest["git"]["tree"]) != (commit, tree):
        die("audit manifest Git identity differs from the packaging checkout")
    if manifest["release"]["version"] != version:
        die("audit manifest version differs from release contract")
    expected_gate_ids = contract["audit"]["gate_ids"]
    if (
        [gate.get("id") for gate in manifest.get("gates", [])]
        != expected_gate_ids
        or any(gate.get("status") != "PASS" for gate in manifest["gates"])
    ):
        die("cannot package an audit manifest with a non-PASS gate")

    source_tar = dist / f"{prefix}.tar.gz"
    with tempfile.TemporaryDirectory(prefix="green-frame-source-") as temporary:
        raw_tar = Path(temporary) / "source.tar"
        subprocess.run(
            [
                "git", "archive", "--format=tar", f"--prefix={prefix}/",
                f"--output={raw_tar}", manifest["git"]["commit"],
            ],
            cwd=ROOT,
            check=True,
        )
        gzip_without_timestamp(raw_tar, source_tar)

    audit_files = [
        *sorted(path for path in EVIDENCE.rglob("*") if path.is_file()),
        ROOT / "audit/axioms.txt",
        ROOT / "audit/AXIOM_POLICY.md",
        ROOT / "audit/CLAIM_LEDGER.md",
        ROOT / "audit/claim-ledger.json",
        ROOT / "audit/SOURCE_PROVENANCE.md",
        ROOT / "audit/THEOREM_REGISTRY.md",
        ROOT / "audit/theorem-registry.json",
        ROOT / "audit/axiom-allowlist.json",
        ROOT / "audit/release-contract.json",
        ROOT / "research/SOURCE_MANIFEST.md",
        ROOT / "research/source-manifest.json",
        ROOT / "lean-toolchain",
        ROOT / "lakefile.toml",
        ROOT / "lake-manifest.json",
    ]
    missing = [
        path.relative_to(ROOT).as_posix()
        for path in audit_files
        if not path.is_file() or path.is_symlink()
    ]
    if missing:
        die(f"audit bundle inputs missing, nonregular, or symlinked: {missing}")
    audit_bundle = dist / f"{prefix}-audit.tar.gz"
    with tempfile.TemporaryDirectory(prefix="green-frame-audit-") as temporary:
        raw_tar = Path(temporary) / "audit.tar"
        with tarfile.open(raw_tar, mode="w", format=tarfile.PAX_FORMAT) as archive:
            for path in sorted(set(audit_files)):
                relative = path.relative_to(ROOT).as_posix()
                add_file(archive, path, f"{prefix}-audit/{relative}")
        gzip_without_timestamp(raw_tar, audit_bundle)

    primary = ROOT / contract["research"]["directory"] / contract["research"]["primary"]
    if Path(contract["research"]["primary"]).name != contract["research"]["primary"]:
        die("primary research asset must be one plain filename")
    paper_asset = dist / contract["research"]["primary"]
    shutil.copyfile(primary, paper_asset)
    shutil.copyfile(manifest_path, dist / "audit-manifest.json")
    shutil.copyfile(EVIDENCE / "axiom-report.json", dist / "axiom-report.json")

    checksum_targets = sorted(
        [source_tar, audit_bundle, paper_asset, dist / "audit-manifest.json", dist / "axiom-report.json"],
        key=lambda path: path.name,
    )
    checksum_file = dist / "SHA256SUMS.txt"
    checksum_file.write_text(
        "".join(f"{sha256(path)}  {path.name}\n" for path in checksum_targets),
        encoding="utf-8",
    )
    for line in checksum_file.read_text(encoding="utf-8").splitlines():
        expected, name = line.split("  ", maxsplit=1)
        if sha256(dist / name) != expected:
            die(f"post-package checksum verification failed: {name}")

    expected_assets = {
        f"{prefix}.tar.gz",
        f"{prefix}-audit.tar.gz",
        contract["research"]["primary"],
        "audit-manifest.json",
        "axiom-report.json",
        "SHA256SUMS.txt",
    }
    dist_entries = list(dist.iterdir())
    if any(not path.is_file() or path.is_symlink() for path in dist_entries):
        die("release dist directory contains a nonregular entry or symlink")
    actual_assets = {path.name for path in dist_entries}
    if actual_assets != expected_assets:
        die(f"release asset set mismatch: {sorted(actual_assets)}")
    print(
        f"PASS: built {len(expected_assets)} release assets for "
        f"{manifest['git']['commit']} with checksums"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
