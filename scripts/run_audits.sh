#!/usr/bin/env bash
set -euo pipefail
python3 scripts/check_reproducibility.py
python3 scripts/check_release_metadata.py
python3 scripts/check_repository.py
python3 scripts/check_source_provenance.py
lake build --wfail GreenFrame
lake env lean GreenFrame/Audit.lean 2>&1 | tee audit/axioms.txt
python3 scripts/check_axiom_output.py audit/axioms.txt
