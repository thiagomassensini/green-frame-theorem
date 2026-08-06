# Green Frame Theorem

[![Lean 4.32.0](https://img.shields.io/badge/Lean-4.32.0-blue)](lean-toolchain)
[![Mathlib 4.32.0](https://img.shields.io/badge/Mathlib-4.32.0-blue)](lakefile.toml)

Lean 4 formal core for the **All-Bases Green Frame Theorem**: a carry-weighted arithmetic analysis with an admissible camera partition, a Pythagorean Green–return split, explicit frame inequalities, a Parseval interface, and exact Poisson reconstruction of coherent bulk data.

The preserved mathematical specification proves the full paper theorem on the all-bases carry atlas, including the canonical weights, the universal frame constants, the Parseval normalization, bounded Poisson reconstruction, finite sections, and the nontrivial bulk witness `(b,n)=(2,4)`. The Lean library isolates its reusable algebraic and operator-theoretic core into 41 named theorems. The exact paper-to-kernel boundary is recorded in [`audit/CLAIM_LEDGER.md`](audit/CLAIM_LEDGER.md); no numerical experiment is used as a premise.

## Reproduce

```bash
python3 scripts/materialize_source.py
lake build --wfail GreenFrame
lake env lean GreenFrame/Audit.lean
./scripts/run_audits.sh
```

The audit rejects `sorry`, `admit`, project `axiom` declarations, `unsafe` declarations, unregistered theorem changes, mutable GitHub Action refs, and non-allowlisted transitive axioms. The only permitted foundational axioms are:

```text
propext
Quot.sound
Classical.choice
```

## Formal chain

```text
finite admissible camera partition
  → normalized nonnegative weights
  → Green/residual mass conservation
  → Green stencil Bessel estimate
  → lower and upper frame ledger
  → injective full analysis
  → Parseval-normalized analysis interface
  → exact Poisson intertwining
  → coherent range as a graph
  → nontrivial bulk and return
  → uniform finite sections and closed limit transport
```

## Repository map

- `GreenFrame/Arithmetic`: admissible and normalized camera weights; canonical `(2,4)` witness.
- `GreenFrame/Analysis`: Pythagorean split, Green estimate, frame certificate, Parseval and Poisson layers.
- `GreenFrame/Finite`: cutoff-uniform inequalities and limit preservation.
- `GreenFrame/Audit.lean`: kernel axiom report for all 41 public theorems.
- [`docs/source`](docs/source): checksummed, byte-preserved paper specification and reconstruction instructions.
- `audit`: theorem registry, claim ledger, provenance, and generated evidence.

## Scope firewall

This repository does not assert a zero theorem, a special-function identity, a functional equation, an infinite self-adjoint height operator, or a Weyl family. Those are separate layers. The frame theorem is independent of primality and may be read over real or complex Hilbert spaces at the paper level; this Lean core uses real scalars for the reusable inequalities and linear-map interfaces.

## Citation and release

Citation metadata is in [`CITATION.cff`](CITATION.cff) and [`.zenodo.json`](.zenodo.json). Release `v1.0.0` is the first audited publication of the recovered formal core and source bundle.
