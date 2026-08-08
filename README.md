# Green Frame Theorem

> v2.0.0 evidence is bound to the exact commit, tree and successful seven-gate
> runs recorded in the release audit manifest. Earlier green checkpoints are
> not release evidence.

[![Lean 4.32.0](https://img.shields.io/badge/Lean-4.32.0-blue)](lean-toolchain)
[![Mathlib pinned](https://img.shields.io/badge/Mathlib-pinned-blue)](lake-manifest.json)

This repository formalizes a concrete all-bases carry construction in Lean 4.
Its vertical layer starts from positional depth and canonical log-depth
weights, builds Green and residual coordinates on complex `l2`, and proves
bounded analysis operators with explicit constants. Separate modules construct
the elementary horizontal atlas, the normalized-tower TFVD chart, canonical
Parseval normalization, static Poisson reconstruction and finite sections.

The authoritative release scope is the conjunction of:

- the public import closure rooted at `GreenFrame.lean`;
- `audit/theorem-registry.json`, `audit/THEOREM_REGISTRY.md`, and
  `GreenFrame/Audit.lean` in identical order;
- the ordered named kernel-axiom report;
- `audit/claim-ledger.json` and `audit/CLAIM_LEDGER.md`, which map every paper
  claim to exact Lean evidence or to an explicit boundary status.

## v2 claim surface

The final release contract is 23 = 20 + 1 + 1 + 1:

- 20 exact concrete claims target `KERNEL_CHECKED`;
- normalized finite-section convergence is `CONDITIONAL` on one named
  common-space inverse-square-root CFC limit;
- finite Poisson convergence is `OPEN` and has no theorem evidence;
- the Weyl/Schur layer is `FUTURE_LAYER`.

No claim receives a kernel status until all cited qualified declarations and
their final GF IDs pass the seven gates at the exact release SHA.

## Concrete vertical and horizontal content

For every positive integer coordinate, the canonical cameras range over all
integer bases `b>=2`, including composite bases. The formalization represents
finite active support, the all-base partition identity, the endpoint-charge
depth-one share, the conservative Green/return mass split, residual mass in
`[1/2,1]`, the complex three-level Green stencil and its normalized-tower TFVD
chart.

The elementary atlas is a distinct seed-plus-weighted-coordinate isometry. On
one base's horizontal subspace, its own camera vanishes and the seed plus all
other cameras gives the off-base resolution identity. This horizontal theorem
is not inferred from a vertical stencil estimate.

The explicit Green estimate is

```text
C_G = 3/2 + 12 S2 + 3 S3,
S2 = sum_(b>=2) b^(-2),
S3 = sum_(b>=2) b^(-3).
```

## Exact frame and Poisson split

The paper coefficient decomposition is represented literally as

```text
external = seed + residual + G1
bulk     = G>=2
T        = ((seed, residual, G1), G>=2).
```

The Green energy identity `||Gf||^2=||G1 f||^2+||G>=2 f||^2` prevents the
global Bessel bound from being counted twice. The concrete analysis therefore
has squared-norm bounds `1/2` and `C_F=1+C_G`.

After canonical inverse-square-root normalization, the external map is bounded
below by `1/(2 C_F)`, has closed range, and supports both a restricted static
Poisson map on compatible external data and an ambient zero extension. The
coherent normalized image is the closed restricted graph.

The canonical bulk witness is `(base,n)=(2,4)` on `e4`, which lies in `G>=2`.
It yields `||B0||^2 >= 1/(4 C_F)`. The depth-one `(2,2)` witness is not evidence
for a bulk claim.

## Finite sections and their boundary

The finite maps are literal common-space sections

```text
T_N = Q_N T P_N,
```

where the masks retain both `n<=N` and `base<=N`. Their ranges are finite, the
frame bounds are uniform in `N`, and `T_N f -> T f` is the exact `FS-002`
theorem.

For `FS-003`, v2 records only a named conditional implication: if the CFC
inverse square roots of the common-space extended finite frame operators
converge strongly, then the embedded normalized analyses converge strongly to
the canonical analysis. Here the finite normalized map is definitionally the
common-space composition `S_N R_N`; v2 does not also claim an identification
with a separately bundled finite-domain operator. That CFC hypothesis is not
discharged in v2.

`FS-004` remains `OPEN`: the repository does not claim strong convergence of
finite Poisson operators. The Weyl family remains a future spectral layer.

## Reproduce the exact release evidence

```bash
lake build --wfail GreenFrame
lake env lean GreenFrame/Audit.lean
./scripts/run_audits.sh
```

The audit derives all counts from the checked tree, verifies the 16 preserved
research inputs byte-for-byte, checks the full public import closure, rejects
forbidden trust escapes and enforces the foundational allowlist
`Classical.choice`, `Quot.sound`, and `propext`.

Research Markdown and Python laboratories are provenance, not kernel premises.
The project does not infer a zero theorem, a special-function identity, a
functional equation, a primality result, an infinite self-adjoint height
operator, finite-Poisson convergence or a Weyl family.

## Citation and history

Citation metadata is in `CITATION.cff` and `.zenodo.json`. Tag `v1.0.0` remains
unchanged as historical material. Release `v2.0.0` is evidence only for the
exact commit, tree and Actions runs recorded in its audit manifest.
