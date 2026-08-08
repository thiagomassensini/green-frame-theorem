# Scope and trust boundary

This document fixes the permanent scope of the Green Frame Theorem v2
formalization. It does not grant evidence status by itself. The authoritative
release surface is the conjunction of the public Lean import closure, the
ordered theorem registry, the named axiom report, the claim ledger, and the
exact-SHA release audit.

## Audited theorem surface

The v2 registry is contiguous from `GF-001` through `GF-494` and contains 494
public theorem declarations. The 23 claims inherited from the primary
specification have the following exact partition:

| Status | Count | Meaning |
|---|---:|---|
| `KERNEL_CHECKED` | 20 | The cited declarations establish the claim at the exact audited release SHA. |
| `CONDITIONAL` | 1 | A registered implication establishes the conclusion only under its stated, undischarged hypothesis. |
| `OPEN` | 1 | No theorem evidence is claimed in v2. |
| `FUTURE_LAYER` | 1 | The proposed construction is deliberately outside the v2 theorem surface. |

Thus the release boundary is exactly

```text
23 claims = 20 kernel + 1 conditional + 1 open + 1 future.
```

`ABGF-FS-003` is the conditional row. `ABGF-FS-004` is open. Only
`ABGF-WEYL-001` belongs to the future layer.

`KERNEL_CHECKED` means more than the presence of a plausible theorem name. At
the release SHA, each cited qualified declaration must be reachable from the
public root, occur in the JSON registry, the Markdown registry, and
`GreenFrame/Audit.lean` in the same order, and have a named `#print axioms`
report. The permitted foundational axiom set is limited to
`Classical.choice`, `Quot.sound`, and `propext`.

## Mathematical object

The state space is complex `l2` on the positive integers. Every integer base
`b >= 2`, prime or composite, participates through positional carry depth.
Canonical log-depth weights distribute each nonseed coordinate among its
finitely many active bases. Every camera weight is then divided into an
orthogonal Green-transmitted part and a residual-return part.

The coefficient split used by every frame, Parseval, Poisson, bulk, and finite
section statement is literal:

```text
external = seed + residual + G1
bulk     = G>=2
T        = ((seed, residual, G1), G>=2).
```

Here `G1` contains Green events without a grandparent, while `G>=2` contains
events with a grandparent. The canonical nontrivial-bulk witness is
`(base,n)=(2,4)` on `twoFourWitnessState=e4`.

## Distinct layers

The repository keeps three constructions separate because none is a renaming
of another:

| Layer | Content | What it is not |
|---|---|---|
| Vertical Green | Multiplicative parent and grandparent stencil, together with its normalized-tower TFVD chart. | The horizontal atlas identity. |
| Horizontal atlas | Seed plus weighted coordinate cameras, with exact off-base resolution on one base's horizontal subspace. | A second-difference Green estimate. |
| Static Poisson | Bounded reconstruction of the normalized coherent bulk from compatible normalized external coefficients. | Finite-Poisson convergence or a Weyl family. |

The finite-section layer approximates the already constructed analysis map in
a common ambient space. It does not merge these three mathematical roles.

## What v2 establishes

The 20 kernel rows cover:

- finite active support and the canonical all-base partition of unity;
- the depth-one activity share and the elementary horizontal atlas;
- conservative Green/return masses, the normalized-tower TFVD identity, and
  the global Green Bessel estimate;
- the concrete frame bounds, frame-operator invertibility, and canonical
  Parseval normalization;
- the exact static Poisson intertwining and closed coherent graph;
- a quantitative nonzero normalized bulk witnessed at `(2,4)` on `e4`;
- literal finite sections with uniform bounds and strong convergence of
  `Q_N T P_N` to `T`.

The exact declaration map is maintained in `audit/claim-ledger.json` and
`audit/CLAIM_LEDGER.md`; these overview documents do not replace that map.

## Explicit boundaries

V2 does not claim:

- an unconditional proof that the normalized finite analyses converge;
- construction or strong convergence of finite Poisson operators;
- a Weyl or Schur-complement family for the `log n` generator;
- an infinite self-adjoint height operator or a maximal-extension theorem;
- a zero theorem, special-function identity, analytic continuation,
  functional equation, or primality result;
- optimal frame, external, bulk, or Poisson constants.

For `ABGF-FS-003`, v2 registers a conditional implication whose missing input
is the strong limit of common-space CFC inverse square roots. For
`ABGF-FS-004`, there are no theorem IDs. Static Poisson reconstruction must not
be cited as evidence for either finite-Poisson convergence or the future Weyl
layer.

## Source and evidence boundary

The preserved research Markdown and Python laboratories document provenance,
paper arguments, finite experiments, and the route by which the formalization
was designed. They are not Lean premises and do not promote a claim to kernel
status. Likewise, a successful audit from a different commit, a historical
release artifact, or a matching numerical experiment is not evidence for the
v2 release SHA.
