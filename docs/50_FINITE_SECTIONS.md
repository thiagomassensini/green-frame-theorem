# Concrete finite sections and limit boundary

The finite-section layer uses literal coordinate masks in the same ambient
state and coefficient spaces as the infinite operator. Its exact results are
uniform finite bounds and strong convergence of the unnormalized analysis.
Normalized convergence is conditional; finite-Poisson convergence is open.

## Literal masks

Let `P_N = stateCoordinateCutoff N`. It retains the state coordinates

```text
n <= N.
```

Let `Q_N = concreteCoefficientCutoff N`. It keeps the seed and retains each
residual, depth-one, and bulk row only when both

```text
event number <= N,
physical base <= N.
```

Both masks are contractive and idempotent. Their ranges are identified with
the corresponding finite-support submodules, and the retained index types are
finite. At a retained state coordinate, every nonzero camera automatically
has physical base at most `N` because active bases divide the coordinate.

Define the common-space section literally by

```text
S_N = Q_N T P_N
    = concreteEmbeddedFiniteAnalysis omega N.
```

The bundled finite-domain map is the restriction of `S_N` to
`H_N = range(P_N) = FiniteState N`.

## Uniform bounds: `ABGF-FS-001`

For every `f` in `H_N`, the concrete section retains the full seed-residual
analysis needed for the lower bound, while `Q_N` remains contractive for the
upper bound. Therefore

```text
(1/2) * ||f||^2 <= ||S_N f||^2 <= C_F * ||f||^2,
C_F = 1 + C_G,
```

uniformly in `N`. The statement is proved both for the embedded map and the
bundled `H_N` operator. It is stronger than pointwise numerical invertibility
of each finite matrix.

Registry evidence is:

- `GF-476 GreenFrame.Concrete.stateCoordinateCutoff_range`;
- `GF-474 GreenFrame.Concrete.concreteEmbeddedFiniteAnalysis_norm_sq_bounds`;
- `GF-475 GreenFrame.Concrete.concreteFiniteAnalysisOperator_norm_sq_bounds`.

## Strong analysis limit: `ABGF-FS-002`

The state and coefficient masks converge pointwise to the identity in their
respective `l2` spaces. The standard two-term estimate then gives, for every
state `f`,

```text
S_N f = Q_N T P_N f -> T f.
```

This exact common-space theorem is
`GF-493 GreenFrame.Concrete.concreteEmbeddedFiniteAnalysis_tendsto`.

## Conditional normalized limit: `ABGF-FS-003`

To avoid a kernel on the complement of `H_N`, define the common-space finite
frame extension

```text
Fhat_N
  = frameOperator(S_N) + (1 - P_N)
  = extendedFiniteFrameOperator omega N.
```

Its CFC inverse square root and the embedded normalized analysis are

```text
R_N = CFC.rpow(Fhat_N, -1/2),
V_N = S_N R_N.
```

In this row, `V_N` means exactly this common-space composition. V2 does not
also claim an identification with a separately bundled finite-domain
normalization.

The registered theorem is

```text
GF-494 GreenFrame.Concrete.concreteEmbeddedCanonicalAnalysis_tendsto_of_extendedInverseSqrt_tendsto
```

and proves the implication

```text
[for every f, R_N f -> F^(-1/2) f]
  ==> [for every f, V_N f -> V f].
```

The antecedent is not discharged in v2. It is the missing strong
continuous-functional-calculus limit for the inverse square roots. For this
reason the ledger status is `CONDITIONAL`, not `KERNEL_CHECKED`, even though
the implication itself is a registered theorem.

## Open finite-Poisson limit: `ABGF-FS-004`

V2 constructs neither a finite normalized external pseudoinverse compatible
with the above common-space model nor a theorem that finite Poisson maps
converge strongly to `M_AB`. Accordingly:

```text
ABGF-FS-004 = OPEN
theorem IDs = []
```

Finite experiments and the exact static identity `M_AB E0 = B0` do not fill
this gap. The open step begins only after the `FS-003` CFC hypothesis has been
discharged and the finite normalized external inverses have been controlled.

## Status summary

| Claim | Status | Evidence or boundary |
|---|---|---|
| `ABGF-FS-001` | `KERNEL_CHECKED` | `GF-474`, `GF-475`, `GF-476` |
| `ABGF-FS-002` | `KERNEL_CHECKED` | `GF-493` |
| `ABGF-FS-003` | `CONDITIONAL` | `GF-494`, under the explicit common-space CFC inverse-square-root limit |
| `ABGF-FS-004` | `OPEN` | No theorem IDs; finite Poisson convergence is not constructed in v2 |

As everywhere in the repository, the statuses become release evidence only
through the exact-SHA registry, named axiom report, and release audit.
