# Concrete Green frame and canonical Parseval normalization

The frame theorem is stated for the actual all-bases analysis operator. It is
not obtained by assuming an abstract frame certificate for an unspecified
map.

## Exact coefficient split

For an admissible camera partition, write

```text
E f = (seed f, residual f, G1 f),
B f = G>=2 f,
T f = (E f, B f).
```

Thus, literally,

```text
external = seed + residual + G1
bulk     = G>=2
T        = ((seed, residual, G1), G>=2).
```

The codomain products are `L2` products, so the squared norm is

```text
||T f||^2
  = |f(1)|^2 + ||residual f||^2
    + ||G1 f||^2 + ||G>=2 f||^2
  = |f(1)|^2 + ||residual f||^2 + ||G f||^2.
```

The last equality uses the orthogonal Green depth split. It prevents `G1` and
`G>=2` from being bounded separately by `C_G` and then counted twice.

## Uniform frame bounds

Set

```text
C_G = 3/2 + 12*S2 + 3*S3,
C_F = 1 + C_G.
```

For every state `f`, the concrete operator satisfies

```text
(1/2) * ||f||^2 <= ||T f||^2 <= C_F * ||f||^2.
```

The lower bound comes from the seed and residual-return coordinates; all
Green terms are nonnegative. The seed-residual energy is at most `||f||^2`,
and the entire Green energy is at most `C_G ||f||^2`, giving the upper bound.
Both constants are independent of coordinate, base, and cutoff.

`ABGF-FR-001` is the concrete bound with this precise split. A generic scalar
interval lemma or a theorem parameterized by unconstructed cutoff data is not
equivalent evidence.

## Frame operator

Define

```text
F = T* T.
```

The quadratic bounds give

```text
(1/2) I <= F <= C_F I.
```

For the concrete `T`, v2 registers positivity, strict positivity,
invertibility, and bijectivity of `F`. In particular, the inverse square root
is defined by continuous functional calculus on a spectrum separated from
zero.

The generic operator-theory heads in the registry are used with the explicit
specialization

```text
T      = concreteAnalysisOperator canonicalCarryInfinitePartition,
bounds = concreteSplitFrameBounds canonicalCarryInfinitePartition.
```

This specialization consumes the constructed concrete bounds; it does not
postulate them.

## Canonical Parseval normalization

Define

```text
V = T F^(-1/2).
```

Then

```text
V* V = I
```

and `V` is an isometry. The normalization is the canonical CFC inverse-square
root normalization of the same concrete frame operator. V2 does not replace
it with a supplied linear isometry or a normalization certificate.

Writing `V=(E0,B0)` preserves the exact coefficient grouping:

```text
E0 = E F^(-1/2),
B0 = B F^(-1/2).
```

This normalized split is the input to the static Poisson construction.

## Claim evidence

| Claim | Kernel evidence |
|---|---|
| `ABGF-FR-001` | `GF-280`, `GF-281`, `GF-282` |
| `ABGF-FR-002` | `GF-286`, `GF-288`, `GF-289`, `GF-290` |
| `ABGF-FR-003` | `GF-294`, `GF-295`, `GF-296`, `GF-298` |

The authoritative ledger records the qualified names and the concrete
instantiations. The displayed inequalities are certified constants, not a
claim that `1/2` and `C_F` are optimal frame bounds.
