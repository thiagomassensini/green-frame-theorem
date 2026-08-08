# Canonical Parseval and static Poisson completion

The Poisson layer reconstructs the normalized depth-at-least-two bulk from
compatible normalized external coefficients. It is a fixed bounded operator
constructed from the canonical Parseval analysis; it is not a convergence
statement and it is not a Weyl function.

## Normalized external and bulk maps

For the exact frame split, write

```text
V  = T F^(-1/2) = (E0, B0),
E0 = E F^(-1/2),
B0 = B F^(-1/2),
```

where

```text
E = seed + residual + G1,
B = G>=2.
```

Since `V` is an isometry,

```text
E0* E0 + B0* B0 = I.
```

The external component has the quantitative lower bound

```text
||E0 f||^2 >= (1 / (2*C_F)) * ||f||^2.
```

It is therefore injective and antilipschitz, and `range(E0)` is closed.

## Restricted and ambient Poisson maps

On the closed compatible range, the restricted Poisson map is the unique
bounded map satisfying

```text
M_res (E0 f) = B0 f.
```

Equivalently, introduce the canonical external left inverse

```text
S_E = (E0* E0)^(-1) E0*
```

and define the ambient zero extension

```text
M_AB = B0 S_E.
```

The exact intertwining identity is

```text
M_AB E0 = B0.
```

The ambient operator first projects arbitrary external data to its compatible
component; on the orthogonal complement of `range(E0)`, the canonical left
inverse vanishes. The restricted theorem and the ambient theorem are both
registered, so the domain convention is explicit rather than hidden in the
phrase “Poisson operator.”

## Closed coherent graph

The normalized coherent image is exactly

```text
range(V)
  = { (y, M_res y) : y in range(E0) }.
```

Because `range(E0)` is closed and the restricted Poisson map is bounded, this
is a closed graph. The statement concerns the coherent coefficient image of
the static normalized analysis, not an orbit or a cutoff limit.

## Canonical nontrivial bulk

At `(base,n)=(2,4)`, the canonical weights satisfy `omega_2(4)=1/2`, hence
the base-two Green mass is `1/4`. The event has a grandparent and therefore
belongs to `G>=2`. Applied to `twoFourWitnessState=e4`, its raw coordinate
gives

```text
||B e4||^2 >= 1/4.
```

Transferring the witness through the frame square root yields the normalized
operator bound

```text
||B0||^2 >= 1 / (4*C_F).
```

This is a quantitative bulk theorem. The depth-one point `(2,2)` is excluded
because it belongs to `G1`, which is external in the v2 split.

## Claim evidence

| Claim | Kernel evidence |
|---|---|
| `ABGF-PO-001` | `GF-303`, with `GF-282` and `GF-283` fixing the concrete constants |
| `ABGF-PO-002` | `GF-305`, `GF-307` |
| `ABGF-PO-003` | `GF-310`, `GF-357` |
| `ABGF-PO-004` | `GF-313`, `GF-314` |
| `ABGF-BK-001` | `GF-328`, `GF-344`, `GF-347`, `GF-348` |
| `ABGF-BK-002` | `GF-349`, `GF-350` |

## Boundaries of this document

- The vertical normalized-tower TFVD theorem identifies a stencil; it does
  not construct this Poisson map.
- The horizontal off-base theorem is an elementary-atlas resolution; it does
  not imply Poisson reconstruction.
- `ABGF-FS-004`, strong convergence of finite Poisson operators, is `OPEN`
  and has no theorem IDs in v2.
- `ABGF-WEYL-001` is `FUTURE_LAYER`. A static bounded map `M_AB` is not the
  parameter-dependent Schur complement of a `log n` generator.
