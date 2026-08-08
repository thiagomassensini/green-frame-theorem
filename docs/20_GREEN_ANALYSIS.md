# Vertical Green and return analysis

The vertical layer turns each arithmetic camera weight into a conservative
pair of orthogonal coefficient channels and applies the three-level Green
stencil along multiplicative ancestor towers.

## Conservative fibre split

For camera weight `omega_b(n)` and base `b >= 2`, define

```text
mu_G(b,n) = omega_b(n) / b,
mu_R(b,n) = omega_b(n) * (1 - 1/b).
```

The identity

```text
mu_G(b,n) + mu_R(b,n) = omega_b(n)
```

holds pointwise before summing over bases or state coordinates. The two masses
are implemented in distinct coefficient coordinates, so this is a
Pythagorean conservation law rather than cancellation between signed terms.

For every nonseed coordinate, summing the residual masses over cameras gives

```text
1/2 <= sum_b mu_R(b,n) <= 1.
```

The lower bound is the source of the universal lower frame estimate. It does
not depend on a selected base or on a finite cutoff.

## Three-level vertical stencil

The Green coordinate associated with an active event `(b,n)` is the
`sqrt(mu_G(b,n))`-weighted second difference

```text
f(n) - 2 b^(-1/2) f(n/b)
     + 1_{b^2 divides n} b^(-1) f(n/b^2).
```

The current coordinate, parent, and optional grandparent follow the
multiplicative tower of the same base. Composite bases are treated by the same
positional-depth construction; no prime valuation theorem is assumed.

The formal tower chart is constructed independently and then identified with
the global stencil. The v2 evidence includes both the normalized-tower TFVD
identity and its literal depth-one truncation. A matching informal formula
alone would not close `ABGF-GR-003`.

## Depth sectors

The Green event space is partitioned into two literal subtypes:

```text
G1     = events without a grandparent,
G>=2   = events with a grandparent.
```

Their coordinate projections are orthogonal and recombine the total Green
energy exactly:

```text
||G f||^2 = ||G1 f||^2 + ||G>=2 f||^2.
```

This identity is essential later: the frame upper bound contains the global
Green constant once, even though `G1` is grouped with the external sector and
`G>=2` with the bulk.

## Global Bessel estimate

Let

```text
S2 = sum_{b>=2} b^(-2),
S3 = sum_{b>=2} b^(-3),
C_G = 3/2 + 12*S2 + 3*S3.
```

The three stencil levels contribute respectively `3/2`, `12*S2`, and
`3*S3`. The resulting concrete `l2` analysis satisfies

```text
||G f||^2 <= C_G * ||f||^2.
```

The estimate proves summability and boundedness of the global Green analysis,
not only a bound for one finite matrix. `C_G` is explicit and universal, but
v2 makes no optimality claim.

## Separation from the other layers

- The horizontal theorem is the elementary-atlas off-base resolution, not a
  restriction of this stencil.
- Static Poisson is constructed only after frame normalization and acts
  between external and bulk coefficient sectors.
- A future Weyl family would require a parameter-dependent spectral boundary
  problem; the normalized-tower TFVD identity is not such a family.

## Claim evidence

| Claim | Kernel evidence |
|---|---|
| `ABGF-GR-001` | `GF-063` |
| `ABGF-GR-002` | `GF-191`, `GF-192`, `GF-225` |
| `ABGF-GR-003` | `GF-428`, `GF-438`, `GF-439`, `GF-441` |
| `ABGF-GR-004` | `GF-171`, `GF-174`, `GF-177` |

The claim ledger supplies the qualified declarations and exact release
status. These rows are part of the 20-claim kernel surface only at the exact
audited v2 SHA.
