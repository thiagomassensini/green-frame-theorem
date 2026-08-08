# Arithmetic partition and horizontal atlas

This layer constructs the all-base weights used by every later analytic
operator. It also constructs the elementary horizontal atlas. The atlas result
is recorded here because it depends on the arithmetic partition, but it is
mathematically separate from the vertical Green stencil.

## Positional depth for every base

For an integer base `b >= 2` and a positive integer `n`, the positional depth
is

```text
k_b(n) = max { k : b^k divides n }.
```

No primality hypothesis is imposed. For fixed `n`, positive depth implies
`b | n` and therefore `2 <= b <= n`; only finitely many bases are active.
This is the finiteness mechanism behind `ABGF-AR-001`.

The canonical activity and normalizer are

```text
x_b(n) = k_b(n) * log b,
A(n)   = sum_{c=2}^n x_c(n).
```

For `n > 1`, the canonical camera weight is

```text
omega_b(n) = x_b(n) / A(n),
```

with weight zero outside active divisors. The normalizer is positive, every
weight is nonnegative, the support is finite, and

```text
sum_{b>=2} omega_b(n) = 1.
```

The Lean API packages the same properties in
`AdmissibleInfinitePartition`, so the analytic construction can be reused for
other admissible weights while retaining the canonical carry instance as the
release object.

## Depth-one activity cannot disappear

Split the canonical activity at a nonseed coordinate into

```text
A1(n)    = sum of x_b(n) over k_b(n)=1,
A>=2(n)  = sum of x_b(n) over k_b(n)>=2.
```

The endpoint-charge construction sends every bulk contribution to a
depth-one endpoint and proves

```text
A>=2(n) <= 2 * A1(n).
```

Consequently,

```text
1/3 <= A1(n) / A(n).
```

This is an exact arithmetic statement about the canonical weights. It is not
an optimized frame bound and it does not identify depth-one events with the
depth-at-least-two bulk.

## Elementary atlas

For an admissible partition, the elementary camera coordinate at `(b,n)` is
the state coordinate multiplied by the square root of its camera weight. The
atlas combines the seed with every such coordinate:

```text
A(f) = (f(1), (sqrt(omega_b(n)) * f(n))_(b,n)).
```

The partition identity gives the exact norm formula

```text
||A(f)||^2 = ||f||^2,
```

and hence an actual linear isometry, not merely a scalar bookkeeping lemma.
The canonical carry atlas is the corresponding specialization.

## Horizontal off-base resolution

Fix one base `a`. On the horizontal subspace for that base, the elementary
camera belonging to `a` vanishes. The seed and the cameras of all remaining
bases then resolve the state norm exactly. This is the content of
`ABGF-AN-002`.

The word *horizontal* refers to this fixed-base subspace identity. The
coordinate cameras in the identity are the elementary weighted cameras; the
theorem is not derived from, and must not be restated as, the vertical
second-difference stencil or its TFVD chart.

## Canonical coordinate `(2,4)`

At `n=4`, the active canonical bases are `2` and `4`, with equal log-depth
activities and weights `1/2`. The base-two event has depth two. Later, after
the Green/return split, that exact event on `e4` supplies the canonical bulk
witness. A depth-one event such as `(2,2)` cannot witness a `G>=2` claim.

## Claim evidence

| Claim | Kernel evidence |
|---|---|
| `ABGF-AR-001` | `GF-061`, `GF-089`, `GF-095` |
| `ABGF-AR-002` | `GF-056`, `GF-062`, `GF-096`, `GF-097` |
| `ABGF-AR-003` | `GF-374`, `GF-377` |
| `ABGF-AN-001` | `GF-399`, `GF-400`, `GF-402`, `GF-404` |
| `ABGF-AN-002` | `GF-409`, `GF-419` |

The qualified declaration names and authoritative statuses are recorded in
the claim ledger. The GF numbers above are coordinates in the fixed
`GF-001`--`GF-494` v2 registry, not substitutes for the exact-SHA audit.
