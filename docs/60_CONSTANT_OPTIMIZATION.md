# Certified constants and optimization boundary

V2 exposes universal constants sufficient for the concrete all-bases frame,
Parseval, Poisson, bulk, and finite-section theorems. They are certified
bounds, not asserted optima.

## Certified constants

Define the convergent positive series

```text
S2 = sum_{b>=2} b^(-2),
S3 = sum_{b>=2} b^(-3).
```

The Green and full-frame constants are

```text
C_G = 3/2 + 12*S2 + 3*S3,
C_F = 1 + C_G.
```

The registered release statements use them as follows:

| Quantity | Certified v2 bound | Principal evidence |
|---|---|---|
| Global Green analysis | `||G f||^2 <= C_G ||f||^2` | `GF-171`, `GF-174`, `GF-177` |
| Full analysis | `(1/2)||f||^2 <= ||T f||^2 <= C_F||f||^2` | `GF-280`, `GF-281`, `GF-282` |
| Normalized external map | `||E0 f||^2 >= (1/(2*C_F))||f||^2` | `GF-303`, with `GF-282`, `GF-283` |
| Normalized canonical bulk | `||B0||^2 >= 1/(4*C_F)` | `GF-349`, `GF-350` |
| Concrete finite sections | the same `1/2` and `C_F`, uniformly in `N` | `GF-474`, `GF-475` |

The lower bulk constant comes from the explicit `(base,n)=(2,4)` event on
`e4`; it is not inferred from a numerical singular value and it does not use
the depth-one `(2,2)` event.

## Why `C_G` is conservative

The global proof deliberately uses three uniform relaxations:

1. the unweighted three-term estimate
   `|u+v+w|^2 <= 3(|u|^2+|v|^2+|w|^2)`;
2. the pointwise replacement of an arithmetic camera weight by
   `omega_b(n) <= 1` in the ancestor terms;
3. summation over every base `b >= 2`, without exploiting all simultaneous
   divisibility restrictions at a fixed coordinate.

These steps yield the transparent contributions

```text
current      : 3/2,
parent       : 12*S2,
grandparent  : 3*S3.
```

The exact Green depth decomposition is then used once:

```text
||G f||^2 = ||G1 f||^2 + ||G>=2 f||^2.
```

Consequently `C_F=1+C_G`. Bounding `G1` and `G>=2` independently by the full
`C_G` would produce an avoidable double count and would not describe the v2
frame theorem.

## Certified arithmetic information available for refinements

The canonical endpoint-charge theorem proves

```text
bulkActivity(n) <= 2 * depthOneActivity(n),
depthOneActivity(n) / allBaseNormalizer(n) >= 1/3.
```

This is kernel evidence (`GF-374`, `GF-377`) and may support sharper external
estimates. V2 does not claim that it already improves the published lower
frame constant or determines an optimal distribution between `G1` and
`G>=2`.

## Legitimate optimization routes

Future improvements may use:

- weighted Young inequalities with base-dependent parameters;
- a Schur test for the sparse Gram operator on the multiplicative graph
  `n <-> b*n <-> b^2*n`;
- the exact log-depth ratio
  `omega_b(n)=k_b(n) log(b)/A(n)` instead of the bound `omega<=1`;
- the proved depth-one activity share to sharpen the normalized external
  coercivity;
- restricted base families, provided a new admissible partition and lower
  frame mechanism are proved rather than assumed.

These are research directions, not hidden premises of the registered bounds.

## Optimization problems

For the fixed canonical analysis, one may define the paper-level optimization
quantities

```text
A_* = inf_{||f||=1} ||T f||^2,
B_* = sup_{||f||=1} ||T f||^2.
```

The registered frame inequality immediately constrains these quantities by

```text
1/2 <= A_* <= B_* <= C_F,
```

This displayed consequence is not a separate v2 ledger row. V2 does not
determine either extremum, prove that either is attained, or identify optimal
Poisson and external constants. Any later sharper value must receive its own
theorem evidence and claim-ledger mapping.

## Numerical evidence policy

The preserved Python laboratories may compare finite spectra, test candidate
constants, and guide stronger conjectures. Such computations remain
provenance and regression evidence. They cannot replace an infinite `l2`
bound, discharge the `FS-003` CFC hypothesis, prove `FS-004`, or alter the
20-kernel/1-conditional/1-open/1-future release partition.
