# Green and return analysis

For a camera mass `weight` and base scale `base`, the formal split is

```text
greenMass    = weight / base
residualMass = weight * (1 - 1/base)
```

For every `base ≥ 2`, the residual factor is at least `1/2` and the Green factor is at most `1/2`. Their sum is exactly the original weight.

The local second-difference stencil is bounded by a three-term quadratic estimate. Summing this estimate over a finite index set gives the formal Green Bessel lemma used by the frame ledger.
