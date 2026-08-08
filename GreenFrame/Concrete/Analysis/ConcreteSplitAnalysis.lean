import GreenFrame.Concrete.Analysis.ConcreteSplitBounds

/-!
# Concrete paper external/bulk split analysis

Thin public aggregator for the exact paper split:

* external = seed + residual + depth-one Green rows;
* bulk = depth-at-least-two Green rows.

`ConcreteSplitOperators` supplies the literal Hilbert-sum operators and exact
energy recombination.  `ConcreteSplitBounds` supplies the sharp ledger
`lower = 1/2`, `upper = 1 + greenBesselConstant` without counting the Green
estimate twice.
-/
