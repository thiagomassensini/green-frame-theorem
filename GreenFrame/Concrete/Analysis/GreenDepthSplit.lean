import GreenFrame.Concrete.Analysis.GreenDepthSectorOperator

/-!
# Canonical depth split of the global Green analysis

Thin public aggregator for the acyclic canonical depth-split checkpoint chain:

1. `GreenDepthCoordinates`;
2. `GreenDepthMaskedEnergy`;
3. `GreenDepthMaskedOperator`;
4. `GreenDepthSectorEnergy`;
5. `GreenDepthSectorOperator`.

The resulting paper split is external = seed + residual + `G1` and bulk =
`G>=2`, where the literal bulk rows satisfy `HasGrandparent`.
-/
