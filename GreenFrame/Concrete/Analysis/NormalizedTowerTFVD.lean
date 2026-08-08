import GreenFrame.Concrete.Analysis.CanonicalTowerChart

/-!
# Canonical normalized-tower TFVD

Thin public aggregator for the acyclic `ABGF-GR-003` chain:

1. `TowerTFVDCoordinates`;
2. `TowerRootExtraction` and `TowerTFVDIntertwining` (independent branches,
   promoted in that physical order);
3. `CanonicalTowerChart`.

The final module constructs the chart for every event.  There is no abstract
atlas-completeness assumption in this API.
-/
