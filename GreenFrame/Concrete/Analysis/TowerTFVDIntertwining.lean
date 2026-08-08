import GreenFrame.Concrete.Analysis.TowerTFVDCoordinates

/-!
# Normalized tower TFVD: chart intertwining

Third physical checkpoint for `ABGF-GR-003`, independent of root extraction:
an exact representation chart and the unweighted/weighted intertwining, with
no stencil equality stored as a field.

This module deliberately contains no atlas-completeness proposition.  The
next arithmetic checkpoints construct a chart for every global event.
-/

open scoped ENNReal lp

namespace GreenFrame.Concrete

/-- Exact identification of one global Green event with a normalized tower event. -/
structure TowerChart (e : GreenEvent) where
  /-- Tower event representing the global event. -/
  tower : TowerEvent
  /-- The chart preserves the camera code. -/
  code_eq : tower.code = e.1
  /-- The tower current node is the global event number. -/
  current_eq : tower.current = eventNumber e
  /-- The tower parent is the global event parent. -/
  parent_eq : tower.parent = e.2
  /-- At depth at least two, the tower and global second ancestors agree. -/
  grandparent_eq : 2 ≤ tower.depth →
    tower.grandparent = grandparentIndex e
  /-- The global second-ancestor guard is exactly the tower depth guard. -/
  hasGrandparent_iff : HasGrandparent e ↔ 2 ≤ tower.depth

/-- A tower chart transports the global second-ancestor guard exactly. -/
theorem TowerChart.hasGrandparent
    {e : GreenEvent} (c : TowerChart e) :
    HasGrandparent e ↔ 2 ≤ c.tower.depth :=
  c.hasGrandparent_iff

/-- The global vertical stencil is the tower TFVD represented by any exact chart. -/
theorem verticalGreenStencil_eq_normalizedTowerTFVD_of_chart
    {e : GreenEvent} (c : TowerChart e) (f : State) :
    verticalGreenStencil e f = normalizedTowerTFVD c.tower f := by
  by_cases hg : HasGrandparent e
  · have hd : 2 ≤ c.tower.depth := c.hasGrandparent_iff.mp hg
    simp only [verticalGreenStencil, currentTerm, parentTerm,
      grandparentTerm, hg, if_true, normalizedTowerTFVD, hd]
    rw [c.code_eq, c.current_eq, c.parent_eq, c.grandparent_eq hd]
    ring
  · have hd : ¬ 2 ≤ c.tower.depth := by
      intro hdepth
      exact hg (c.hasGrandparent_iff.mpr hdepth)
    simp only [verticalGreenStencil, currentTerm, parentTerm,
      grandparentTerm, hg, if_false, normalizedTowerTFVD, hd]
    rw [c.code_eq, c.current_eq, c.parent_eq]
    ring

/-- Weighted Green coordinates intertwine with the normalized tower TFVD. -/
theorem greenCoordinate_eq_normalizedTowerTFVD_of_chart
    (omega : AdmissibleInfinitePartition) {e : GreenEvent}
    (c : TowerChart e) (f : State) :
    greenCoordinate omega e f =
      ((greenAmplitude omega e : ℝ) : ℂ) *
        normalizedTowerTFVD c.tower f := by
  rw [greenCoordinate,
    verticalGreenStencil_eq_normalizedTowerTFVD_of_chart c f]

end GreenFrame.Concrete
