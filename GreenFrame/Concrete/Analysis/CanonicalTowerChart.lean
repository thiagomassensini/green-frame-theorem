import GreenFrame.Concrete.Analysis.TowerRootExtraction
import GreenFrame.Concrete.Analysis.TowerTFVDIntertwining

/-!
# Canonical normalized-tower chart

Fourth checkpoint for `ABGF-GR-003`: instantiate a canonical positive-depth
tower event and the chart intertwining without a supplied completeness
hypothesis.
-/

open scoped ENNReal lp

namespace GreenFrame.Concrete

/-- The current global event has tower depth one more than its parent. -/
def canonicalTowerEvent (e : GreenEvent) : TowerEvent where
  code := e.1
  root := eventTowerRoot e
  depth := eventParentDepth e + 1
  depth_pos := by omega

/-- The canonical tower event has the original global event parent. -/
theorem canonicalTowerEvent_parent (e : GreenEvent) :
    (canonicalTowerEvent e).parent = e.2 := by
  apply PNat.eq
  simpa [canonicalTowerEvent, TowerEvent.parent, towerNode,
    eventTowerRoot, eventTowerRootPNat] using eventParent_factorization e

/-- The canonical tower event reaches the original global event number. -/
theorem canonicalTowerEvent_current (e : GreenEvent) :
    (canonicalTowerEvent e).current = eventNumber e := by
  apply PNat.eq
  simp [canonicalTowerEvent, TowerEvent.current, towerNode,
    eventTowerRoot, eventTowerRootPNat, eventNumber_coe]
  calc
    baseNat e.1 ^ (eventParentDepth e + 1) * eventTowerRootNat e =
        baseNat e.1 *
          (baseNat e.1 ^ eventParentDepth e * eventTowerRootNat e) := by
      rw [pow_succ]
      ring
    _ = baseNat e.1 * (e.2 : ℕ) := by
      rw [eventParent_factorization]

/-- The global second-ancestor predicate is exactly canonical tower depth at least two. -/
theorem canonicalTowerEvent_hasGrandparent (e : GreenEvent) :
    HasGrandparent e ↔ 2 ≤ (canonicalTowerEvent e).depth := by
  change (baseNat e.1 : ℕ) ∣ (e.2 : ℕ) ↔
    2 ≤ eventParentDepth e + 1
  constructor
  · intro h; have := (positionalDepth_pos_iff_dvd (baseNat_ge_two e.1) e.2.property).2 h; omega
  · intro h; apply (positionalDepth_pos_iff_dvd (baseNat_ge_two e.1) e.2.property).1; omega
  -- The two directions avoid coercion-sensitive rewriting under the equivalence.

/-- At depth at least two, the canonical tower and global second ancestors agree. -/
theorem canonicalTowerEvent_grandparent
    (e : GreenEvent) (hdepth : 2 ≤ (canonicalTowerEvent e).depth) :
    (canonicalTowerEvent e).grandparent = grandparentIndex e := by
  have hg : HasGrandparent e :=
    (canonicalTowerEvent_hasGrandparent e).mpr hdepth
  have hk : 0 < eventParentDepth e := by
    change 2 ≤ eventParentDepth e + 1 at hdepth
    omega
  apply mul_left_cancel (a := basePNat e.1)
  rw [base_mul_grandparentIndex hg]
  apply PNat.eq
  simp [canonicalTowerEvent, TowerEvent.grandparent, towerNode,
    eventTowerRoot, eventTowerRootPNat]
  calc
    baseNat e.1 *
        (baseNat e.1 ^ (eventParentDepth e + 1 - 2) *
          eventTowerRootNat e) =
        baseNat e.1 ^ eventParentDepth e * eventTowerRootNat e := by
      have hsub : eventParentDepth e + 1 - 2 = eventParentDepth e - 1 := by
        omega
      rw [hsub]
      have hsucc : eventParentDepth e - 1 + 1 = eventParentDepth e := by
        omega
      calc
        baseNat e.1 *
              (baseNat e.1 ^ (eventParentDepth e - 1) *
                eventTowerRootNat e) =
            (baseNat e.1 * baseNat e.1 ^ (eventParentDepth e - 1)) *
              eventTowerRootNat e := by
          ring
        _ = baseNat e.1 ^ (eventParentDepth e - 1 + 1) *
              eventTowerRootNat e := by
          rw [pow_succ']
        _ = baseNat e.1 ^ eventParentDepth e *
              eventTowerRootNat e := by
          rw [hsucc]
    _ = (e.2 : ℕ) := eventParent_factorization e

/-- Canonical chart for every global Green event. -/
noncomputable def canonicalTowerChart (e : GreenEvent) : TowerChart e where
  tower := canonicalTowerEvent e
  code_eq := rfl
  current_eq := canonicalTowerEvent_current e
  parent_eq := canonicalTowerEvent_parent e
  grandparent_eq := canonicalTowerEvent_grandparent e
  hasGrandparent_iff := canonicalTowerEvent_hasGrandparent e

/-- Completeness is a theorem with an explicit witness, not a hypothesis. -/
theorem canonicalNormalizedTowerAtlasComplete :
    ∀ e : GreenEvent, Nonempty (TowerChart e) := by
  intro e
  exact ⟨canonicalTowerChart e⟩

/-- Every global event has a normalized tower representation, unconditionally. -/
theorem globalStencil_has_normalizedTowerTFVD
    (e : GreenEvent) (f : State) :
    ∃ c : TowerChart e,
      verticalGreenStencil e f = normalizedTowerTFVD c.tower f := by
  exact ⟨canonicalTowerChart e,
    verticalGreenStencil_eq_normalizedTowerTFVD_of_chart
      (canonicalTowerChart e) f⟩

/-- `ABGF-GR-003` with the canonical chart and no completeness hypothesis. -/
theorem verticalGreenStencil_eq_canonicalNormalizedTowerTFVD
    (e : GreenEvent) (f : State) :
    verticalGreenStencil e f =
      normalizedTowerTFVD (canonicalTowerEvent e) f :=
  verticalGreenStencil_eq_normalizedTowerTFVD_of_chart
    (canonicalTowerChart e) f

/-- Weighted global-coordinate version of the canonical tower identity. -/
theorem greenCoordinate_eq_canonicalNormalizedTowerTFVD
    (omega : AdmissibleInfinitePartition) (e : GreenEvent) (f : State) :
    greenCoordinate omega e f =
      ((greenAmplitude omega e : ℝ) : ℂ) *
        normalizedTowerTFVD (canonicalTowerEvent e) f :=
  greenCoordinate_eq_normalizedTowerTFVD_of_chart
    omega (canonicalTowerChart e) f

/-- The canonical tower formula really loses its third term at depth one. -/
theorem canonicalNormalizedTowerTFVD_depth_one
    (e : GreenEvent) (hdepth : ¬ HasGrandparent e) (f : State) :
    normalizedTowerTFVD (canonicalTowerEvent e) f =
      f (eventNumber e) -
        (((2 * carryRatio e.1 : ℝ) : ℂ) * f e.2) := by
  have hnot : ¬ 2 ≤ (canonicalTowerEvent e).depth := by
    intro htwo
    exact hdepth ((canonicalTowerEvent_hasGrandparent e).mpr htwo)
  have hone : (canonicalTowerEvent e).depth = 1 := by
    have hpos := (canonicalTowerEvent e).depth_pos
    omega
  rw [normalizedTowerTFVD_depth_one _ hone,
    canonicalTowerEvent_current, canonicalTowerEvent_parent]; rfl

/-- Global two-term truncation, obtained through the canonical tower chart. -/
theorem verticalGreenStencil_depth_one_eq_canonicalTowerTruncation
    (e : GreenEvent) (hdepth : ¬ HasGrandparent e) (f : State) :
    verticalGreenStencil e f =
      f (eventNumber e) -
        (((2 * carryRatio e.1 : ℝ) : ℂ) * f e.2) := by
  rw [verticalGreenStencil_eq_canonicalNormalizedTowerTFVD]
  exact canonicalNormalizedTowerTFVD_depth_one e hdepth f

end GreenFrame.Concrete
