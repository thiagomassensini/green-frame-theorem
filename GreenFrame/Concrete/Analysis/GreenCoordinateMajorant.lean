import GreenFrame.Concrete.Analysis.GreenCurrentBound
import GreenFrame.Concrete.Analysis.GreenParentBound
import GreenFrame.Concrete.Analysis.GreenGrandparentBound

/-!
# Pointwise assembly of the global Green majorant

This checkpoint performs only the algebra identifying the expanded
three-point stencil estimate with the sum of the current, parent, and
grandparent majorants.
-/

open scoped ENNReal lp

namespace GreenFrame.Concrete

/-- Sum of the three global majorants. -/
noncomputable def greenCoordinateMajorant
    (omega : AdmissibleInfinitePartition) (f : State) (e : GreenEvent) : ℝ :=
  currentGreenMajorant omega f e +
    parentGreenMajorant omega f e +
    grandparentGreenMajorant omega f e

theorem greenCoordinateMajorant_nonneg
    (omega : AdmissibleInfinitePartition) (f : State) (e : GreenEvent) :
    0 ≤ greenCoordinateMajorant omega f e := by
  exact add_nonneg
    (add_nonneg (currentGreenMajorant_nonneg omega f e)
      (parentGreenMajorant_nonneg omega f e))
    (grandparentGreenMajorant_nonneg omega f e)

/-- The pointwise stencil estimate is exactly dominated by the assembled majorant. -/
theorem greenCoordinate_normSq_le_majorant
    (omega : AdmissibleInfinitePartition) (f : State) (e : GreenEvent) :
    Complex.normSq (greenCoordinate omega e f) ≤
      greenCoordinateMajorant omega f e := by
  have hq4 : carryRatio e.1 ^ 4 = (baseReal e.1)⁻¹ ^ 2 := by
    calc
      carryRatio e.1 ^ 4 = (carryRatio e.1 ^ 2) ^ 2 := by ring
      _ = (baseReal e.1)⁻¹ ^ 2 := by rw [carryRatio_sq]
  calc
    Complex.normSq (greenCoordinate omega e f) ≤
        3 * (omega.weight e.1 (eventNumber e) / baseReal e.1) *
          (stateEnergy f (eventNumber e) +
            4 * carryRatio e.1 ^ 2 * stateEnergy f e.2 +
            if HasGrandparent e then
              carryRatio e.1 ^ 4 * stateEnergy f (grandparentIndex e)
            else 0) := by
      simpa only [stateEnergy] using greenCoordinate_normSq_le_explicit omega e f
    _ = greenCoordinateMajorant omega f e := by
      by_cases h : HasGrandparent e
      · simp only [greenCoordinateMajorant, currentGreenMajorant,
          currentCameraMajorant, parentGreenMajorant, grandparentGreenMajorant,
          h, ↓reduceIte, carryRatio_sq, hq4]
        field_simp [inv_pow, ne_of_gt (baseReal_pos e.1)]
        ring
      · simp only [greenCoordinateMajorant, currentGreenMajorant,
          currentCameraMajorant, parentGreenMajorant, grandparentGreenMajorant,
          h, ↓reduceIte, carryRatio_sq]
        field_simp [inv_pow, ne_of_gt (baseReal_pos e.1)]
        ring

end GreenFrame.Concrete
