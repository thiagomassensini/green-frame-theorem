import GreenFrame.Concrete.Analysis.GreenCoordinateMajorant

/-!
# Assembly of the global Green coordinate estimate

The already identified pointwise majorant is summed here.  This is the
checkpoint that proves the actual coordinate family is square summable and
derives the explicit constant
`C_G = 3/2 + 12*S₂ + 3*S₃`.
-/

open scoped ENNReal lp

namespace GreenFrame.Concrete

/-- The assembled majorant is summable. -/
theorem greenCoordinateMajorant_summable
    (omega : AdmissibleInfinitePartition) (f : State) :
    Summable (greenCoordinateMajorant omega f) :=
  ((currentGreenMajorant_summable omega f).add
    (parentGreenMajorant_summable omega f)).add
    (grandparentGreenMajorant_summable omega f)

/-- The actual Green coordinate family is square summable. -/
theorem greenCoordinate_normSq_summable
    (omega : AdmissibleInfinitePartition) (f : State) :
    Summable (fun e : GreenEvent => Complex.normSq (greenCoordinate omega e f)) :=
  Summable.of_nonneg_of_le
    (fun _e => Complex.normSq_nonneg _)
    (greenCoordinate_normSq_le_majorant omega f)
    (greenCoordinateMajorant_summable omega f)

/-- Global Bessel estimate at the level of coordinate-energy sums. -/
theorem greenCoordinate_tsum_normSq_le
    (omega : AdmissibleInfinitePartition) (f : State) :
    (∑' e : GreenEvent, Complex.normSq (greenCoordinate omega e f)) ≤
      greenBesselConstant * ‖f‖ ^ 2 := by
  calc
    (∑' e : GreenEvent, Complex.normSq (greenCoordinate omega e f)) ≤
        ∑' e : GreenEvent, greenCoordinateMajorant omega f e :=
      (greenCoordinate_normSq_summable omega f).tsum_le_tsum
        (greenCoordinate_normSq_le_majorant omega f)
        (greenCoordinateMajorant_summable omega f)
    _ = (∑' e : GreenEvent, currentGreenMajorant omega f e) +
          (∑' e : GreenEvent, parentGreenMajorant omega f e) +
          (∑' e : GreenEvent, grandparentGreenMajorant omega f e) := by
      simp only [greenCoordinateMajorant]
      rw [((currentGreenMajorant_summable omega f).add
          (parentGreenMajorant_summable omega f)).tsum_add
          (grandparentGreenMajorant_summable omega f),
        (currentGreenMajorant_summable omega f).tsum_add
          (parentGreenMajorant_summable omega f)]
    _ ≤ ((3 : ℝ) / 2 * ‖f‖ ^ 2) +
          (12 * S₂ * ‖f‖ ^ 2) +
          (3 * S₃ * ‖f‖ ^ 2) := by
      exact add_le_add
        (add_le_add
          (currentGreenMajorant_tsum_le omega f)
          (parentGreenMajorant_tsum_le omega f))
        (grandparentGreenMajorant_tsum_le omega f)
    _ = greenBesselConstant * ‖f‖ ^ 2 := by
      simp only [greenBesselConstant]
      ring

end GreenFrame.Concrete
