import GreenFrame.Concrete.Analysis.ConcreteBulkWitnessCoordinates

/-!
# Raw paper-bulk lower bound for the canonical `(2,4)` witness

The selected coordinate belongs to the literal `G≥2` subtype.  This
checkpoint lifts its exact squared energy `1/4` first to the bulk sector and
then to the `rawBulk` interface.
-/

noncomputable section

open scoped ENNReal InnerProductSpace lp

namespace GreenFrame.Concrete

/-- Since the event has a grandparent, it is a literal `G≥2` sector row. -/
theorem canonicalCarry_twoFour_bulkCoordinate :
    greenBulkSectorAnalysis canonicalCarryInfinitePartition
      twoFourWitnessState twoFourBulkEvent = (1 / 2 : ℂ) := by
  rw [greenBulkSectorAnalysis_apply, twoFourBulkEvent_val,
    canonicalCarry_twoFour_greenCoordinate]

/-- Exact pointwise squared paper-bulk energy `1/4`. -/
theorem canonicalCarry_twoFour_bulkCoordinate_normSq :
    Complex.normSq
      (greenBulkSectorAnalysis canonicalCarryInfinitePartition
        twoFourWitnessState twoFourBulkEvent) = (1 / 4 : ℝ) := by
  rw [canonicalCarry_twoFour_bulkCoordinate]
  norm_num [Complex.normSq]

/-- The complete raw paper bulk carries at least the witness coordinate's
energy. -/
theorem canonicalCarry_greenBulkAnalysis_norm_sq_lower :
    (1 / 4 : ℝ) ≤
      ‖greenBulkSectorAnalysis canonicalCarryInfinitePartition
        twoFourWitnessState‖ ^ 2 := by
  rw [greenBulkSectorAnalysis_norm_sq_eq]
  have hs : Summable (fun e : BulkGreenEvent =>
      Complex.normSq
        (greenCoordinate canonicalCarryInfinitePartition e.1
          twoFourWitnessState)) := by
    exact (greenCoordinate_normSq_summable
      canonicalCarryInfinitePartition twoFourWitnessState).subtype
        {e : GreenEvent | HasGrandparent e}
  calc
    (1 / 4 : ℝ) =
        Complex.normSq
          (greenCoordinate canonicalCarryInfinitePartition
            twoFourBulkEvent.1 twoFourWitnessState) := by
      rw [twoFourBulkEvent_val, canonicalCarry_twoFour_greenCoordinate]
      norm_num [Complex.normSq]
    _ ≤ ∑' e : BulkGreenEvent,
        Complex.normSq
          (greenCoordinate canonicalCarryInfinitePartition e.1
            twoFourWitnessState) :=
      hs.le_tsum twoFourBulkEvent (fun e _ => Complex.normSq_nonneg _)

/-- Raw paper-bulk energy lower bound in the exact split interface. -/
theorem canonicalCarry_rawBulk_twoFour_norm_sq_lower :
    (1 / 4 : ℝ) ≤
      ‖rawBulk
        (concreteAnalysisOperator canonicalCarryInfinitePartition)
        twoFourWitnessState‖ ^ 2 := by
  simpa only [rawBulk_concreteAnalysisOperator_apply] using
    canonicalCarry_greenBulkAnalysis_norm_sq_lower

/-- The explicit `e₄` state gives a nonzero raw paper bulk. -/
theorem canonicalCarry_rawBulk_twoFour_ne_zero :
    rawBulk (concreteAnalysisOperator canonicalCarryInfinitePartition)
      twoFourWitnessState ≠ 0 := by
  intro hzero
  have h := canonicalCarry_rawBulk_twoFour_norm_sq_lower
  rw [hzero, norm_zero] at h
  norm_num at h

end GreenFrame.Concrete
