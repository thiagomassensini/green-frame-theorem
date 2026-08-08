import GreenFrame.Concrete.Analysis.ConcreteBulkWitnessRaw
import GreenFrame.Concrete.Analysis.NontrivialPoisson

/-!
# CFC normalization and static Poisson transfer of the `(2,4)` witness

This final declaration-bearing checkpoint transports the raw bulk witness
through the positive CFC square root and records the exact normalized
operator lower bound and restricted-Poisson nontriviality.
-/

noncomputable section

open scoped ENNReal InnerProductSpace lp

namespace GreenFrame.Concrete

/-- Operator-level nontriviality of the exact raw paper bulk. -/
theorem canonicalCarry_rawBulk_ne_zero :
    rawBulk (concreteAnalysisOperator canonicalCarryInfinitePartition) ≠ 0 := by
  intro hzero
  apply canonicalCarry_rawBulk_twoFour_ne_zero
  rw [hzero]
  rfl

/-- The CFC-transferred `e₄` witness retains squared normalized bulk energy
at least `1/4`. -/
theorem canonicalCarry_normalizedBulk_twoFour_norm_sq_lower :
    (1 / 4 : ℝ) ≤
      ‖normalizedBulk
        (concreteAnalysisOperator canonicalCarryInfinitePartition)
        (sqrtFrame
          (concreteAnalysisOperator canonicalCarryInfinitePartition)
          twoFourWitnessState)‖ ^ 2 := by
  rw [normalizedBulk_sqrtFrame_apply
    (concreteSplitFrameBounds canonicalCarryInfinitePartition).toComplexFrameBounds
    twoFourWitnessState]
  exact canonicalCarry_rawBulk_twoFour_norm_sq_lower

/-- Quantitative paper claim `‖B₀‖² ≥ 1/(4 C_F)` with
`C_F = 1 + greenBesselConstant`. -/
theorem canonicalCarry_normalizedBulk_operator_norm_sq_lower :
    1 / (4 * (1 + greenBesselConstant)) ≤
      ‖normalizedBulk
        (concreteAnalysisOperator canonicalCarryInfinitePartition)‖ ^ 2 := by
  have h := normalizedBulk_opNorm_sq_lower_of_raw_witness
    (concreteSplitFrameBounds canonicalCarryInfinitePartition).toComplexFrameBounds
    twoFourWitnessState_norm
    canonicalCarry_rawBulk_twoFour_norm_sq_lower
  have hupper : 0 < 1 + greenBesselConstant :=
    add_pos_of_pos_of_nonneg (by norm_num) greenBesselConstant_nonneg
  calc
    1 / (4 * (1 + greenBesselConstant)) =
        (1 / 4 : ℝ) / (1 + greenBesselConstant) := by
      field_simp [hupper.ne']
    _ ≤ ‖normalizedBulk
        (concreteAnalysisOperator canonicalCarryInfinitePartition)‖ ^ 2 := by
      simpa only [concreteSplitFrameBounds_upper] using h

/-- The quantitative lower bound implies normalized paper-bulk
nontriviality. -/
theorem canonicalCarry_normalizedBulk_ne_zero :
    normalizedBulk
      (concreteAnalysisOperator canonicalCarryInfinitePartition) ≠ 0 := by
  intro hzero
  have h := canonicalCarry_normalizedBulk_operator_norm_sq_lower
  rw [hzero, norm_zero] at h
  have hupper : 0 < 1 + greenBesselConstant :=
    add_pos_of_pos_of_nonneg (by norm_num) greenBesselConstant_nonneg
  have hleft : 0 < 1 / (4 * (1 + greenBesselConstant)) := by positivity
  linarith

/-- End-to-end nontriviality of the restricted static Poisson operator for
the exact paper split. -/
theorem canonicalCarry_restrictedPoisson_ne_zero :
    restrictedPoisson
      (concreteSplitFrameBounds canonicalCarryInfinitePartition) ≠ 0 :=
  restrictedPoisson_ne_zero
    (concreteSplitFrameBounds canonicalCarryInfinitePartition)
    ⟨sqrtFrame
        (concreteAnalysisOperator canonicalCarryInfinitePartition)
        twoFourWitnessState,
      by
        intro hzero
        have h := canonicalCarry_normalizedBulk_twoFour_norm_sq_lower
        rw [hzero, norm_zero] at h
        norm_num at h⟩

end GreenFrame.Concrete
