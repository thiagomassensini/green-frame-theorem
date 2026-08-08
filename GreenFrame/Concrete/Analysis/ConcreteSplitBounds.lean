import GreenFrame.Concrete.Analysis.ConcreteSplitOperators

/-!
# Concrete paper split bounds

This checkpoint derives the exact lower/upper ledger for the canonical split
and packages it as a `SplitComplexFrameBounds` certificate.  The global Green
coefficient occurs once because `G₁ ⊕ G≥2` is first recombined exactly.
-/

noncomputable section

open scoped ENNReal InnerProductSpace lp

namespace GreenFrame.Concrete

/-- The exact paper external sector remains bounded below by the conserved
seed-residual energy. -/
theorem concreteExternalAnalysisOperator_lower
    (omega : AdmissibleInfinitePartition) (f : State) :
    (1 / 2 : ℝ) * ‖f‖ ^ 2 ≤
      ‖concreteExternalAnalysisOperator omega f‖ ^ 2 := by
  calc
    (1 / 2 : ℝ) * ‖f‖ ^ 2 ≤
        ‖seedResidualAnalysis omega f‖ ^ 2 :=
      (seedResidualAnalysis_norm_sq_bounds omega f).1
    _ ≤ ‖seedResidualAnalysis omega f‖ ^ 2 +
        ‖greenDepthOneSectorAnalysis omega f‖ ^ 2 :=
      le_add_of_nonneg_right (sq_nonneg _)
    _ = ‖concreteExternalAnalysisOperator omega f‖ ^ 2 :=
      (concreteExternalAnalysisOperator_norm_sq_eq omega f).symm

/-- The paper bulk inherits the global Green Bessel upper bound. -/
theorem concreteBulkAnalysisOperator_upper
    (omega : AdmissibleInfinitePartition) (f : State) :
    ‖rawBulk (concreteAnalysisOperator omega) f‖ ^ 2 ≤
      greenBesselConstant * ‖f‖ ^ 2 := by
  simpa only [rawBulk_concreteAnalysisOperator_apply] using
    greenBulkSectorAnalysis_norm_sq_le omega f

/-- Full concrete paper analysis with the sharp ledger `1/2` and
`1 + greenBesselConstant`. -/
theorem concreteAnalysisOperator_norm_sq_bounds
    (omega : AdmissibleInfinitePartition) (f : State) :
    (1 / 2 : ℝ) * ‖f‖ ^ 2 ≤
        ‖concreteAnalysisOperator omega f‖ ^ 2 ∧
      ‖concreteAnalysisOperator omega f‖ ^ 2 ≤
        (1 + greenBesselConstant) * ‖f‖ ^ 2 := by
  constructor
  · calc
      (1 / 2 : ℝ) * ‖f‖ ^ 2 ≤
          ‖concreteExternalAnalysisOperator omega f‖ ^ 2 :=
        concreteExternalAnalysisOperator_lower omega f
      _ ≤ ‖concreteExternalAnalysisOperator omega f‖ ^ 2 +
          ‖greenBulkSectorAnalysis omega f‖ ^ 2 :=
        le_add_of_nonneg_right (sq_nonneg _)
      _ = ‖concreteAnalysisOperator omega f‖ ^ 2 :=
        (concreteAnalysisOperator_norm_sq_eq_external_add_bulk omega f).symm
  · rw [concreteAnalysisOperator_norm_sq_eq_seedResidual_add_green]
    calc
      ‖seedResidualAnalysis omega f‖ ^ 2 +
          ‖greenAnalysis omega f‖ ^ 2 ≤
          ‖f‖ ^ 2 + greenBesselConstant * ‖f‖ ^ 2 :=
        add_le_add (seedResidualAnalysis_norm_sq_bounds omega f).2
          (greenAnalysis_norm_sq_le omega f)
      _ = (1 + greenBesselConstant) * ‖f‖ ^ 2 := by ring

/-- Concrete split-frame certificate for the exact paper split.  Unlike the
component-sum helper, this constructor uses the `G₁ ⊕ G≥2 = G` identity and
therefore does not duplicate the global Green bound. -/
noncomputable def concreteSplitFrameBounds
    (omega : AdmissibleInfinitePartition) :
    SplitComplexFrameBounds (concreteAnalysisOperator omega) where
  lower := (1 / 2 : ℝ)
  upper := 1 + greenBesselConstant
  lower_pos := by norm_num
  upper_pos := add_pos_of_pos_of_nonneg (by norm_num)
    greenBesselConstant_nonneg
  lower_norm_sq := fun f =>
    (concreteAnalysisOperator_norm_sq_bounds omega f).1
  upper_norm_sq := fun f =>
    (concreteAnalysisOperator_norm_sq_bounds omega f).2
  externalLower := (1 / 2 : ℝ)
  externalLower_pos := by norm_num
  external_lower_norm_sq := fun f => by
    simpa only [rawExternal_concreteAnalysisOperator_apply] using
      concreteExternalAnalysisOperator_lower omega f

/-- The concrete lower bound is exactly one half. -/
@[simp]
theorem concreteSplitFrameBounds_lower
    (omega : AdmissibleInfinitePartition) :
    (concreteSplitFrameBounds omega).lower = (1 / 2 : ℝ) :=
  rfl

/-- The exact full upper bound is not doubled by the row split. -/
@[simp]
theorem concreteSplitFrameBounds_upper
    (omega : AdmissibleInfinitePartition) :
    (concreteSplitFrameBounds omega).upper =
      1 + greenBesselConstant :=
  rfl

/-- The independent external lower ledger is one half. -/
@[simp]
theorem concreteSplitFrameBounds_externalLower
    (omega : AdmissibleInfinitePartition) :
    (concreteSplitFrameBounds omega).externalLower = (1 / 2 : ℝ) :=
  rfl

end GreenFrame.Concrete