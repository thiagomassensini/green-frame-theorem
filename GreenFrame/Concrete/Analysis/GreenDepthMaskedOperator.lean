import GreenFrame.Concrete.Analysis.GreenDepthMaskedEnergy

/-!
# Canonical Green depth split: zero-padded operators

This checkpoint completes the ambient zero-padded bounded-operator packaging.
-/

noncomputable section

open scoped ENNReal lp

namespace GreenFrame.Concrete

/-- Explicit Bessel bound for the paper bulk sector. -/
theorem greenBulkAnalysis_norm_sq_le
    (omega : AdmissibleInfinitePartition) (f : State) :
    ‖greenBulkAnalysis omega f‖ ^ 2 ≤
      greenBesselConstant * ‖f‖ ^ 2 :=
  (greenBulkAnalysis_norm_sq_le_green omega f).trans
    (greenAnalysis_norm_sq_le omega f)

/-- `G₁` is additive. -/
theorem greenDepthOneAnalysis_add
    (omega : AdmissibleInfinitePartition) (f g : State) :
    greenDepthOneAnalysis omega (f + g) =
      greenDepthOneAnalysis omega f + greenDepthOneAnalysis omega g := by
  apply lp.ext
  funext e
  by_cases h : HasGrandparent e <;>
    simp [greenDepthOneAnalysis_apply, greenDepthOneCoordinate, h,
      greenCoordinate_add]

/-- `G₁` is complex homogeneous. -/
theorem greenDepthOneAnalysis_smul
    (omega : AdmissibleInfinitePartition) (c : ℂ) (f : State) :
    greenDepthOneAnalysis omega (c • f) =
      c • greenDepthOneAnalysis omega f := by
  apply lp.ext
  funext e
  by_cases h : HasGrandparent e <;>
    simp [greenDepthOneAnalysis_apply, greenDepthOneCoordinate, h,
      greenCoordinate_smul]

/-- `G≥2` is additive. -/
theorem greenBulkAnalysis_add
    (omega : AdmissibleInfinitePartition) (f g : State) :
    greenBulkAnalysis omega (f + g) =
      greenBulkAnalysis omega f + greenBulkAnalysis omega g := by
  apply lp.ext
  funext e
  by_cases h : HasGrandparent e <;>
    simp [greenBulkAnalysis_apply, greenBulkCoordinate, h,
      greenCoordinate_add]

/-- `G≥2` is complex homogeneous. -/
theorem greenBulkAnalysis_smul
    (omega : AdmissibleInfinitePartition) (c : ℂ) (f : State) :
    greenBulkAnalysis omega (c • f) = c • greenBulkAnalysis omega f := by
  apply lp.ext
  funext e
  by_cases h : HasGrandparent e <;>
    simp [greenBulkAnalysis_apply, greenBulkCoordinate, h,
      greenCoordinate_smul]

/-- Linear depth-one Green analysis. -/
noncomputable def greenDepthOneAnalysisLinearMap
    (omega : AdmissibleInfinitePartition) :
    State →ₗ[ℂ] ℓ²(GreenEvent, ℂ) where
  toFun := greenDepthOneAnalysis omega
  map_add' := greenDepthOneAnalysis_add omega
  map_smul' := greenDepthOneAnalysis_smul omega

/-- Linear paper-bulk Green analysis. -/
noncomputable def greenBulkAnalysisLinearMap
    (omega : AdmissibleInfinitePartition) :
    State →ₗ[ℂ] ℓ²(GreenEvent, ℂ) where
  toFun := greenBulkAnalysis omega
  map_add' := greenBulkAnalysis_add omega
  map_smul' := greenBulkAnalysis_smul omega

/-- Norm-form depth-one bound used for continuous packaging. -/
theorem greenDepthOneAnalysis_norm_le
    (omega : AdmissibleInfinitePartition) (f : State) :
    ‖greenDepthOneAnalysis omega f‖ ≤
      Real.sqrt greenBesselConstant * ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  calc
    ‖greenDepthOneAnalysis omega f‖ ^ 2 ≤
        greenBesselConstant * ‖f‖ ^ 2 :=
      greenDepthOneAnalysis_norm_sq_le omega f
    _ = (Real.sqrt greenBesselConstant * ‖f‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt greenBesselConstant_nonneg]

/-- Norm-form bulk bound used for continuous packaging. -/
theorem greenBulkAnalysis_norm_le
    (omega : AdmissibleInfinitePartition) (f : State) :
    ‖greenBulkAnalysis omega f‖ ≤
      Real.sqrt greenBesselConstant * ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  calc
    ‖greenBulkAnalysis omega f‖ ^ 2 ≤
        greenBesselConstant * ‖f‖ ^ 2 :=
      greenBulkAnalysis_norm_sq_le omega f
    _ = (Real.sqrt greenBesselConstant * ‖f‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt greenBesselConstant_nonneg]

/-- Bounded depth-one Green analysis operator. -/
noncomputable def greenDepthOneAnalysisOperator
    (omega : AdmissibleInfinitePartition) :
    State →L[ℂ] ℓ²(GreenEvent, ℂ) :=
  (greenDepthOneAnalysisLinearMap omega).mkContinuous
    (Real.sqrt greenBesselConstant) (greenDepthOneAnalysis_norm_le omega)

/-- Bounded depth-at-least-two paper-bulk operator. -/
noncomputable def greenBulkAnalysisOperator
    (omega : AdmissibleInfinitePartition) :
    State →L[ℂ] ℓ²(GreenEvent, ℂ) :=
  (greenBulkAnalysisLinearMap omega).mkContinuous
    (Real.sqrt greenBesselConstant) (greenBulkAnalysis_norm_le omega)

@[simp]
theorem greenDepthOneAnalysisOperator_apply
    (omega : AdmissibleInfinitePartition) (f : State) :
    greenDepthOneAnalysisOperator omega f = greenDepthOneAnalysis omega f :=
  rfl

end GreenFrame.Concrete
