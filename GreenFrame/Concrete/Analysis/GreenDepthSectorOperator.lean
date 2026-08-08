import GreenFrame.Concrete.Analysis.GreenDepthSectorEnergy

/-!
# Canonical Green depth split: literal sector operators

This checkpoint completes the literal subtype-indexed bounded operators.
-/

noncomputable section

open scoped ENNReal lp

namespace GreenFrame.Concrete

/-- The literal bulk restriction inherits the global Green bound. -/
theorem greenBulkSectorAnalysis_norm_sq_le
    (omega : AdmissibleInfinitePartition) (f : State) :
    ‖greenBulkSectorAnalysis omega f‖ ^ 2 ≤
      greenBesselConstant * ‖f‖ ^ 2 := by
  calc
    ‖greenBulkSectorAnalysis omega f‖ ^ 2 ≤
        ‖greenDepthOneSectorAnalysis omega f‖ ^ 2 +
          ‖greenBulkSectorAnalysis omega f‖ ^ 2 :=
      le_add_of_nonneg_left (sq_nonneg _)
    _ = ‖greenAnalysis omega f‖ ^ 2 :=
      (greenAnalysis_norm_sq_eq_depthOneSector_add_bulkSector omega f).symm
    _ ≤ greenBesselConstant * ‖f‖ ^ 2 :=
      greenAnalysis_norm_sq_le omega f

theorem greenDepthOneSectorAnalysis_add
    (omega : AdmissibleInfinitePartition) (f g : State) :
    greenDepthOneSectorAnalysis omega (f + g) =
      greenDepthOneSectorAnalysis omega f +
        greenDepthOneSectorAnalysis omega g := by
  apply lp.ext
  funext e
  exact greenCoordinate_add omega e.1 f g

theorem greenDepthOneSectorAnalysis_smul
    (omega : AdmissibleInfinitePartition) (c : ℂ) (f : State) :
    greenDepthOneSectorAnalysis omega (c • f) =
      c • greenDepthOneSectorAnalysis omega f := by
  apply lp.ext
  funext e
  exact greenCoordinate_smul omega e.1 c f

theorem greenBulkSectorAnalysis_add
    (omega : AdmissibleInfinitePartition) (f g : State) :
    greenBulkSectorAnalysis omega (f + g) =
      greenBulkSectorAnalysis omega f + greenBulkSectorAnalysis omega g := by
  apply lp.ext
  funext e
  exact greenCoordinate_add omega e.1 f g

theorem greenBulkSectorAnalysis_smul
    (omega : AdmissibleInfinitePartition) (c : ℂ) (f : State) :
    greenBulkSectorAnalysis omega (c • f) =
      c • greenBulkSectorAnalysis omega f := by
  apply lp.ext
  funext e
  exact greenCoordinate_smul omega e.1 c f

noncomputable def greenDepthOneSectorAnalysisLinearMap
    (omega : AdmissibleInfinitePartition) :
    State →ₗ[ℂ] DepthOneGreenSpace where
  toFun := greenDepthOneSectorAnalysis omega
  map_add' := greenDepthOneSectorAnalysis_add omega
  map_smul' := greenDepthOneSectorAnalysis_smul omega

noncomputable def greenBulkSectorAnalysisLinearMap
    (omega : AdmissibleInfinitePartition) :
    State →ₗ[ℂ] BulkGreenSpace where
  toFun := greenBulkSectorAnalysis omega
  map_add' := greenBulkSectorAnalysis_add omega
  map_smul' := greenBulkSectorAnalysis_smul omega

theorem greenDepthOneSectorAnalysis_norm_le
    (omega : AdmissibleInfinitePartition) (f : State) :
    ‖greenDepthOneSectorAnalysis omega f‖ ≤
      Real.sqrt greenBesselConstant * ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  calc
    ‖greenDepthOneSectorAnalysis omega f‖ ^ 2 ≤
        greenBesselConstant * ‖f‖ ^ 2 :=
      greenDepthOneSectorAnalysis_norm_sq_le omega f
    _ = (Real.sqrt greenBesselConstant * ‖f‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt greenBesselConstant_nonneg]

theorem greenBulkSectorAnalysis_norm_le
    (omega : AdmissibleInfinitePartition) (f : State) :
    ‖greenBulkSectorAnalysis omega f‖ ≤
      Real.sqrt greenBesselConstant * ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  calc
    ‖greenBulkSectorAnalysis omega f‖ ^ 2 ≤
        greenBesselConstant * ‖f‖ ^ 2 :=
      greenBulkSectorAnalysis_norm_sq_le omega f
    _ = (Real.sqrt greenBesselConstant * ‖f‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt greenBesselConstant_nonneg]

noncomputable def greenDepthOneSectorAnalysisOperator
    (omega : AdmissibleInfinitePartition) :
    State →L[ℂ] DepthOneGreenSpace :=
  (greenDepthOneSectorAnalysisLinearMap omega).mkContinuous
    (Real.sqrt greenBesselConstant)
      (greenDepthOneSectorAnalysis_norm_le omega)

noncomputable def greenBulkSectorAnalysisOperator
    (omega : AdmissibleInfinitePartition) :
    State →L[ℂ] BulkGreenSpace :=
  (greenBulkSectorAnalysisLinearMap omega).mkContinuous
    (Real.sqrt greenBesselConstant) (greenBulkSectorAnalysis_norm_le omega)

@[simp]
theorem greenDepthOneSectorAnalysisOperator_apply
    (omega : AdmissibleInfinitePartition) (f : State) :
    greenDepthOneSectorAnalysisOperator omega f =
      greenDepthOneSectorAnalysis omega f :=
  rfl

@[simp]
theorem greenBulkSectorAnalysisOperator_apply
    (omega : AdmissibleInfinitePartition) (f : State) :
    greenBulkSectorAnalysisOperator omega f = greenBulkSectorAnalysis omega f :=
  rfl

end GreenFrame.Concrete
