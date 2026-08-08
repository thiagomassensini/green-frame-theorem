import GreenFrame.Concrete.Analysis.ResidualAnalysis
import GreenFrame.Concrete.Analysis.GreenDepthSplit
import GreenFrame.Concrete.Analysis.ComplexFrameBounds

/-!
# Concrete paper split operators and exact energy identities

This checkpoint defines the literal paper split

* external = seed + residual + depth-one Green rows;
* bulk = depth-at-least-two Green rows,

and proves the exact orthogonal recombination identities used by the
quantitative bounds checkpoint.
-/

noncomputable section

open scoped ENNReal InnerProductSpace lp

namespace GreenFrame.Concrete

/-- Paper external coefficient space: seed-residual plus depth-one Green. -/
abbrev ConcreteExternalSpace :=
  HilbertSum SeedResidualSpace DepthOneGreenSpace

/-- Paper full coefficient space: external plus depth-at-least-two Green. -/
abbrev ConcreteAnalysisSpace :=
  HilbertSum ConcreteExternalSpace BulkGreenSpace

/-- Raw paper external analysis `(seed, residual, G₁)`. -/
noncomputable def concreteExternalAnalysisOperator
    (omega : AdmissibleInfinitePartition) :
    State →L[ℂ] ConcreteExternalSpace :=
  (WithLp.prodContinuousLinearEquiv
      2 ℂ SeedResidualSpace DepthOneGreenSpace).symm.toContinuousLinearMap.comp
    ((seedResidualAnalysisCLM omega).prod
      (greenDepthOneSectorAnalysisOperator omega))

@[simp]
theorem concreteExternalAnalysisOperator_apply
    (omega : AdmissibleInfinitePartition) (f : State) :
    concreteExternalAnalysisOperator omega f =
      WithLp.toLp 2
        (seedResidualAnalysis omega f,
          greenDepthOneSectorAnalysis omega f) := by
  rfl

/-- Complete concrete paper analysis `((seed,residual,G₁),G≥2)`. -/
noncomputable def concreteAnalysisOperator
    (omega : AdmissibleInfinitePartition) :
    State →L[ℂ] ConcreteAnalysisSpace :=
  (WithLp.prodContinuousLinearEquiv
      2 ℂ ConcreteExternalSpace BulkGreenSpace).symm.toContinuousLinearMap.comp
    ((concreteExternalAnalysisOperator omega).prod
      (greenBulkSectorAnalysisOperator omega))

/-- Pointwise formula for the exact paper split. -/
@[simp]
theorem concreteAnalysisOperator_apply
    (omega : AdmissibleInfinitePartition) (f : State) :
    concreteAnalysisOperator omega f =
      WithLp.toLp 2
        (concreteExternalAnalysisOperator omega f,
          greenBulkSectorAnalysis omega f) := by
  rfl

/-- The raw external projection is seed + residual + `G₁`. -/
@[simp]
theorem rawExternal_concreteAnalysisOperator_apply
    (omega : AdmissibleInfinitePartition) (f : State) :
    rawExternal (concreteAnalysisOperator omega) f =
      concreteExternalAnalysisOperator omega f := by
  simp only [rawExternal_apply, concreteAnalysisOperator_apply,
    WithLp.toLp_fst]

/-- The raw bulk projection is exactly `G≥2`, not the aggregate Green map. -/
@[simp]
theorem rawBulk_concreteAnalysisOperator_apply
    (omega : AdmissibleInfinitePartition) (f : State) :
    rawBulk (concreteAnalysisOperator omega) f =
      greenBulkSectorAnalysis omega f := by
  simp only [rawBulk_apply, concreteAnalysisOperator_apply,
    WithLp.toLp_snd]

/-- Orthogonal seed-residual/depth-one identity inside the external sector. -/
theorem concreteExternalAnalysisOperator_norm_sq_eq
    (omega : AdmissibleInfinitePartition) (f : State) :
    ‖concreteExternalAnalysisOperator omega f‖ ^ 2 =
      ‖seedResidualAnalysis omega f‖ ^ 2 +
        ‖greenDepthOneSectorAnalysis omega f‖ ^ 2 := by
  simpa only [concreteExternalAnalysisOperator_apply,
    WithLp.toLp_fst, WithLp.toLp_snd] using
    WithLp.prod_norm_sq_eq_of_L2
      (concreteExternalAnalysisOperator omega f)

/-- Exact Pythagorean identity for the paper external/bulk split. -/
theorem concreteAnalysisOperator_norm_sq_eq_external_add_bulk
    (omega : AdmissibleInfinitePartition) (f : State) :
    ‖concreteAnalysisOperator omega f‖ ^ 2 =
      ‖concreteExternalAnalysisOperator omega f‖ ^ 2 +
        ‖greenBulkSectorAnalysis omega f‖ ^ 2 := by
  simpa only [concreteAnalysisOperator_apply, WithLp.toLp_fst,
    WithLp.toLp_snd] using
    WithLp.prod_norm_sq_eq_of_L2 (concreteAnalysisOperator omega f)

/-- Recombining `G₁` and `G≥2` recovers the already certified global Green
energy exactly. -/
theorem concreteAnalysisOperator_norm_sq_eq_seedResidual_add_green
    (omega : AdmissibleInfinitePartition) (f : State) :
    ‖concreteAnalysisOperator omega f‖ ^ 2 =
      ‖seedResidualAnalysis omega f‖ ^ 2 +
        ‖greenAnalysis omega f‖ ^ 2 := by
  calc
    ‖concreteAnalysisOperator omega f‖ ^ 2 =
        ‖concreteExternalAnalysisOperator omega f‖ ^ 2 +
          ‖greenBulkSectorAnalysis omega f‖ ^ 2 :=
      concreteAnalysisOperator_norm_sq_eq_external_add_bulk omega f
    _ = (‖seedResidualAnalysis omega f‖ ^ 2 +
          ‖greenDepthOneSectorAnalysis omega f‖ ^ 2) +
          ‖greenBulkSectorAnalysis omega f‖ ^ 2 := by
      rw [concreteExternalAnalysisOperator_norm_sq_eq]
    _ = ‖seedResidualAnalysis omega f‖ ^ 2 +
          (‖greenDepthOneSectorAnalysis omega f‖ ^ 2 +
            ‖greenBulkSectorAnalysis omega f‖ ^ 2) := by ring
    _ = ‖seedResidualAnalysis omega f‖ ^ 2 +
          ‖greenAnalysis omega f‖ ^ 2 := by
      rw [greenAnalysis_norm_sq_eq_depthOneSector_add_bulkSector]

end GreenFrame.Concrete