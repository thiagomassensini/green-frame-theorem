import GreenFrame.Concrete.Finite.CoordinateCutoffs
import GreenFrame.Concrete.Finite.L2ProductCutoff

/-!
# Concrete finite coordinate-cutoff maps

This checkpoint packages every literal finite mask, the nested coefficient
cutoff, and the seed-residual projection used in `ABGF-FS-001`.
-/

noncomputable section

open scoped ENNReal InnerProductSpace lp

namespace GreenFrame.Concrete

noncomputable def stateCoordinateCutoff (N : ℕ) : State →L[ℂ] State :=
  l2CoordinateMaskCLM (stateIndexRetained N)

noncomputable def residualCoordinateCutoff (N : ℕ) :
    ResidualSpace →L[ℂ] ResidualSpace :=
  l2CoordinateMaskCLM (residualEventRetained N)

noncomputable def depthOneCoordinateCutoff (N : ℕ) :
    DepthOneGreenSpace →L[ℂ] DepthOneGreenSpace :=
  l2CoordinateMaskCLM (depthOneEventRetained N)

noncomputable def bulkCoordinateCutoff (N : ℕ) :
    BulkGreenSpace →L[ℂ] BulkGreenSpace :=
  l2CoordinateMaskCLM (bulkEventRetained N)

noncomputable def seedResidualCoordinateCutoff (N : ℕ) :
    SeedResidualSpace →L[ℂ] SeedResidualSpace :=
  l2ProductMap (ContinuousLinearMap.id ℂ ℂ) (residualCoordinateCutoff N)

noncomputable def externalCoordinateCutoff (N : ℕ) :
    ConcreteExternalSpace →L[ℂ] ConcreteExternalSpace :=
  l2ProductMap (seedResidualCoordinateCutoff N) (depthOneCoordinateCutoff N)

noncomputable def concreteCoefficientCutoff (N : ℕ) :
    ConcreteAnalysisSpace →L[ℂ] ConcreteAnalysisSpace :=
  l2ProductMap (externalCoordinateCutoff N) (bulkCoordinateCutoff N)

/-- Projection from the full paper codomain onto seed plus residual. -/
noncomputable def concreteSeedResidualProjection :
    ConcreteAnalysisSpace →L[ℂ] SeedResidualSpace :=
  (l2FirstProjection (E := SeedResidualSpace) (B := DepthOneGreenSpace)).comp
    (l2FirstProjection (E := ConcreteExternalSpace) (B := BulkGreenSpace))

theorem stateCoordinateCutoff_contracts (N : ℕ) (f : State) :
    ‖stateCoordinateCutoff N f‖ ≤ ‖f‖ :=
  l2CoordinateMask_norm_le (stateIndexRetained N) f

theorem concreteCoefficientCutoff_contracts
    (N : ℕ) (y : ConcreteAnalysisSpace) :
    ‖concreteCoefficientCutoff N y‖ ≤ ‖y‖ := by
  apply l2ProductMap_norm_le
  · intro z
    apply l2ProductMap_norm_le
    · intro w
      exact l2ProductMap_norm_le _ _
        (fun x => le_rfl)
        (fun x => l2CoordinateMask_norm_le _ x) w
    · intro x
      exact l2CoordinateMask_norm_le _ x
  · intro x
    exact l2CoordinateMask_norm_le _ x

theorem concreteSeedResidualProjection_contracts
    (y : ConcreteAnalysisSpace) :
    ‖concreteSeedResidualProjection y‖ ≤ ‖y‖ := by
  exact (l2FirstProjection_norm_le
    ((l2FirstProjection (E := ConcreteExternalSpace)
      (B := BulkGreenSpace)) y)).trans
    (l2FirstProjection_norm_le y)

theorem stateCoordinateCutoff_idempotent (N : ℕ) :
    (stateCoordinateCutoff N).comp (stateCoordinateCutoff N) =
      stateCoordinateCutoff N :=
  l2CoordinateMask_idempotent (stateIndexRetained N)

theorem concreteCoefficientCutoff_idempotent (N : ℕ) :
    (concreteCoefficientCutoff N).comp (concreteCoefficientCutoff N) =
      concreteCoefficientCutoff N := by
  apply l2ProductMap_idempotent
  · apply l2ProductMap_idempotent
    · apply l2ProductMap_idempotent
      · rfl
      · exact l2CoordinateMask_idempotent (residualEventRetained N)
    · exact l2CoordinateMask_idempotent (depthOneEventRetained N)
  · exact l2CoordinateMask_idempotent (bulkEventRetained N)

end GreenFrame.Concrete
