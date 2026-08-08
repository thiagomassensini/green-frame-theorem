import GreenFrame.Concrete.Finite.ConcreteCoordinateCutoffMaps
import GreenFrame.Concrete.Finite.L2CoordinateMaskLimit

/-!
# Strong limits of every concrete coordinate cutoff

This checkpoint instantiates the generic Tannery tail lemma in the state,
residual, literal depth-one, literal bulk, and nested coefficient spaces.
-/

noncomputable section

open scoped ENNReal InnerProductSpace lp Topology
open Filter

namespace GreenFrame.Concrete

theorem stateCoordinateCutoff_tendsto (f : State) :
    Tendsto (fun N => stateCoordinateCutoff N f) atTop (nhds f) := by
  simpa only [stateCoordinateCutoff, l2CoordinateMaskCLM_apply] using
    l2CoordinateMask_tendsto
      (fun N n => stateIndexRetained N n)
      (fun n => by
        filter_upwards [eventually_ge_atTop (n : ℕ)] with N hN
        exact hN)
      f

theorem residualCoordinateCutoff_tendsto (y : ResidualSpace) :
    Tendsto (fun N => residualCoordinateCutoff N y) atTop (nhds y) := by
  simpa only [residualCoordinateCutoff, l2CoordinateMaskCLM_apply] using
    l2CoordinateMask_tendsto
      (fun N e => residualEventRetained N e)
      (fun e => by
        filter_upwards [eventually_ge_atTop
          (max (e.1 : ℕ) (baseNat e.2))] with N hN
        exact ⟨(le_max_left _ _).trans hN,
          (le_max_right _ _).trans hN⟩)
      y

theorem depthOneCoordinateCutoff_tendsto (y : DepthOneGreenSpace) :
    Tendsto (fun N => depthOneCoordinateCutoff N y) atTop (nhds y) := by
  simpa only [depthOneCoordinateCutoff, l2CoordinateMaskCLM_apply] using
    l2CoordinateMask_tendsto
      (fun N e => depthOneEventRetained N e)
      (fun e => by
        filter_upwards [eventually_ge_atTop
          (max (eventNumber e.1 : ℕ) (baseNat e.1.1))] with N hN
        exact ⟨(le_max_left _ _).trans hN,
          (le_max_right _ _).trans hN⟩)
      y

theorem bulkCoordinateCutoff_tendsto (y : BulkGreenSpace) :
    Tendsto (fun N => bulkCoordinateCutoff N y) atTop (nhds y) := by
  simpa only [bulkCoordinateCutoff, l2CoordinateMaskCLM_apply] using
    l2CoordinateMask_tendsto
      (fun N e => bulkEventRetained N e)
      (fun e => by
        filter_upwards [eventually_ge_atTop
          (max (eventNumber e.1 : ℕ) (baseNat e.1.1))] with N hN
        exact ⟨(le_max_left _ _).trans hN,
          (le_max_right _ _).trans hN⟩)
      y

theorem seedResidualCoordinateCutoff_tendsto (y : SeedResidualSpace) :
    Tendsto (fun N => seedResidualCoordinateCutoff N y) atTop (nhds y) := by
  exact l2ProductMap_tendsto
    (fun _ => ContinuousLinearMap.id ℂ ℂ)
    residualCoordinateCutoff
    (fun x => tendsto_const_nhds)
    residualCoordinateCutoff_tendsto y

theorem externalCoordinateCutoff_tendsto (y : ConcreteExternalSpace) :
    Tendsto (fun N => externalCoordinateCutoff N y) atTop (nhds y) := by
  exact l2ProductMap_tendsto
    seedResidualCoordinateCutoff depthOneCoordinateCutoff
    seedResidualCoordinateCutoff_tendsto
    depthOneCoordinateCutoff_tendsto y

theorem concreteCoefficientCutoff_tendsto (y : ConcreteAnalysisSpace) :
    Tendsto (fun N => concreteCoefficientCutoff N y) atTop (nhds y) := by
  exact l2ProductMap_tendsto
    externalCoordinateCutoff bulkCoordinateCutoff
    externalCoordinateCutoff_tendsto
    bulkCoordinateCutoff_tendsto y

end GreenFrame.Concrete
