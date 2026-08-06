import GreenFrame.Analysis.NontrivialBulk

/-!
# Uniform finite-section bounds
-/

namespace GreenFrame

/-- Every finite section inherits the same scalar frame ledger. -/
theorem uniform_section_bounds {ι : Type*} (state residual green : ι → ℝ)
    (hlower : ∀ i, (1 / 2 : ℝ) * state i ≤ residual i)
    (hresidual : ∀ i, residual i ≤ state i)
    (hgreen_nonneg : ∀ i, 0 ≤ green i)
    (hgreen_upper : ∀ i, green i ≤ greenBoundConstant * state i) (i : ι) :
    (1 / 2 : ℝ) * state i ≤ fullEnergy (residual i) (green i) ∧
      fullEnergy (residual i) (green i) ≤ fullFrameBound * state i := by
  exact allBasesGreenAnalysis_bounds (hlower i) (hresidual i)
    (hgreen_nonneg i) (hgreen_upper i)

end GreenFrame
