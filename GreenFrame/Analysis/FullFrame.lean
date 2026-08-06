import GreenFrame.Analysis.GreenBounds

/-!
# Scalar frame ledger

The operator proof reduces to a lower/upper ledger for the residual-seed
energy and the Green energy. This module records that reduction exactly.
-/

namespace GreenFrame

/-- Conservative Green bound used by the kernel certificate. -/
def greenBoundConstant : ℝ := 12

/-- Corresponding universal full-frame upper bound. -/
def fullFrameBound : ℝ := 13

/-- Full analysis energy is the orthogonal sum of residual-seed and Green energies. -/
def fullEnergy (residualSeed green : ℝ) : ℝ := residualSeed + green

/-- The residual-seed ledger itself lies between half and all of the state energy. -/
theorem residual_seed_norm_sq_bounds {state residualSeed : ℝ}
    (hlower : (1 / 2 : ℝ) * state ≤ residualSeed)
    (hupper : residualSeed ≤ state) :
    (1 / 2 : ℝ) * state ≤ residualSeed ∧ residualSeed ≤ state :=
  ⟨hlower, hupper⟩

/-- The full analysis inherits the residual lower frame bound. -/
theorem fullEnergy_lower {state residualSeed green : ℝ}
    (hlower : (1 / 2 : ℝ) * state ≤ residualSeed)
    (hgreen : 0 ≤ green) :
    (1 / 2 : ℝ) * state ≤ fullEnergy residualSeed green := by
  dsimp [fullEnergy]
  linarith

/-- The full analysis inherits a universal upper frame bound. -/
theorem fullEnergy_upper {state residualSeed green : ℝ}
    (hresidual : residualSeed ≤ state)
    (hgreen : green ≤ greenBoundConstant * state) :
    fullEnergy residualSeed green ≤ fullFrameBound * state := by
  norm_num [fullEnergy, greenBoundConstant, fullFrameBound] at *
  linarith

/-- The two estimates combine into the All-Bases Green frame inequality. -/
theorem allBasesGreenAnalysis_bounds {state residualSeed green : ℝ}
    (hlower : (1 / 2 : ℝ) * state ≤ residualSeed)
    (hresidual : residualSeed ≤ state)
    (hgreen_nonneg : 0 ≤ green)
    (hgreen_upper : green ≤ greenBoundConstant * state) :
    (1 / 2 : ℝ) * state ≤ fullEnergy residualSeed green ∧
      fullEnergy residualSeed green ≤ fullFrameBound * state := by
  exact ⟨fullEnergy_lower hlower hgreen_nonneg,
    fullEnergy_upper hresidual hgreen_upper⟩

end GreenFrame
