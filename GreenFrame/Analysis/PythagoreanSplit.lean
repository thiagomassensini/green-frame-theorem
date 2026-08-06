import GreenFrame.Arithmetic.CarryWitness

/-!
# Pythagorean Green-return split
-/

namespace GreenFrame

/-- Mass transmitted through the Green channel. -/
noncomputable def greenMass (weight base : ℝ) : ℝ := weight / base

/-- Mass retained in the orthogonal residual/return channel. -/
noncomputable def residualMass (weight base : ℝ) : ℝ := weight * (1 - 1 / base)

/-- Green mass is nonnegative for a nonnegative weight and positive base. -/
theorem greenMass_nonneg {weight base : ℝ} (hw : 0 ≤ weight) (hb : 0 < base) :
    0 ≤ greenMass weight base := by
  exact div_nonneg hw hb.le

/-- Residual mass is nonnegative for every positional base `base ≥ 2`. -/
theorem residualMass_nonneg {weight base : ℝ} (hw : 0 ≤ weight) (hb : 2 ≤ base) :
    0 ≤ residualMass weight base := by
  have hbpos : 0 < base := by linarith
  have hone : 1 / base ≤ 1 := by
    rw [div_le_iff₀ hbpos]
    nlinarith
  exact mul_nonneg hw (sub_nonneg.mpr hone)

/-- The Green and residual channels conserve the complete camera mass. -/
theorem green_residual_split {weight base : ℝ} (hb : base ≠ 0) :
    greenMass weight base + residualMass weight base = weight := by
  field_simp [greenMass, residualMass, hb]
  ring

/-- At least half of every camera weight remains in the residual channel. -/
theorem residualMass_ge_half_weight {weight base : ℝ}
    (hw : 0 ≤ weight) (hb : 2 ≤ base) :
    (1 / 2 : ℝ) * weight ≤ residualMass weight base := by
  have hbpos : 0 < base := by linarith
  have hdiv : 1 / base ≤ (1 / 2 : ℝ) := by
    rw [div_le_iff₀ hbpos]
    nlinarith
  have hfactor : (1 / 2 : ℝ) ≤ 1 - 1 / base := by
    linarith
  simpa [residualMass, mul_comm, mul_left_comm, mul_assoc] using
    (mul_le_mul_of_nonneg_left hfactor hw)

/-- At most half of every camera weight is sent through Green. -/
theorem greenMass_le_half_weight {weight base : ℝ}
    (hw : 0 ≤ weight) (hb : 2 ≤ base) :
    greenMass weight base ≤ (1 / 2 : ℝ) * weight := by
  have hbpos : 0 < base := by linarith
  have hdiv : 1 / base ≤ (1 / 2 : ℝ) := by
    rw [div_le_iff₀ hbpos]
    nlinarith
  simpa [greenMass, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    (mul_le_mul_of_nonneg_left hdiv hw)

end GreenFrame
