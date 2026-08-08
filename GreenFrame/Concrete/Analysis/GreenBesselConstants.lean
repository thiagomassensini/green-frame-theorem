import GreenFrame.Concrete.Analysis.GreenReindexing
import Mathlib.Analysis.PSeries

/-!
# Constants for the global Green estimate

This checkpoint proves convergence of the two coded-base series and defines
the explicit constant.  No state or global Green summation appears yet.
-/

open scoped ENNReal lp

namespace GreenFrame.Concrete

/-- The convergent coded-base `p`-series. -/
noncomputable def inverseBasePowerSum (k : ℕ) : ℝ :=
  ∑' r : ℕ, 1 / baseReal r ^ k

/-- `S₂ = ∑_{b≥2} b⁻²`, with `b = r + 2`. -/
noncomputable abbrev S₂ : ℝ := inverseBasePowerSum 2

/-- `S₃ = ∑_{b≥2} b⁻³`, with `b = r + 2`. -/
noncomputable abbrev S₃ : ℝ := inverseBasePowerSum 3

/-- Universal Green Bessel constant. -/
noncomputable def greenBesselConstant : ℝ :=
  (3 : ℝ) / 2 + 12 * S₂ + 3 * S₃

/-- Public expansion of the universal Green constant. -/
theorem greenBesselConstant_eq :
    greenBesselConstant = (3 : ℝ) / 2 + 12 * S₂ + 3 * S₃ :=
  rfl

/-- Every coded-base `p`-series with exponent above one is summable. -/
theorem inverseBasePower_summable {k : ℕ} (hk : 1 < k) :
    Summable (fun r : ℕ => 1 / baseReal r ^ k) := by
  have hfull : Summable (fun n : ℕ => 1 / (n : ℝ) ^ k) :=
    summable_one_div_nat_pow.mpr hk
  have hshift := (summable_nat_add_iff 2).mpr hfull
  simpa only [baseReal, baseNat, Nat.cast_add, Nat.cast_ofNat] using hshift

/-- The square-base series is summable. -/
theorem inverseBaseSquare_summable :
    Summable (fun r : ℕ => 1 / baseReal r ^ 2) :=
  inverseBasePower_summable (by omega)

/-- The cube-base series is summable. -/
theorem inverseBaseCube_summable :
    Summable (fun r : ℕ => 1 / baseReal r ^ 3) :=
  inverseBasePower_summable (by omega)

/-- `S₂` is nonnegative. -/
theorem S2_nonneg : 0 ≤ S₂ := by
  exact tsum_nonneg fun r => div_nonneg zero_le_one (pow_nonneg (baseReal_nonneg r) _)

/-- `S₃` is nonnegative. -/
theorem S3_nonneg : 0 ≤ S₃ := by
  exact tsum_nonneg fun r => div_nonneg zero_le_one (pow_nonneg (baseReal_nonneg r) _)

/-- The explicit Green constant is nonnegative. -/
theorem greenBesselConstant_nonneg : 0 ≤ greenBesselConstant := by
  dsimp only [greenBesselConstant]
  have h2 : 0 ≤ S₂ := S2_nonneg
  have h3 : 0 ≤ S₃ := S3_nonneg
  positivity

end GreenFrame.Concrete
