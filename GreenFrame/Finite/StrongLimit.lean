import GreenFrame.Finite.Sections

/-!
# Closed transport of uniform bounds to a limit
-/

namespace GreenFrame

open Filter Topology

/-- A convergent sequence in a fixed closed interval has its limit in that interval. -/
theorem strong_limit_preserves_bounds {u : ℕ → ℝ} {limit lower upper : ℝ}
    (hu : ∀ n, lower ≤ u n ∧ u n ≤ upper)
    (hlim : Tendsto u atTop (𝓝 limit)) :
    lower ≤ limit ∧ limit ≤ upper := by
  have hevent : ∀ᶠ n in atTop, u n ∈ Set.Icc lower upper :=
    Filter.Eventually.of_forall hu
  exact isClosed_Icc.mem_of_tendsto hlim hevent

end GreenFrame
