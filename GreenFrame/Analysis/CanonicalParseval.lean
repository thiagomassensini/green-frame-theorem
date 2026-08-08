import GreenFrame.Analysis.FrameOperator

/-!
# Canonical Parseval interface
-/

namespace GreenFrame

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- A normalized analysis is represented by a linear isometry. -/
abbrev NormalizedAnalysis := H →ₗᵢ[ℝ] K

/-- The canonical normalized analysis is an isometry. -/
theorem normalizedAnalysis_isometry (V : NormalizedAnalysis (H := H) (K := K)) :
    Isometry V :=
  V.isometry

/-- Parseval normalization preserves every state norm exactly. -/
theorem normalizedAnalysis_norm (V : NormalizedAnalysis (H := H) (K := K)) (x : H) :
    ‖V x‖ = ‖x‖ := by
  exact V.norm_map x

end GreenFrame
