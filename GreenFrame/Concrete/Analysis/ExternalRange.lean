import GreenFrame.Concrete.Analysis.NormalizedSplit
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Closed normalized external range
-/

noncomputable section

open scoped InnerProductSpace NNReal

namespace GreenFrame.Concrete

variable {H E B : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]

/-- Reciprocal square-root constant used by the anti-Lipschitz estimate. -/
def inverseSqrtAntiConstant (a : ℝ) : ℝ≥0 :=
  ⟨(√a)⁻¹, inv_nonneg.mpr (Real.sqrt_nonneg a)⟩

/-- A positive lower norm-square estimate gives an anti-Lipschitz map. -/
omit [CompleteSpace H] [CompleteSpace E] in
theorem antilipschitz_of_norm_sq_lower
    {S : H →L[ℂ] E} {a : ℝ} (ha : 0 < a)
    (h : ∀ x, a * ‖x‖ ^ 2 ≤ ‖S x‖ ^ 2) :
    AntilipschitzWith (inverseSqrtAntiConstant a) S := by
  refine S.antilipschitz_of_bound
    (K := inverseSqrtAntiConstant a) ?_
  intro x
  change ‖x‖ ≤ (√a)⁻¹ * ‖S x‖
  rw [inv_mul_eq_div, le_div_iff₀ (Real.sqrt_pos.2 ha)]
  apply (sq_le_sq₀ (mul_nonneg (norm_nonneg x) (Real.sqrt_nonneg a))
    (norm_nonneg (S x))).mp
  rw [mul_pow, Real.sq_sqrt ha.le]
  simpa only [mul_comm] using h x

/-- Concrete anti-Lipschitz estimate for the normalized external analysis. -/
theorem normalizedExternal_antilipschitz
    {T : H →L[ℂ] HilbertSum E B}
    (bounds : SplitComplexFrameBounds T) :
    AntilipschitzWith
      (inverseSqrtAntiConstant (normalizedExternalLower bounds))
      (normalizedExternal T) :=
  antilipschitz_of_norm_sq_lower
    (normalizedExternalLower_pos bounds)
    (normalizedExternal_lower_norm_sq bounds)

theorem normalizedExternal_injective
    {T : H →L[ℂ] HilbertSum E B}
    (bounds : SplitComplexFrameBounds T) :
    Function.Injective (normalizedExternal T) :=
  (normalizedExternal_antilipschitz bounds).injective

/-- Closedness is derived, not stored in a certificate. -/
theorem normalizedExternal_range_closed
    {T : H →L[ℂ] HilbertSum E B}
    (bounds : SplitComplexFrameBounds T) :
    IsClosed (Set.range (normalizedExternal T)) :=
  (normalizedExternal_antilipschitz bounds).isClosed_range
    (normalizedExternal T).uniformContinuous

/-- Bounded inverse whose domain is exactly the compatible external range. -/
def normalizedExternalRangeInverse
    {T : H →L[ℂ] HilbertSum E B}
    (bounds : SplitComplexFrameBounds T) :
    (normalizedExternal T).range →L[ℂ] H :=
  ((normalizedExternal T).equivRange
    (normalizedExternal_injective bounds)
    (normalizedExternal_range_closed bounds)).symm.toContinuousLinearMap

/-- Exact left-inverse identity on coherent external data. -/
@[simp]
theorem normalizedExternalRangeInverse_apply
    {T : H →L[ℂ] HilbertSum E B}
    (bounds : SplitComplexFrameBounds T) (x : H) :
    normalizedExternalRangeInverse bounds
      ((normalizedExternal T).rangeRestrict x) = x := by
  simpa only [normalizedExternalRangeInverse] using
    ((normalizedExternal T).equivRange
      (normalizedExternal_injective bounds)
      (normalizedExternal_range_closed bounds)).symm_apply_apply x

end GreenFrame.Concrete
