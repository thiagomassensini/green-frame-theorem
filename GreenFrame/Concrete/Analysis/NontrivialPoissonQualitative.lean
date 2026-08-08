import GreenFrame.Concrete.Analysis.RestrictedGraph
import GreenFrame.Concrete.Analysis.CanonicalParseval

/-!
# Qualitative nontrivial normalized bulk and Poisson operator
-/

noncomputable section

open scoped InnerProductSpace

namespace GreenFrame.Concrete

variable {H E B : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]

/-- Positive square root used to transfer a raw bulk witness through Parseval
normalization. -/
def sqrtFrame (T : H →L[ℂ] HilbertSum E B) : H →L[ℂ] H :=
  CFC.rpow (frameOperator T) (1 / 2 : ℝ)

/-- The chosen inverse square root cancels the positive square root. -/
theorem inverseSqrtFrame_comp_sqrtFrame
    {T : H →L[ℂ] HilbertSum E B}
    (bounds : ComplexFrameBounds T) :
    (inverseSqrtFrame T).comp (sqrtFrame T) = 1 := by
  simpa only [inverseSqrtFrame, sqrtFrame, CFC.rpow_eq_pow,
    ContinuousLinearMap.mul_def] using
    CFC.rpow_neg_mul_rpow (a := frameOperator T) (1 / 2 : ℝ)
      (frameOperator_strictlyPositive bounds)

@[simp]
theorem inverseSqrtFrame_sqrtFrame_apply
    {T : H →L[ℂ] HilbertSum E B}
    (bounds : ComplexFrameBounds T) (x : H) :
    inverseSqrtFrame T (sqrtFrame T x) = x := by
  have h := congrArg
    (fun S : H →L[ℂ] H => S x)
    (inverseSqrtFrame_comp_sqrtFrame bounds)
  simpa using h

/-- A raw bulk witness survives canonical Parseval normalization. -/
theorem normalizedBulk_sqrtFrame_apply
    {T : H →L[ℂ] HilbertSum E B}
    (bounds : ComplexFrameBounds T) (x : H) :
    normalizedBulk T (sqrtFrame T x) = rawBulk T x := by
  simp [normalizedBulk, inverseSqrtFrame_sqrtFrame_apply bounds]

theorem normalizedBulk_nonzero_of_rawBulk_witness
    {T : H →L[ℂ] HilbertSum E B}
    (bounds : ComplexFrameBounds T)
    (h : ∃ x, rawBulk T x ≠ 0) :
    ∃ u, normalizedBulk T u ≠ 0 := by
  obtain ⟨x, hx⟩ := h
  refine ⟨sqrtFrame T x, ?_⟩
  rw [normalizedBulk_sqrtFrame_apply bounds]
  exact hx

/-- Nonzero normalized bulk forces the static Poisson return to be nonzero. -/
theorem restrictedPoisson_ne_zero
    {T : H →L[ℂ] HilbertSum E B}
    (bounds : SplitComplexFrameBounds T)
    (h : ∃ x, normalizedBulk T x ≠ 0) :
    restrictedPoisson bounds ≠ 0 := by
  rintro hzero
  obtain ⟨x, hx⟩ := h
  apply hx
  calc
    normalizedBulk T x =
        restrictedPoisson bounds ((normalizedExternal T).rangeRestrict x) :=
      (restrictedPoisson_apply_external bounds x).symm
    _ = 0 := by rw [hzero]; rfl

/-- End-to-end nontriviality from the concrete raw witness. -/
theorem restrictedPoisson_ne_zero_of_rawBulk_witness
    {T : H →L[ℂ] HilbertSum E B}
    (bounds : SplitComplexFrameBounds T)
    (h : ∃ x, rawBulk T x ≠ 0) :
    restrictedPoisson bounds ≠ 0 :=
  restrictedPoisson_ne_zero bounds <|
    normalizedBulk_nonzero_of_rawBulk_witness
      bounds.toComplexFrameBounds h

end GreenFrame.Concrete
