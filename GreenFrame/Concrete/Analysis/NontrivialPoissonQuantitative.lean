import GreenFrame.Concrete.Analysis.NontrivialPoissonQualitative

/-!
# Quantitative square-root transfer to the normalized bulk operator
-/

noncomputable section

open scoped InnerProduct InnerProductSpace

namespace GreenFrame.Concrete

variable {H E B : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]

/-- The positive square root is nonnegative. -/
theorem sqrtFrame_nonneg (T : H →L[ℂ] HilbertSum E B) :
    0 ≤ sqrtFrame T :=
  CFC.rpow_nonneg

/-- The positive square root is self-adjoint. -/
theorem sqrtFrame_isSelfAdjoint (T : H →L[ℂ] HilbertSum E B) :
    IsSelfAdjoint (sqrtFrame T) :=
  IsSelfAdjoint.of_nonneg (sqrtFrame_nonneg T)

/-- Adjoint formula for the positive square root. -/
theorem sqrtFrame_adjoint (T : H →L[ℂ] HilbertSum E B) :
    (sqrtFrame T)† = sqrtFrame T :=
  (sqrtFrame_isSelfAdjoint T).adjoint_eq

/-- Squaring the CFC square root recovers the frame operator. -/
theorem sqrtFrame_comp_self
    {T : H →L[ℂ] HilbertSum E B}
    (bounds : ComplexFrameBounds T) :
    (sqrtFrame T).comp (sqrtFrame T) = frameOperator T := by
  let F : H →L[ℂ] H := frameOperator T
  have hFnonneg : 0 ≤ F :=
    (ContinuousLinearMap.nonneg_iff_isPositive F).2
      (frameOperator_positive T)
  change CFC.rpow F (1 / 2 : ℝ) * CFC.rpow F (1 / 2 : ℝ) = F
  calc
    CFC.rpow F (1 / 2 : ℝ) * CFC.rpow F (1 / 2 : ℝ) =
        CFC.rpow F ((1 / 2 : ℝ) + (1 / 2 : ℝ)) :=
      by
        simpa only [CFC.rpow_eq_pow] using
          (CFC.rpow_add (a := F) (x := (1 / 2 : ℝ))
            (y := (1 / 2 : ℝ)) (frameOperator_isUnit bounds)).symm
    _ = CFC.rpow F (1 : ℝ) := by norm_num
    _ = F := by
      simpa only [CFC.rpow_eq_pow] using CFC.rpow_one F hFnonneg

/-- The square-root witness has exactly the raw analysis energy. -/
theorem sqrtFrame_norm_sq_eq_analysis_norm_sq
    {T : H →L[ℂ] HilbertSum E B}
    (bounds : ComplexFrameBounds T) (x : H) :
    ‖sqrtFrame T x‖ ^ 2 = ‖T x‖ ^ 2 := by
  calc
    ‖sqrtFrame T x‖ ^ 2 =
        RCLike.re ⟪sqrtFrame T x, sqrtFrame T x⟫_ℂ :=
      (inner_self_eq_norm_sq _).symm
    _ = RCLike.re ⟪((sqrtFrame T)†) (sqrtFrame T x), x⟫_ℂ := by
      rw [← (sqrtFrame T).adjoint_inner_left x (sqrtFrame T x)]
    _ = RCLike.re ⟪((sqrtFrame T)† ∘L sqrtFrame T) x, x⟫_ℂ := rfl
    _ = RCLike.re ⟪frameOperator T x, x⟫_ℂ := by
      rw [sqrtFrame_adjoint, sqrtFrame_comp_self bounds]
    _ = ‖T x‖ ^ 2 := frameOperator_re_inner T x

/-- A quantitative raw bulk witness on a unit vector transfers to an
operator-norm lower bound after canonical Parseval normalization. -/
theorem normalizedBulk_opNorm_sq_lower_of_raw_witness
    {T : H →L[ℂ] HilbertSum E B}
    (bounds : ComplexFrameBounds T) {x : H} (hx : ‖x‖ = 1)
    {c : ℝ} (hwitness : c ≤ ‖rawBulk T x‖ ^ 2) :
    c / bounds.upper ≤ ‖normalizedBulk T‖ ^ 2 := by
  let u : H := sqrtFrame T x
  have hu : ‖u‖ ^ 2 ≤ bounds.upper := by
    calc
      ‖u‖ ^ 2 = ‖T x‖ ^ 2 :=
        sqrtFrame_norm_sq_eq_analysis_norm_sq bounds x
      _ ≤ bounds.upper * ‖x‖ ^ 2 := bounds.upper_norm_sq x
      _ = bounds.upper := by rw [hx]; norm_num
  have happly :
      ‖normalizedBulk T u‖ ≤
        ‖normalizedBulk T‖ * ‖u‖ :=
    (normalizedBulk T).le_opNorm u
  have happlySq :
      ‖normalizedBulk T u‖ ^ 2 ≤
        (‖normalizedBulk T‖ * ‖u‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 happly
  have hproduct :
      c ≤ ‖normalizedBulk T‖ ^ 2 * bounds.upper := by
    calc
      c ≤ ‖rawBulk T x‖ ^ 2 := hwitness
      _ = ‖normalizedBulk T u‖ ^ 2 := by
        dsimp [u]
        rw [normalizedBulk_sqrtFrame_apply bounds x]
      _ ≤ (‖normalizedBulk T‖ * ‖u‖) ^ 2 := happlySq
      _ = ‖normalizedBulk T‖ ^ 2 * ‖u‖ ^ 2 := by ring
      _ ≤ ‖normalizedBulk T‖ ^ 2 * bounds.upper :=
        mul_le_mul_of_nonneg_left hu (sq_nonneg _)
  exact (div_le_iff₀ bounds.upper_pos).2 hproduct

end GreenFrame.Concrete
