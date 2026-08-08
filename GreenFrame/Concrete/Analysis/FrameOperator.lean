import GreenFrame.Concrete.Analysis.ComplexFrameBounds
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Positive invertible frame operator

This is the recommended first operator-theory checkpoint.  It does not yet
construct a functional-calculus square root.
-/

noncomputable section

open scoped InnerProduct InnerProductSpace NNReal

namespace GreenFrame.Concrete

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The frame operator `T†T`. -/
def frameOperator (T : H →L[ℂ] K) : H →L[ℂ] H :=
  T† ∘L T

/-- Quadratic form of the frame operator. -/
theorem frameOperator_inner (T : H →L[ℂ] K) (x : H) :
    ⟪frameOperator T x, x⟫_ℂ = ⟪T x, T x⟫_ℂ := by
  change ⟪T† (T x), x⟫_ℂ = ⟪T x, T x⟫_ℂ
  exact T.adjoint_inner_left x (T x)

/-- Real quadratic form is exactly the analysis energy. -/
theorem frameOperator_re_inner (T : H →L[ℂ] K) (x : H) :
    RCLike.re ⟪frameOperator T x, x⟫_ℂ = ‖T x‖ ^ 2 := by
  rw [frameOperator_inner, inner_self_eq_norm_sq]

/-- The frame operator is positive without any frame lower bound. -/
theorem frameOperator_positive (T : H →L[ℂ] K) :
    (frameOperator T).IsPositive :=
  ContinuousLinearMap.isPositive_adjoint_comp_self T

/-- The recorded lower frame bound is coercivity of the frame operator. -/
theorem frameOperator_coercive {T : H →L[ℂ] K}
    (bounds : ComplexFrameBounds T) (x : H) :
    bounds.lower * ‖x‖ ^ 2 ≤ RCLike.re ⟪frameOperator T x, x⟫_ℂ := by
  rw [frameOperator_re_inner]
  exact bounds.lower_norm_sq x

/-- A positive lower frame bound makes `T†T` a unit in the Banach algebra of
continuous endomorphisms. -/
theorem frameOperator_isUnit {T : H →L[ℂ] K}
    (bounds : ComplexFrameBounds T) : IsUnit (frameOperator T) := by
  let c : ℝ≥0 := ⟨bounds.lower, bounds.lower_pos.le⟩
  have hc : 0 < c := by
    change 0 < bounds.lower
    exact bounds.lower_pos
  refine ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map
    (frameOperator T) (c := c) hc ?_
  intro x
  change ‖x‖ ^ 2 * bounds.lower ≤ ‖⟪frameOperator T x, x⟫_ℂ‖
  calc
    ‖x‖ ^ 2 * bounds.lower = bounds.lower * ‖x‖ ^ 2 := mul_comm _ _
    _ ≤ ‖T x‖ ^ 2 := bounds.lower_norm_sq x
    _ = ‖⟪frameOperator T x, x⟫_ℂ‖ := by
      rw [frameOperator_inner]
      exact (inner_self_eq_norm_sq (T x)).symm.trans
        (inner_self_re_eq_norm (T x))

/-- Invertibility exposed as ordinary bijectivity. -/
theorem frameOperator_bijective {T : H →L[ℂ] K}
    (bounds : ComplexFrameBounds T) : Function.Bijective (frameOperator T) :=
  ContinuousLinearMap.isUnit_iff_bijective.mp (frameOperator_isUnit bounds)

/-- Strict positivity packages positivity and invertibility for the continuous
functional calculus. -/
theorem frameOperator_strictlyPositive {T : H →L[ℂ] K}
    (bounds : ComplexFrameBounds T) : IsStrictlyPositive (frameOperator T) :=
  (frameOperator_isUnit bounds).isStrictlyPositive <|
    (ContinuousLinearMap.nonneg_iff_isPositive _).2 (frameOperator_positive T)

end GreenFrame.Concrete