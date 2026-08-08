import GreenFrame.Concrete.Analysis.FrameOperator
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Canonical Parseval normalization

The only genuinely spectral bridge is isolated in this module.
-/

noncomputable section

open scoped InnerProduct InnerProductSpace

namespace GreenFrame.Concrete

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Canonical inverse square root of the frame operator. -/
def inverseSqrtFrame (T : H →L[ℂ] K) : H →L[ℂ] H :=
  CFC.rpow (frameOperator T) (-(1 / 2 : ℝ))

/-- The inverse square root is nonnegative. -/
theorem inverseSqrtFrame_nonneg (T : H →L[ℂ] K) :
    0 ≤ inverseSqrtFrame T :=
  CFC.rpow_nonneg

/-- The inverse square root is self-adjoint. -/
theorem inverseSqrtFrame_isSelfAdjoint (T : H →L[ℂ] K) :
    IsSelfAdjoint (inverseSqrtFrame T) :=
  IsSelfAdjoint.of_nonneg (inverseSqrtFrame_nonneg T)

/-- Adjoint form used when normalizing `V†V`. -/
theorem inverseSqrtFrame_adjoint (T : H →L[ℂ] K) :
    (inverseSqrtFrame T)† = inverseSqrtFrame T :=
  (inverseSqrtFrame_isSelfAdjoint T).adjoint_eq

/-- Functional-calculus normalization identity. -/
theorem inverseSqrt_frameOperator_inverseSqrt {T : H →L[ℂ] K}
    (bounds : ComplexFrameBounds T) :
    inverseSqrtFrame T ∘L frameOperator T ∘L inverseSqrtFrame T = 1 := by
  simpa only [inverseSqrtFrame, CFC.rpow_eq_pow, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_assoc] using
    CFC.conjugate_rpow_neg_one_half
      (frameOperator T) (frameOperator_strictlyPositive bounds)

/-- Canonically normalized analysis `T (T†T)⁻¹/²`. -/
def canonicalAnalysis (T : H →L[ℂ] K) : H →L[ℂ] K :=
  T ∘L inverseSqrtFrame T

/-- The canonical analysis has identity Gram operator. -/
theorem canonicalAnalysis_adjoint_comp_self {T : H →L[ℂ] K}
    (bounds : ComplexFrameBounds T) :
    (canonicalAnalysis T)† ∘L canonicalAnalysis T = 1 := by
  let Q : H →L[ℂ] H := inverseSqrtFrame T
  calc
    (canonicalAnalysis T)† ∘L canonicalAnalysis T
        = (Q† ∘L T†) ∘L (T ∘L Q) := by
            rw [canonicalAnalysis, ContinuousLinearMap.adjoint_comp]
    _ = Q† ∘L (T† ∘L T) ∘L Q := rfl
    _ = Q ∘L frameOperator T ∘L Q := by
          rw [show Q† = Q from inverseSqrtFrame_adjoint T]
          rfl
    _ = 1 := inverseSqrt_frameOperator_inverseSqrt bounds

/-- Parseval normalization is an isometry. -/
theorem canonicalAnalysis_isometry {T : H →L[ℂ] K}
    (bounds : ComplexFrameBounds T) : Isometry (canonicalAnalysis T) :=
  (ContinuousLinearMap.isometry_iff_adjoint_comp_self _).2
    (canonicalAnalysis_adjoint_comp_self bounds)

/-- Bundled canonical Parseval analysis, constructed rather than assumed. -/
def canonicalParseval {T : H →L[ℂ] K}
    (bounds : ComplexFrameBounds T) : H →ₗᵢ[ℂ] K :=
  (canonicalAnalysis T).toLinearMap.toLinearIsometry <| by
    exact canonicalAnalysis_isometry bounds

@[simp]
theorem canonicalParseval_apply {T : H →L[ℂ] K}
    (bounds : ComplexFrameBounds T) (x : H) :
    canonicalParseval bounds x = canonicalAnalysis T x :=
  rfl

theorem canonicalParseval_norm {T : H →L[ℂ] K}
    (bounds : ComplexFrameBounds T) (x : H) :
    ‖canonicalAnalysis T x‖ = ‖x‖ := by
  simpa only [canonicalParseval_apply] using
    (canonicalParseval bounds).norm_map x

end GreenFrame.Concrete
