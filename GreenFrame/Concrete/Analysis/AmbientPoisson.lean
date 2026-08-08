import GreenFrame.Concrete.Analysis.StaticPoisson
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Ambient canonical Poisson completion

Optional stronger checkpoint implementing the paper's literal formula
`S_E = (E₀†E₀)⁻¹E₀†` and `M = B₀S_E` on the full external Hilbert
space.  The restricted-range construction should land first because it has a
smaller elaboration surface.
-/

noncomputable section

open scoped InnerProduct InnerProductSpace NNReal

namespace GreenFrame.Concrete

variable {H E B : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]

def externalGram (T : H →L[ℂ] HilbertSum E B) : H →L[ℂ] H :=
  (normalizedExternal T)† ∘L normalizedExternal T

theorem externalGram_inner
    (T : H →L[ℂ] HilbertSum E B) (x : H) :
    ⟪externalGram T x, x⟫_ℂ =
      ⟪normalizedExternal T x, normalizedExternal T x⟫_ℂ := by
  change ⟪((normalizedExternal T)†) (normalizedExternal T x), x⟫_ℂ = _
  exact (normalizedExternal T).adjoint_inner_left x (normalizedExternal T x)

theorem externalGram_isUnit
    {T : H →L[ℂ] HilbertSum E B}
    (bounds : SplitComplexFrameBounds T) : IsUnit (externalGram T) := by
  let a : ℝ := normalizedExternalLower bounds
  let c : ℝ≥0 := ⟨a, (normalizedExternalLower_pos bounds).le⟩
  have hc : 0 < c := by
    change 0 < a
    exact normalizedExternalLower_pos bounds
  refine ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map
    (externalGram T) (c := c) hc ?_
  intro x
  change ‖x‖ ^ 2 * a ≤ ‖⟪externalGram T x, x⟫_ℂ‖
  calc
    ‖x‖ ^ 2 * a = a * ‖x‖ ^ 2 := mul_comm _ _
    _ ≤ ‖normalizedExternal T x‖ ^ 2 :=
      normalizedExternal_lower_norm_sq bounds x
    _ = ‖⟪externalGram T x, x⟫_ℂ‖ := by
      rw [externalGram_inner]
      exact (inner_self_eq_norm_sq (normalizedExternal T x)).symm.trans
        (inner_self_re_eq_norm (normalizedExternal T x))

theorem externalGram_strictlyPositive
    {T : H →L[ℂ] HilbertSum E B}
    (bounds : SplitComplexFrameBounds T) :
    IsStrictlyPositive (externalGram T) :=
  (externalGram_isUnit bounds).isStrictlyPositive <|
    (ContinuousLinearMap.nonneg_iff_isPositive _).2
      (ContinuousLinearMap.isPositive_adjoint_comp_self
        (normalizedExternal T))

def externalGramInverse (T : H →L[ℂ] HilbertSum E B) : H →L[ℂ] H :=
  CFC.rpow (externalGram T) (-1 : ℝ)

/-- Literal ambient synthesis formula `(E₀†E₀)⁻¹E₀†`. -/
def ambientExternalSynthesis
    (T : H →L[ℂ] HilbertSum E B) : E →L[ℂ] H :=
  externalGramInverse T ∘L (normalizedExternal T)†

theorem ambientExternalSynthesis_comp_external
    {T : H →L[ℂ] HilbertSum E B}
    (bounds : SplitComplexFrameBounds T) :
    ambientExternalSynthesis T ∘L normalizedExternal T = 1 := by
  calc
    ambientExternalSynthesis T ∘L normalizedExternal T
        = externalGramInverse T ∘L externalGram T := by
      simp only [ambientExternalSynthesis, externalGram,
        ContinuousLinearMap.comp_assoc]
    _ = 1 := by
      simpa only [externalGramInverse, ContinuousLinearMap.mul_def,
        CFC.rpow_one (externalGram T)
          (externalGram_strictlyPositive bounds).nonneg] using
        CFC.rpow_neg_mul_rpow (a := externalGram T) 1
          (externalGram_strictlyPositive bounds)

/-- Ambient static Poisson operator from arbitrary external data. -/
def ambientPoisson
    (T : H →L[ℂ] HilbertSum E B) : E →L[ℂ] B :=
  normalizedBulk T ∘L ambientExternalSynthesis T

theorem ambientPoisson_intertwining
    {T : H →L[ℂ] HilbertSum E B}
    (bounds : SplitComplexFrameBounds T) :
    ambientPoisson T ∘L normalizedExternal T = normalizedBulk T := by
  calc
    ambientPoisson T ∘L normalizedExternal T
        = normalizedBulk T ∘L
            (ambientExternalSynthesis T ∘L normalizedExternal T) := by
      simp only [ambientPoisson, ContinuousLinearMap.comp_assoc]
    _ = normalizedBulk T := by
      rw [ambientExternalSynthesis_comp_external bounds]
      exact ContinuousLinearMap.comp_id _

end GreenFrame.Concrete
