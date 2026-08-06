import GreenFrame.Analysis.FullFrame

/-!
# Abstract frame operator consequences
-/

namespace GreenFrame

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- A compact certificate for the two frame inequalities. -/
structure FrameCertificate (T : H →L[ℝ] K) where
  lower : ∀ x, (1 / 2 : ℝ) * ‖x‖ ^ 2 ≤ ‖T x‖ ^ 2
  upper : ∀ x, ‖T x‖ ^ 2 ≤ fullFrameBound * ‖x‖ ^ 2

/-- Lower operator inequality exposed as a named theorem. -/
theorem frameOperator_lower {T : H →L[ℝ] K} (hT : FrameCertificate T) (x : H) :
    (1 / 2 : ℝ) * ‖x‖ ^ 2 ≤ ‖T x‖ ^ 2 :=
  hT.lower x

/-- Upper operator inequality exposed as a named theorem. -/
theorem frameOperator_upper {T : H →L[ℝ] K} (hT : FrameCertificate T) (x : H) :
    ‖T x‖ ^ 2 ≤ fullFrameBound * ‖x‖ ^ 2 :=
  hT.upper x

/-- A positive lower frame bound makes the analysis injective. -/
theorem fullAnalysis_injective {T : H →L[ℝ] K} (hT : FrameCertificate T) :
    Function.Injective T := by
  intro x y hxy
  have hmap : T (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hlower := hT.lower (x - y)
  rw [hmap, norm_zero, zero_pow] at hlower
  have hnorm : ‖x - y‖ = 0 := by
    nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

end GreenFrame
