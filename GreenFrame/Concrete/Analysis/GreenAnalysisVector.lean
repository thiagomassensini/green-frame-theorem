import GreenFrame.Concrete.Analysis.GreenBesselAssembly

/-!
# The global Green coordinate vector

This checkpoint packages the square-summable coordinate family as an actual
complex `ℓ²` vector and proves its energy bound.  Bounded linear-map packaging
is intentionally deferred to the next checkpoint.
-/

open scoped ENNReal lp

namespace GreenFrame.Concrete

/-- The actual global Green coordinate family, packaged as an `ℓ²` vector. -/
noncomputable def greenAnalysis
    (omega : AdmissibleInfinitePartition) (f : State) : ℓ²(GreenEvent, ℂ) :=
  ⟨fun e => greenCoordinate omega e f, by
    apply memℓp_gen
    apply (greenCoordinate_normSq_summable omega f).congr
    intro e
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (Complex.sq_norm (greenCoordinate omega e f)).symm⟩

@[simp]
theorem greenAnalysis_apply
    (omega : AdmissibleInfinitePartition) (f : State) (e : GreenEvent) :
    greenAnalysis omega f e = greenCoordinate omega e f :=
  rfl

/-- Squared norm of the packaged analysis vector equals its coordinate energy. -/
theorem greenAnalysis_norm_sq_eq
    (omega : AdmissibleInfinitePartition) (f : State) :
    ‖greenAnalysis omega f‖ ^ 2 =
      ∑' e : GreenEvent, Complex.normSq (greenCoordinate omega e f) := by
  calc
    ‖greenAnalysis omega f‖ ^ 2 =
        ∑' e : GreenEvent, ‖greenCoordinate omega e f‖ ^ (2 : ℕ) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, greenAnalysis_apply] using
        lp.norm_rpow_eq_tsum
          (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (greenAnalysis omega f)
    _ = ∑' e : GreenEvent, Complex.normSq (greenCoordinate omega e f) := by
      apply tsum_congr
      intro e
      exact Complex.sq_norm _

/-- The explicit global Green Bessel inequality. -/
theorem greenAnalysis_norm_sq_le
    (omega : AdmissibleInfinitePartition) (f : State) :
    ‖greenAnalysis omega f‖ ^ 2 ≤ greenBesselConstant * ‖f‖ ^ 2 := by
  rw [greenAnalysis_norm_sq_eq]
  exact greenCoordinate_tsum_normSq_le omega f

end GreenFrame.Concrete
