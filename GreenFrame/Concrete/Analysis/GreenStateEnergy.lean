import GreenFrame.Concrete.Analysis.GreenBesselConstants

/-!
# State energy identities for the global Green estimate

This checkpoint converts the defining `Memℓp` certificate of a complex
`ℓ²` state into a summable coordinate norm-square family and its exact total.
-/

open scoped ENNReal lp

namespace GreenFrame.Concrete

/-- Pointwise energy of a complex state coordinate. -/
def stateEnergy (f : State) (n : PNat) : ℝ :=
  Complex.normSq (f n)

/-- State energy is nonnegative. -/
theorem stateEnergy_nonneg (f : State) (n : PNat) :
    0 ≤ stateEnergy f n :=
  Complex.normSq_nonneg _

/-- The coordinate-energy series of an `ℓ²` state is summable. -/
theorem stateEnergy_summable (f : State) :
    Summable (stateEnergy f) := by
  apply ((lp.memℓp f).summable
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).congr
  intro n
  simpa only [stateEnergy, ENNReal.toReal_ofNat] using
    Complex.sq_norm (f n)

/-- The total coordinate energy is the Hilbert norm squared. -/
theorem stateEnergy_tsum_eq_norm_sq (f : State) :
    (∑' n : PNat, stateEnergy f n) = ‖f‖ ^ 2 := by
  calc
    (∑' n : PNat, stateEnergy f n) =
        ∑' n : PNat, ‖f n‖ ^ 2 := by
      apply tsum_congr
      intro n
      simpa only [stateEnergy] using (Complex.sq_norm (f n)).symm
    _ = ‖f‖ ^ 2 :=
      (lp.norm_rpow_eq_tsum
        (by norm_num : 0 < (2 : ℝ≥0∞).toReal) f).symm

/-- The camera-weight sum is at most one at every state coordinate. -/
theorem weight_tsum_le_one (omega : AdmissibleInfinitePartition) (n : PNat) :
    (∑' r : ℕ, omega.weight r n) ≤ 1 := by
  by_cases hn : n = 1
  · subst n
    simp
  · rw [omega.weight_tsum_eq_one hn]

end GreenFrame.Concrete
