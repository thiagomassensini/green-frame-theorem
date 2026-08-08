import GreenFrame.Concrete.Analysis.GreenStateEnergy

/-!
# Global first-ancestor Green bound

The partition weight is dropped using `weight_le_one`, leaving a product of
the state energy with the coded-base square series.
-/

open scoped ENNReal lp

namespace GreenFrame.Concrete

/-- First-ancestor majorant carrying the actual partition weight. -/
noncomputable def parentGreenMajorant
    (omega : AdmissibleInfinitePartition) (f : State) (e : GreenEvent) : ℝ :=
  12 * omega.weight e.1 (eventNumber e) / baseReal e.1 ^ 2 * stateEnergy f e.2

/-- Weight-free first-ancestor dominant. -/
noncomputable def parentGreenDominant (f : State) (e : GreenEvent) : ℝ :=
  12 / baseReal e.1 ^ 2 * stateEnergy f e.2

theorem parentGreenMajorant_nonneg
    (omega : AdmissibleInfinitePartition) (f : State) (e : GreenEvent) :
    0 ≤ parentGreenMajorant omega f e := by
  exact mul_nonneg
    (div_nonneg
      (mul_nonneg (by norm_num) (omega.weight_nonneg e.1 (eventNumber e)))
      (pow_nonneg (baseReal_nonneg e.1) _))
    (stateEnergy_nonneg f e.2)

theorem parentGreenDominant_nonneg (f : State) (e : GreenEvent) :
    0 ≤ parentGreenDominant f e := by
  exact mul_nonneg
    (div_nonneg (by norm_num) (pow_nonneg (baseReal_nonneg e.1) _))
    (stateEnergy_nonneg f e.2)

/-- Dropping the partition weight bounds the first-ancestor term. -/
theorem parentGreenMajorant_le_dominant
    (omega : AdmissibleInfinitePartition) (f : State) (e : GreenEvent) :
    parentGreenMajorant omega f e ≤ parentGreenDominant f e := by
  have hw := omega.weight_le_one e.1 (eventNumber e)
  have hc : 0 ≤ 12 / baseReal e.1 ^ 2 * stateEnergy f e.2 :=
    parentGreenDominant_nonneg f e
  calc
    parentGreenMajorant omega f e =
        (12 / baseReal e.1 ^ 2 * stateEnergy f e.2) *
          omega.weight e.1 (eventNumber e) := by
      simp only [parentGreenMajorant]
      ring
    _ ≤ (12 / baseReal e.1 ^ 2 * stateEnergy f e.2) * 1 :=
      mul_le_mul_of_nonneg_left hw hc
    _ = parentGreenDominant f e := by simp [parentGreenDominant]

/-- The weight-free parent dominant is summable. -/
theorem parentGreenDominant_summable (f : State) :
    Summable (parentGreenDominant f) := by
  apply (summable_prod_of_nonneg
    (fun e => parentGreenDominant_nonneg f e)).mpr
  refine ⟨?_, ?_⟩
  · intro r
    exact (stateEnergy_summable f).mul_left (12 / baseReal r ^ 2)
  · have hcoeff : Summable (fun r : ℕ => 12 / baseReal r ^ 2) := by
      exact (inverseBaseSquare_summable.mul_left (12 : ℝ)).congr
        fun r => by ring
    apply (hcoeff.mul_right (‖f‖ ^ 2)).congr
    intro r
    rw [tsum_mul_left, stateEnergy_tsum_eq_norm_sq]

/-- The first-ancestor majorant is summable. -/
theorem parentGreenMajorant_summable
    (omega : AdmissibleInfinitePartition) (f : State) :
    Summable (parentGreenMajorant omega f) :=
  Summable.of_nonneg_of_le
    (parentGreenMajorant_nonneg omega f)
    (parentGreenMajorant_le_dominant omega f)
    (parentGreenDominant_summable f)

/-- The global first-ancestor contribution is bounded by `12 S₂`. -/
theorem parentGreenMajorant_tsum_le
    (omega : AdmissibleInfinitePartition) (f : State) :
    (∑' e : GreenEvent, parentGreenMajorant omega f e) ≤
      12 * S₂ * ‖f‖ ^ 2 := by
  calc
    (∑' e : GreenEvent, parentGreenMajorant omega f e) ≤
        ∑' e : GreenEvent, parentGreenDominant f e :=
      (parentGreenMajorant_summable omega f).tsum_le_tsum
        (parentGreenMajorant_le_dominant omega f)
        (parentGreenDominant_summable f)
    _ = 12 * S₂ * ‖f‖ ^ 2 := by
      rw [(parentGreenDominant_summable f).tsum_prod]
      simp_rw [parentGreenDominant, tsum_mul_left, stateEnergy_tsum_eq_norm_sq]
      calc
        (∑' r : ℕ, 12 / baseReal r ^ 2 * ‖f‖ ^ 2) =
            (∑' r : ℕ, 12 * (1 / baseReal r ^ 2)) * ‖f‖ ^ 2 := by
          rw [tsum_mul_right]
        _ = (12 * S₂) * ‖f‖ ^ 2 := by rw [tsum_mul_left]
        _ = 12 * S₂ * ‖f‖ ^ 2 := rfl

end GreenFrame.Concrete
