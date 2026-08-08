import GreenFrame.Concrete.Analysis.GreenStateEnergy

/-!
# Global second-ancestor Green bound

For each camera this module reindexes the divisibility condition by
`m = b_r k`, then sums the remaining coded-base cube series.
-/

open scoped ENNReal lp

namespace GreenFrame.Concrete

/-- Conditional second-ancestor majorant carrying the actual weight. -/
noncomputable def grandparentGreenMajorant
    (omega : AdmissibleInfinitePartition) (f : State) (e : GreenEvent) : ℝ :=
  if HasGrandparent e then
    3 * omega.weight e.1 (eventNumber e) / baseReal e.1 ^ 3 *
      stateEnergy f (grandparentIndex e)
  else
    0

/-- Weight-free second-ancestor dominant. -/
noncomputable def grandparentGreenDominant (f : State) (e : GreenEvent) : ℝ :=
  if HasGrandparent e then
    3 / baseReal e.1 ^ 3 * stateEnergy f (grandparentIndex e)
  else
    0

theorem grandparentGreenMajorant_nonneg
    (omega : AdmissibleInfinitePartition) (f : State) (e : GreenEvent) :
    0 ≤ grandparentGreenMajorant omega f e := by
  by_cases h : HasGrandparent e
  · simp only [grandparentGreenMajorant, h, ↓reduceIte]
    exact mul_nonneg
      (div_nonneg
        (mul_nonneg (by norm_num) (omega.weight_nonneg e.1 (eventNumber e)))
        (pow_nonneg (baseReal_nonneg e.1) _))
      (stateEnergy_nonneg f (grandparentIndex e))
  · simp [grandparentGreenMajorant, h]

theorem grandparentGreenDominant_nonneg (f : State) (e : GreenEvent) :
    0 ≤ grandparentGreenDominant f e := by
  by_cases h : HasGrandparent e
  · simp only [grandparentGreenDominant, h, ↓reduceIte]
    exact mul_nonneg
      (div_nonneg (by norm_num) (pow_nonneg (baseReal_nonneg e.1) _))
      (stateEnergy_nonneg f (grandparentIndex e))
  · simp [grandparentGreenDominant, h]

/-- Dropping the partition weight bounds the second-ancestor term. -/
theorem grandparentGreenMajorant_le_dominant
    (omega : AdmissibleInfinitePartition) (f : State) (e : GreenEvent) :
    grandparentGreenMajorant omega f e ≤ grandparentGreenDominant f e := by
  by_cases h : HasGrandparent e
  · simp only [grandparentGreenMajorant, grandparentGreenDominant, h, ↓reduceIte]
    have hw := omega.weight_le_one e.1 (eventNumber e)
    have hc : 0 ≤ 3 / baseReal e.1 ^ 3 * stateEnergy f (grandparentIndex e) :=
      mul_nonneg
        (div_nonneg (by norm_num) (pow_nonneg (baseReal_nonneg e.1) _))
        (stateEnergy_nonneg f (grandparentIndex e))
    calc
      3 * omega.weight e.1 (eventNumber e) / baseReal e.1 ^ 3 *
          stateEnergy f (grandparentIndex e) =
          (3 / baseReal e.1 ^ 3 * stateEnergy f (grandparentIndex e)) *
            omega.weight e.1 (eventNumber e) := by ring
      _ ≤ (3 / baseReal e.1 ^ 3 * stateEnergy f (grandparentIndex e)) * 1 :=
        mul_le_mul_of_nonneg_left hw hc
      _ = 3 / baseReal e.1 ^ 3 * stateEnergy f (grandparentIndex e) := by ring
  · simp [grandparentGreenMajorant, grandparentGreenDominant, h]

/-- For a fixed camera, the grandparent dominant is summable in the parent. -/
theorem grandparentGreenDominant_camera_summable (f : State) (r : ℕ) :
    Summable (fun m : PNat => grandparentGreenDominant f (r, m)) := by
  have h := divisiblePullback_summable r
    ((stateEnergy_summable f).mul_left (3 / baseReal r ^ 3))
  apply h.congr
  intro m
  simp only [grandparentGreenDominant, HasGrandparent, grandparentIndex,
    divisiblePullback, PNat.dvd_iff]

/-- Exact fixed-camera sum after `m = b k`. -/
theorem grandparentGreenDominant_camera_tsum (f : State) (r : ℕ) :
    (∑' m : PNat, grandparentGreenDominant f (r, m)) =
      3 / baseReal r ^ 3 * ‖f‖ ^ 2 := by
  calc
    (∑' m : PNat, grandparentGreenDominant f (r, m)) =
        ∑' m : PNat, divisiblePullback r
          (fun k => 3 / baseReal r ^ 3 * stateEnergy f k) m := by
      apply tsum_congr
      intro m
      simp only [grandparentGreenDominant, HasGrandparent, grandparentIndex,
        divisiblePullback, PNat.dvd_iff]
    _ = ∑' k : PNat, 3 / baseReal r ^ 3 * stateEnergy f k :=
      tsum_divisiblePullback r _
    _ = 3 / baseReal r ^ 3 * ‖f‖ ^ 2 := by
      rw [tsum_mul_left, stateEnergy_tsum_eq_norm_sq]

/-- The weight-free grandparent dominant is summable. -/
theorem grandparentGreenDominant_summable (f : State) :
    Summable (grandparentGreenDominant f) := by
  apply (summable_prod_of_nonneg
    (fun e => grandparentGreenDominant_nonneg f e)).mpr
  refine ⟨grandparentGreenDominant_camera_summable f, ?_⟩
  have hcoeff : Summable (fun r : ℕ => 3 / baseReal r ^ 3) := by
    exact (inverseBaseCube_summable.mul_left (3 : ℝ)).congr
      fun r => by ring
  apply (hcoeff.mul_right (‖f‖ ^ 2)).congr
  intro r
  exact (grandparentGreenDominant_camera_tsum f r).symm

/-- The second-ancestor majorant is summable. -/
theorem grandparentGreenMajorant_summable
    (omega : AdmissibleInfinitePartition) (f : State) :
    Summable (grandparentGreenMajorant omega f) :=
  Summable.of_nonneg_of_le
    (grandparentGreenMajorant_nonneg omega f)
    (grandparentGreenMajorant_le_dominant omega f)
    (grandparentGreenDominant_summable f)

/-- The global second-ancestor contribution is bounded by `3 S₃`. -/
theorem grandparentGreenMajorant_tsum_le
    (omega : AdmissibleInfinitePartition) (f : State) :
    (∑' e : GreenEvent, grandparentGreenMajorant omega f e) ≤
      3 * S₃ * ‖f‖ ^ 2 := by
  calc
    (∑' e : GreenEvent, grandparentGreenMajorant omega f e) ≤
        ∑' e : GreenEvent, grandparentGreenDominant f e :=
      (grandparentGreenMajorant_summable omega f).tsum_le_tsum
        (grandparentGreenMajorant_le_dominant omega f)
        (grandparentGreenDominant_summable f)
    _ = 3 * S₃ * ‖f‖ ^ 2 := by
      rw [(grandparentGreenDominant_summable f).tsum_prod]
      simp_rw [grandparentGreenDominant_camera_tsum]
      calc
        (∑' r : ℕ, 3 / baseReal r ^ 3 * ‖f‖ ^ 2) =
            (∑' r : ℕ, 3 / baseReal r ^ 3) * ‖f‖ ^ 2 := by
          rw [tsum_mul_right]
        _ = (∑' r : ℕ, 3 * (1 / baseReal r ^ 3)) * ‖f‖ ^ 2 := by
          congr 1
          apply tsum_congr
          intro r
          ring
        _ = (3 * S₃) * ‖f‖ ^ 2 := by
          rw [tsum_mul_left]
          rfl
        _ = 3 * S₃ * ‖f‖ ^ 2 := rfl

end GreenFrame.Concrete
