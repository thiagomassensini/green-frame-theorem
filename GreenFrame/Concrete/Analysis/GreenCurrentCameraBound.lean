import GreenFrame.Concrete.Analysis.GreenStateEnergy

/-!
# Current-node bound before event-space reindexing

For each current state coordinate, the camera weights yield a summable
majorant.  Tonelli then gives summability on the full number--camera product.
-/

open scoped ENNReal lp

namespace GreenFrame.Concrete

/-- Current-node majorant, indexed by current number and camera. -/
noncomputable def currentCameraMajorant
    (omega : AdmissibleInfinitePartition) (f : State)
    (n : PNat) (r : ℕ) : ℝ :=
  3 * omega.weight r n / baseReal r * stateEnergy f n

theorem currentCameraMajorant_nonneg
    (omega : AdmissibleInfinitePartition) (f : State) (n : PNat) (r : ℕ) :
    0 ≤ currentCameraMajorant omega f n r := by
  exact mul_nonneg
    (div_nonneg (mul_nonneg (by norm_num) (omega.weight_nonneg r n))
      (baseReal_nonneg r))
    (stateEnergy_nonneg f n)

/-- Each current camera is bounded by its half-mass share. -/
theorem currentCameraMajorant_le
    (omega : AdmissibleInfinitePartition) (f : State) (n : PNat) (r : ℕ) :
    currentCameraMajorant omega f n r ≤
      ((3 : ℝ) / 2 * stateEnergy f n) * omega.weight r n := by
  have hb : (2 : ℝ) ≤ baseReal r := by
    have hcast : (2 : ℝ) ≤ (baseNat r : ℝ) := by
      exact_mod_cast baseNat_ge_two r
    simpa only [baseReal_def] using hcast
  have hinv : 1 / baseReal r ≤ (1 : ℝ) / 2 :=
    one_div_le_one_div_of_le (by norm_num) hb
  calc
    currentCameraMajorant omega f n r =
        (3 * omega.weight r n * stateEnergy f n) * (1 / baseReal r) := by
      simp only [currentCameraMajorant]
      ring
    _ ≤ (3 * omega.weight r n * stateEnergy f n) * ((1 : ℝ) / 2) := by
      exact mul_le_mul_of_nonneg_left hinv
        (mul_nonneg
          (mul_nonneg (by norm_num) (omega.weight_nonneg r n))
          (stateEnergy_nonneg f n))
    _ = ((3 : ℝ) / 2 * stateEnergy f n) * omega.weight r n := by ring

/-- For fixed current number, the camera majorants are summable. -/
theorem currentCameraMajorant_summable
    (omega : AdmissibleInfinitePartition) (f : State) (n : PNat) :
    Summable (currentCameraMajorant omega f n) := by
  exact Summable.of_nonneg_of_le
    (currentCameraMajorant_nonneg omega f n)
    (currentCameraMajorant_le omega f n)
    ((omega.weight_summable n).mul_left ((3 : ℝ) / 2 * stateEnergy f n))

/-- The total current contribution at one number is at most `3/2` times its energy. -/
theorem currentCameraMajorant_tsum_le
    (omega : AdmissibleInfinitePartition) (f : State) (n : PNat) :
    (∑' r : ℕ, currentCameraMajorant omega f n r) ≤
      (3 : ℝ) / 2 * stateEnergy f n := by
  calc
    (∑' r : ℕ, currentCameraMajorant omega f n r) ≤
        ∑' r : ℕ,
          (((3 : ℝ) / 2 * stateEnergy f n) * omega.weight r n) :=
      (currentCameraMajorant_summable omega f n).tsum_le_tsum
        (currentCameraMajorant_le omega f n)
        ((omega.weight_summable n).mul_left _)
    _ = ((3 : ℝ) / 2 * stateEnergy f n) *
        (∑' r : ℕ, omega.weight r n) := by rw [tsum_mul_left]
    _ ≤ ((3 : ℝ) / 2 * stateEnergy f n) * 1 := by
      exact mul_le_mul_of_nonneg_left (weight_tsum_le_one omega n)
        (mul_nonneg (by norm_num) (stateEnergy_nonneg f n))
    _ = (3 : ℝ) / 2 * stateEnergy f n := by ring

/-- The full number--camera current majorant is summable. -/
theorem currentCameraMajorant_prod_summable
    (omega : AdmissibleInfinitePartition) (f : State) :
    Summable (fun p : PNat × ℕ =>
      currentCameraMajorant omega f p.1 p.2) := by
  apply (summable_prod_of_nonneg
    (fun p => currentCameraMajorant_nonneg omega f p.1 p.2)).mpr
  refine ⟨currentCameraMajorant_summable omega f, ?_⟩
  exact Summable.of_nonneg_of_le
    (fun n => tsum_nonneg (currentCameraMajorant_nonneg omega f n))
    (currentCameraMajorant_tsum_le omega f)
    ((stateEnergy_summable f).mul_left ((3 : ℝ) / 2))

end GreenFrame.Concrete
