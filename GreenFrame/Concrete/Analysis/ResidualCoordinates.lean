import GreenFrame.Concrete.Analysis.GreenStencilComplex

/-!
# Residual coordinates for the concrete all-bases partition

This is the first residual checkpoint.  It contains only the pointwise
return mass, its camera sum, the exact half-to-one camera bounds, and the
complex residual coordinate.  Global product summability and the packaged
analysis operator belong to `ResidualAnalysis`.

The residual product is ordered as `(number, camera code)`.  This is the
opposite order from `GreenEvent`, intentionally: Tonelli then sums cameras
inside each state coordinate without an additional product reindexing.
-/

open scoped ENNReal lp

namespace GreenFrame.Concrete

/-- Residual coordinates are indexed by state number and camera code. -/
abbrev ResidualEvent := PNat × ℕ

/-- Hilbert space of all residual coordinates. -/
noncomputable abbrev ResidualSpace := ℓ²(ResidualEvent, ℂ)

/-- Reciprocal of the physical base represented by a camera code. -/
noncomputable def baseReciprocal (r : ℕ) : ℝ :=
  1 / baseReal r

/-- The reciprocal of every coded base is strictly positive. -/
theorem baseReciprocal_pos (r : ℕ) :
    0 < baseReciprocal r := by
  exact one_div_pos.mpr (baseReal_pos r)

/-- The reciprocal of every coded base is nonnegative. -/
theorem baseReciprocal_nonneg (r : ℕ) :
    0 ≤ baseReciprocal r :=
  (baseReciprocal_pos r).le

/-- Every physical base is at least two, hence its reciprocal is at most one half. -/
theorem baseReciprocal_le_half (r : ℕ) :
    baseReciprocal r ≤ (1 / 2 : ℝ) := by
  have hbase : (2 : ℝ) ≤ baseReal r := by
    have hcast : (2 : ℝ) ≤ (baseNat r : ℝ) := by
      exact_mod_cast baseNat_ge_two r
    simpa only [baseReal_def] using hcast
  have hinv : 1 / baseReal r ≤ (1 : ℝ) / 2 :=
    one_div_le_one_div_of_le (by norm_num) hbase
  simpa only [baseReciprocal] using hinv

/-- Fraction of camera mass preserved in the return channel. -/
noncomputable def residualFactor (r : ℕ) : ℝ :=
  1 - baseReciprocal r

/-- The return fraction is nonnegative. -/
theorem residualFactor_nonneg (r : ℕ) :
    0 ≤ residualFactor r := by
  dsimp [residualFactor]
  nlinarith [baseReciprocal_le_half r]

/-- At least one half of every camera mass remains in the return channel. -/
theorem residualFactor_half_le (r : ℕ) :
    (1 / 2 : ℝ) ≤ residualFactor r := by
  dsimp [residualFactor]
  nlinarith [baseReciprocal_le_half r]

/-- The return fraction never exceeds one. -/
theorem residualFactor_le_one (r : ℕ) :
    residualFactor r ≤ 1 := by
  dsimp [residualFactor]
  nlinarith [baseReciprocal_nonneg r]

/-- Residual-return event mass `ω_r(n) (1 - 1 / b_r)`. -/
noncomputable def residualEventMass
    (omega : AdmissibleInfinitePartition) (r : ℕ) (n : PNat) : ℝ :=
  omega.weight r n * residualFactor r

/-- Every residual event mass is nonnegative. -/
theorem residualEventMass_nonneg
    (omega : AdmissibleInfinitePartition) (r : ℕ) (n : PNat) :
    0 ≤ residualEventMass omega r n := by
  exact mul_nonneg (omega.weight_nonneg r n) (residualFactor_nonneg r)

/-- Each residual event preserves at least half of its camera weight. -/
theorem residualEventMass_half_weight_le
    (omega : AdmissibleInfinitePartition) (r : ℕ) (n : PNat) :
    (1 / 2 : ℝ) * omega.weight r n ≤ residualEventMass omega r n := by
  calc
    (1 / 2 : ℝ) * omega.weight r n
        ≤ residualFactor r * omega.weight r n :=
      mul_le_mul_of_nonneg_right
        (residualFactor_half_le r) (omega.weight_nonneg r n)
    _ = residualEventMass omega r n := by
      simp [residualEventMass, mul_comm]

/-- Each residual event mass is bounded by its full camera weight. -/
theorem residualEventMass_le_weight
    (omega : AdmissibleInfinitePartition) (r : ℕ) (n : PNat) :
    residualEventMass omega r n ≤ omega.weight r n := by
  simpa only [residualEventMass] using
    mul_le_of_le_one_right
      (omega.weight_nonneg r n) (residualFactor_le_one r)

/-- The residual sector vanishes at the unit seed. -/
@[simp]
theorem residualEventMass_one
    (omega : AdmissibleInfinitePartition) (r : ℕ) :
    residualEventMass omega r (1 : PNat) = 0 := by
  simp [residualEventMass]

/-- Residual event masses are summable over cameras at each number. -/
theorem residualEventMass_summable
    (omega : AdmissibleInfinitePartition) (n : PNat) :
    Summable (fun r => residualEventMass omega r n) := by
  exact Summable.of_nonneg_of_le
    (fun r => residualEventMass_nonneg omega r n)
    (fun r => residualEventMass_le_weight omega r n)
    (omega.weight_summable n)

/-- Total return mass seen by one state coordinate. -/
noncomputable def residualCameraMass
    (omega : AdmissibleInfinitePartition) (n : PNat) : ℝ :=
  ∑' r : ℕ, residualEventMass omega r n

/-- Total residual camera mass is nonnegative. -/
theorem residualCameraMass_nonneg
    (omega : AdmissibleInfinitePartition) (n : PNat) :
    0 ≤ residualCameraMass omega n := by
  exact tsum_nonneg fun r => residualEventMass_nonneg omega r n

/-- The camera-summed residual sector also vanishes at the unit seed. -/
@[simp]
theorem residualCameraMass_one
    (omega : AdmissibleInfinitePartition) :
    residualCameraMass omega (1 : PNat) = 0 := by
  simp [residualCameraMass]

/-- Away from the seed, at least half of the total camera mass returns. -/
theorem residualCameraMass_half_le
    (omega : AdmissibleInfinitePartition) {n : PNat} (hn : n ≠ 1) :
    (1 / 2 : ℝ) ≤ residualCameraMass omega n := by
  calc
    (1 / 2 : ℝ) =
        (1 / 2 : ℝ) * (∑' r : ℕ, omega.weight r n) := by
      rw [omega.weight_tsum_eq_one hn]
      ring
    _ = ∑' r : ℕ, (1 / 2 : ℝ) * omega.weight r n := by
      rw [tsum_mul_left]
    _ ≤ ∑' r : ℕ, residualEventMass omega r n :=
      ((omega.weight_summable n).mul_left (1 / 2 : ℝ)).tsum_le_tsum
        (fun r => residualEventMass_half_weight_le omega r n)
        (residualEventMass_summable omega n)
    _ = residualCameraMass omega n := rfl

/-- No coordinate receives more than unit total residual mass. -/
theorem residualCameraMass_le_one
    (omega : AdmissibleInfinitePartition) (n : PNat) :
    residualCameraMass omega n ≤ 1 := by
  by_cases hn : n = 1
  · subst n
    simp
  · calc
      residualCameraMass omega n
          ≤ ∑' r : ℕ, omega.weight r n :=
        (residualEventMass_summable omega n).tsum_le_tsum
          (fun r => residualEventMass_le_weight omega r n)
          (omega.weight_summable n)
      _ = 1 := omega.weight_tsum_eq_one hn

/-- Square-root residual amplitude. -/
noncomputable def residualAmplitude
    (omega : AdmissibleInfinitePartition) (r : ℕ) (n : PNat) : ℝ :=
  Real.sqrt (residualEventMass omega r n)

/-- Every residual amplitude is nonnegative. -/
theorem residualAmplitude_nonneg
    (omega : AdmissibleInfinitePartition) (r : ℕ) (n : PNat) :
    0 ≤ residualAmplitude omega r n :=
  Real.sqrt_nonneg _

/-- Squaring the amplitude recovers exactly the residual event mass. -/
theorem residualAmplitude_sq
    (omega : AdmissibleInfinitePartition) (r : ℕ) (n : PNat) :
    residualAmplitude omega r n ^ 2 = residualEventMass omega r n :=
  Real.sq_sqrt (residualEventMass_nonneg omega r n)

/-- Pointwise residual coordinate. -/
noncomputable def residualCoordinate
    (omega : AdmissibleInfinitePartition)
    (e : ResidualEvent) (f : State) : ℂ :=
  ((residualAmplitude omega e.2 e.1 : ℝ) : ℂ) * f e.1

/-- A residual coordinate vanishes on the zero state. -/
@[simp]
theorem residualCoordinate_zero
    (omega : AdmissibleInfinitePartition) (e : ResidualEvent) :
    residualCoordinate omega e (0 : State) = 0 := by
  simp [residualCoordinate]

/-- Each residual coordinate is additive in the state. -/
theorem residualCoordinate_add
    (omega : AdmissibleInfinitePartition)
    (e : ResidualEvent) (f g : State) :
    residualCoordinate omega e (f + g) =
      residualCoordinate omega e f + residualCoordinate omega e g := by
  simp [residualCoordinate, mul_add]

/-- Each residual coordinate is complex homogeneous in the state. -/
theorem residualCoordinate_smul
    (omega : AdmissibleInfinitePartition)
    (e : ResidualEvent) (c : ℂ) (f : State) :
    residualCoordinate omega e (c • f) =
      c • residualCoordinate omega e f := by
  simp [residualCoordinate, smul_eq_mul]
  ring

/-- Exact pointwise residual energy. -/
theorem residualCoordinate_normSq_eq
    (omega : AdmissibleInfinitePartition)
    (e : ResidualEvent) (f : State) :
    Complex.normSq (residualCoordinate omega e f) =
      residualEventMass omega e.2 e.1 * Complex.normSq (f e.1) := by
  calc
    Complex.normSq (residualCoordinate omega e f) =
        (residualAmplitude omega e.2 e.1 *
          residualAmplitude omega e.2 e.1) *
          Complex.normSq (f e.1) := by
      rw [residualCoordinate, Complex.normSq_mul, Complex.normSq_ofReal]
    _ = residualEventMass omega e.2 e.1 * Complex.normSq (f e.1) := by
      rw [← pow_two, residualAmplitude_sq]

end GreenFrame.Concrete
