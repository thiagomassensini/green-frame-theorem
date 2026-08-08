import Mathlib

/-!
# Concrete positional depth and canonical all-bases weights

This module is the arithmetic foundation of the concrete Green-frame realization.
Bases are arbitrary natural numbers at least two; no primality hypothesis is used.
The positional depth is Mathlib's maximal-power divisor `padicValNat`.
-/

namespace GreenFrame.Concrete

/-- Positive integer state indices. -/
abbrev PositiveIndex := {n : ℕ // 0 < n}

/-- Positional bases, including composite bases. -/
abbrev PositionalBase := {b : ℕ // 2 ≤ b}

/-- A genuine vertical event `(b,n)` with `b ≥ 2`, `n > 0`, and `b ∣ n`. -/
structure BaseEvent where
  base : ℕ
  number : ℕ
  base_ge_two : 2 ≤ base
  number_pos : 0 < number
  divides : base ∣ number
deriving DecidableEq

/-- Maximal `k` such that `b^k ∣ n`; valid for prime and composite bases. -/
def positionalDepth (b n : ℕ) : ℕ :=
  padicValNat b n

/-- Positive positional depth is exactly divisibility by the base. -/
theorem positionalDepth_pos_iff_dvd {b n : ℕ} (hb : 2 ≤ b) (hn : 0 < n) :
    0 < positionalDepth b n ↔ b ∣ n := by
  change 0 < padicValNat b n ↔ b ∣ n
  rw [show b ∣ n ↔ b ^ 1 ∣ n by simp,
    pow_dvd_iff_le_padicValNat (by omega) (Nat.ne_of_gt hn)]
  omega

/-- Outside a vertical event the positional depth is zero. -/
theorem positionalDepth_eq_zero_of_not_dvd {b n : ℕ} (hb : 2 ≤ b) (hn : 0 < n)
    (hnd : ¬ b ∣ n) :
    positionalDepth b n = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hpos
  exact hnd ((positionalDepth_pos_iff_dvd hb hn).1 hpos)

/-- The maximal depth power divides the number. -/
theorem positionalDepth_pow_dvd (b n : ℕ) :
    b ^ positionalDepth b n ∣ n := by
  exact pow_padicValNat_dvd

/-- The next power does not divide a positive number. -/
theorem positionalDepth_succ_pow_not_dvd {b n : ℕ} (hb : 2 ≤ b) (hn : 0 < n) :
    ¬ b ^ (positionalDepth b n + 1) ∣ n := by
  rw [pow_dvd_iff_le_padicValNat (by omega) (Nat.ne_of_gt hn)]
  simp [positionalDepth]

/-- A base sees itself at exactly depth one. -/
@[simp]
theorem positionalDepth_self {b : ℕ} (hb : 2 ≤ b) :
    positionalDepth b b = 1 := by
  simpa [positionalDepth] using padicValNat_base (by omega : 1 < b)

/-- Every base has depth zero at the unit seed. -/
@[simp]
theorem positionalDepth_one (b : ℕ) :
    positionalDepth b 1 = 0 := by
  simp [positionalDepth]

/-- Any active positional base lies below the number it sees. -/
theorem active_base_le_number {b n : ℕ} (hn : 0 < n) (hdiv : b ∣ n) :
    b ≤ n :=
  Nat.le_of_dvd hn hdiv

/-- Log-depth activity of camera `b` at number `n`. -/
noncomputable def allBaseActivity (b n : ℕ) : ℝ :=
  (positionalDepth b n : ℝ) * Real.log (b : ℝ)

/-- Log-depth activity is nonnegative on positional bases. -/
theorem allBaseActivity_nonneg {b n : ℕ} (hb : 2 ≤ b) :
    0 ≤ allBaseActivity b n := by
  unfold allBaseActivity
  exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ b by omega)))

/-- Nondividing cameras have zero activity. -/
theorem allBaseActivity_eq_zero_of_not_dvd {b n : ℕ} (hb : 2 ≤ b) (hn : 0 < n)
    (hnd : ¬ b ∣ n) :
    allBaseActivity b n = 0 := by
  simp [allBaseActivity, positionalDepth_eq_zero_of_not_dvd hb hn hnd]

/-- The self-camera activity is exactly `log n`. -/
theorem allBaseActivity_self {n : ℕ} (hn : 2 ≤ n) :
    allBaseActivity n n = Real.log (n : ℝ) := by
  simp [allBaseActivity, positionalDepth_self hn]

/-- Finite normalizer for all positional bases active at `n`. -/
noncomputable def allBaseNormalizer (n : ℕ) : ℝ :=
  ∑ b ∈ Finset.Icc 2 n, allBaseActivity b n

/-- The all-bases normalizer is strictly positive for every `n > 1`. -/
theorem allBaseNormalizer_pos {n : ℕ} (hn : 1 < n) :
    0 < allBaseNormalizer n := by
  classical
  unfold allBaseNormalizer
  apply Finset.sum_pos'
  · intro b hbmem
    exact allBaseActivity_nonneg (Finset.mem_Icc.mp hbmem).1
  · refine ⟨n, Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩, ?_⟩
    rw [allBaseActivity_self (by omega)]
    exact Real.log_pos (by exact_mod_cast hn)

/-- Canonical log-depth carry weight. It vanishes off the finite camera interval. -/
noncomputable def carryCameraWeight (b n : ℕ) : ℝ :=
  if 1 < n ∧ 2 ≤ b ∧ b ≤ n then
    allBaseActivity b n / allBaseNormalizer n
  else
    0

/-- Canonical carry weights are nonnegative. -/
theorem carryCameraWeight_nonneg (b n : ℕ) :
    0 ≤ carryCameraWeight b n := by
  classical
  unfold carryCameraWeight
  split_ifs with h
  · exact div_nonneg (allBaseActivity_nonneg h.2.1)
      (allBaseNormalizer_pos h.1).le
  · exact le_rfl

/-- A nondividing camera has zero canonical weight. -/
theorem carryCameraWeight_eq_zero_of_not_dvd {b n : ℕ} (hn : 0 < n)
    (hnd : ¬ b ∣ n) :
    carryCameraWeight b n = 0 := by
  classical
  unfold carryCameraWeight
  split_ifs with h
  · rw [allBaseActivity_eq_zero_of_not_dvd h.2.1 hn hnd]
    simp
  · rfl

/-- A nonzero canonical camera is a genuine finite vertical event. -/
theorem carryCameraWeight_support {b n : ℕ}
    (h : carryCameraWeight b n ≠ 0) :
    1 < n ∧ 2 ≤ b ∧ b ≤ n ∧ b ∣ n := by
  classical
  have hn : 1 < n ∧ 2 ≤ b ∧ b ≤ n := by
    by_contra hbad
    simp [carryCameraWeight, hbad] at h
  refine ⟨hn.1, hn.2.1, hn.2.2, ?_⟩
  by_contra hnd
  exact h (carryCameraWeight_eq_zero_of_not_dvd (by omega) hnd)

/-- The canonical all-bases weights form a partition of unity at every `n > 1`. -/
theorem carryCameraWeight_sum_eq_one {n : ℕ} (hn : 1 < n) :
    ∑ b ∈ Finset.Icc 2 n, carryCameraWeight b n = 1 := by
  classical
  calc
    ∑ b ∈ Finset.Icc 2 n, carryCameraWeight b n =
        ∑ b ∈ Finset.Icc 2 n, allBaseActivity b n / allBaseNormalizer n := by
          apply Finset.sum_congr rfl
          intro b hbmem
          rw [carryCameraWeight]
          simp [hn, (Finset.mem_Icc.mp hbmem).1, (Finset.mem_Icc.mp hbmem).2]
    _ = allBaseNormalizer n / allBaseNormalizer n := by
          rw [Finset.sum_div]
          rfl
    _ = 1 := div_self (allBaseNormalizer_pos hn).ne'

end GreenFrame.Concrete
