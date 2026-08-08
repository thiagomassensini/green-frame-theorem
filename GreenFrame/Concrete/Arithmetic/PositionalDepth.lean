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
    Nat.pow_dvd_iff_le_padicValNat (by omega) (Nat.ne_of_gt hn)]
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
  rw [Nat.pow_dvd_iff_le_padicValNat (by omega) (Nat.ne_of_gt hn)]
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
          rw [← Finset.sum_div]
          rfl
    _ = 1 := div_self (allBaseNormalizer_pos hn).ne'

/-! ## Admissible all-bases partitions and exact `(2,4)` witness -/

/--
Abstract arithmetic interface consumed by the concrete frame layer.

Every nonzero coefficient is a genuine divisibility event, and the finite
camera interval is a partition of unity for every non-seed coordinate.
-/
structure AdmissiblePartition where
  weight : ℕ → ℕ → ℝ
  nonneg : ∀ b n, 0 ≤ weight b n
  support_event :
    ∀ {b n}, weight b n ≠ 0 →
      2 ≤ b ∧ 0 < n ∧ b ∣ n
  sum_eq_one :
    ∀ {n}, 1 < n →
      ∑ b ∈ Finset.Icc 2 n, weight b n = 1

namespace AdmissiblePartition

/-- The support at `n` lies in the finite all-bases camera interval. -/
theorem support_subset_Icc
    (ω : AdmissiblePartition) (n : ℕ) :
    Function.support (fun b => ω.weight b n)
      ⊆ (Finset.Icc 2 n : Set ℕ) := by
  intro b hb
  change ω.weight b n ≠ 0 at hb
  obtain ⟨hbase, hnum, hdvd⟩ := ω.support_event hb
  exact Finset.mem_Icc.mpr
    ⟨hbase, active_base_le_number hnum hdvd⟩

/-- Every coordinate has only finitely many nonzero cameras. -/
theorem support_finite
    (ω : AdmissiblePartition) (n : ℕ) :
    (Function.support (fun b => ω.weight b n)).Finite :=
  (Finset.Icc 2 n).finite_toSet.subset
    (ω.support_subset_Icc n)

/-- No admissible camera carries more than the full unit mass. -/
theorem weight_le_one
    (ω : AdmissiblePartition) (b n : ℕ) :
    ω.weight b n ≤ 1 := by
  by_cases hz : ω.weight b n = 0
  · simp [hz]
  · obtain ⟨hbase, hnum, hdvd⟩ := ω.support_event hz
    have hbn : b ≤ n := active_base_le_number hnum hdvd
    have hn : 1 < n := by omega
    have hmem : b ∈ Finset.Icc 2 n :=
      Finset.mem_Icc.mpr ⟨hbase, hbn⟩
    calc
      ω.weight b n ≤
          ∑ c ∈ Finset.Icc 2 n, ω.weight c n := by
        exact Finset.single_le_sum
          (fun c _ => ω.nonneg c n) hmem
      _ = 1 := ω.sum_eq_one hn

/-- The literal finite-support sum over every natural base equals one. -/
theorem finsum_eq_one
    (ω : AdmissiblePartition) {n : ℕ} (hn : 1 < n) :
    (∑ᶠ b : ℕ, ω.weight b n) = 1 := by
  rw [finsum_eq_sum_of_support_subset _
    (ω.support_subset_Icc n)]
  exact ω.sum_eq_one hn

end AdmissiblePartition

/-- Canonical admissible partition produced by the log-depth carry weights. -/
noncomputable def carryPartition : AdmissiblePartition where
  weight := carryCameraWeight
  nonneg := carryCameraWeight_nonneg
  support_event := by
    intro b n h
    obtain ⟨hn, hb, _hbn, hdvd⟩ :=
      carryCameraWeight_support h
    exact ⟨hb, by omega, hdvd⟩
  sum_eq_one := by
    intro n hn
    exact carryCameraWeight_sum_eq_one hn

/-- Canonical carry-camera support is finite at every coordinate. -/
theorem carryCameraWeight_support_finite (n : ℕ) :
    (Function.support (fun b => carryCameraWeight b n)).Finite := by
  simpa [carryPartition] using
    (AdmissiblePartition.support_finite carryPartition n)

/-- Canonical weights sum to one over literally all natural bases. -/
theorem carryCameraWeight_finsum_eq_one {n : ℕ} (hn : 1 < n) :
    (∑ᶠ b : ℕ, carryCameraWeight b n) = 1 := by
  simpa [carryPartition] using
    (AdmissiblePartition.finsum_eq_one carryPartition hn)

/-- Green-transmitted mass `ω_b(n)/b`. -/
noncomputable def greenMass
    (ω : AdmissiblePartition) (b n : ℕ) : ℝ :=
  ω.weight b n / (b : ℝ)

/-- Residual/return mass `ω_b(n)(1-1/b)`. -/
noncomputable def residualMass
    (ω : AdmissiblePartition) (b n : ℕ) : ℝ :=
  ω.weight b n * (1 - 1 / (b : ℝ))

/-- Exact pointwise conservative split `μ_G + μ_R = ω`. -/
theorem greenMass_add_residualMass
    (ω : AdmissiblePartition) (b n : ℕ) :
    greenMass ω b n + residualMass ω b n =
      ω.weight b n := by
  unfold greenMass residualMass
  ring

/-! ### Composite-base regressions -/

/-- The composite camera `4` sees `64=4³` at depth three. -/
theorem positionalDepth_four_sixtyFour :
    positionalDepth 4 64 = 3 := by
  change padicValNat 4 64 = 3
  apply Nat.le_antisymm
  · have hnext : ¬4 ^ 4 ∣ 64 := by norm_num
    have hnot : ¬4 ≤ padicValNat 4 64 := by
      intro hle
      exact hnext <|
        (Nat.pow_dvd_iff_le_padicValNat
          (by norm_num) (by norm_num)).2 hle
    omega
  · exact
      (Nat.pow_dvd_iff_le_padicValNat
        (by norm_num) (by norm_num)).1 (by norm_num)

/-! ### Exact `(2,4)` arithmetic witness -/

theorem positionalDepth_two_four :
    positionalDepth 2 4 = 2 := by
  change padicValNat 2 4 = 2
  apply Nat.le_antisymm
  · have hnext : ¬2 ^ 3 ∣ 4 := by norm_num
    have hnot : ¬3 ≤ padicValNat 2 4 := by
      intro hle
      exact hnext <|
        (Nat.pow_dvd_iff_le_padicValNat
          (by norm_num) (by norm_num)).2 hle
    omega
  · exact
      (Nat.pow_dvd_iff_le_padicValNat
        (by norm_num) (by norm_num)).1 (by norm_num)

theorem positionalDepth_three_four :
    positionalDepth 3 4 = 0 := by
  exact positionalDepth_eq_zero_of_not_dvd
    (b := 3) (n := 4) (by norm_num) (by norm_num) (by norm_num)

theorem positionalDepth_four_four :
    positionalDepth 4 4 = 1 := by
  exact positionalDepth_self (b := 4) (by norm_num)

theorem allBaseActivity_two_four :
    allBaseActivity 2 4 = 2 * Real.log (2 : ℝ) := by
  simp [allBaseActivity, positionalDepth_two_four]

theorem allBaseActivity_three_four :
    allBaseActivity 3 4 = 0 := by
  simp [allBaseActivity, positionalDepth_three_four]

theorem allBaseActivity_four_four :
    allBaseActivity 4 4 = 2 * Real.log (2 : ℝ) := by
  rw [allBaseActivity_self (by norm_num)]
  calc
    Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) := by norm_num
    _ = 2 * Real.log (2 : ℝ) := Real.log_pow (2 : ℝ) 2

/-- At `n=4`, only bases `2` and `4` contribute equal activity. -/
theorem allBaseNormalizer_four :
    allBaseNormalizer 4 = 4 * Real.log (2 : ℝ) := by
  have hIcc :
      Finset.Icc 2 4 = ({2, 3, 4} : Finset ℕ) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  unfold allBaseNormalizer
  rw [hIcc]
  simp [allBaseActivity_two_four,
    allBaseActivity_three_four,
    allBaseActivity_four_four] <;> ring

/-- Exact canonical witness `ω₂(4)=1/2`. -/
theorem carryCameraWeight_two_four :
    carryCameraWeight 2 4 = (1 : ℝ) / 2 := by
  have hguard :
      (1 : ℕ) < 4 ∧ 2 ≤ 2 ∧ 2 ≤ 4 := by
    norm_num
  have hlog2 : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num)).ne'
  simp only [carryCameraWeight, hguard]
  rw [allBaseActivity_two_four, allBaseNormalizer_four]
  rw [mul_div_mul_right (2 : ℝ) 4 hlog2]
  norm_num

/-- The inactive base `3` has zero weight at `4`. -/
theorem carryCameraWeight_three_four :
    carryCameraWeight 3 4 = 0 := by
  exact carryCameraWeight_eq_zero_of_not_dvd
    (b := 3) (n := 4) (by norm_num) (by norm_num)

/-- The composite camera receives the complementary half. -/
theorem carryCameraWeight_four_four :
    carryCameraWeight 4 4 = (1 : ℝ) / 2 := by
  have hguard :
      (1 : ℕ) < 4 ∧ 2 ≤ 4 ∧ 4 ≤ 4 := by
    norm_num
  have hlog2 : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num)).ne'
  simp only [carryCameraWeight, hguard]
  rw [allBaseActivity_four_four, allBaseNormalizer_four]
  rw [mul_div_mul_right (2 : ℝ) 4 hlog2]
  norm_num

/-- Exact Green-transmitted mass `μ_G(2,4)=1/4`. -/
theorem greenMass_two_four :
    greenMass carryPartition 2 4 = (1 : ℝ) / 4 := by
  change carryCameraWeight 2 4 / (2 : ℝ) = (1 : ℝ) / 4
  rw [carryCameraWeight_two_four]
  norm_num

/-- Exact residual/return mass `μ_R(2,4)=1/4`. -/
theorem residualMass_two_four :
    residualMass carryPartition 2 4 = (1 : ℝ) / 4 := by
  change
    carryCameraWeight 2 4 * (1 - 1 / (2 : ℝ)) =
      (1 : ℝ) / 4
  rw [carryCameraWeight_two_four]
  norm_num

/-- Bundled kernel witness for the canonical bulk event `(b,n)=(2,4)`. -/
theorem twoFourCarryWitness :
    positionalDepth 2 4 = 2 ∧
    allBaseNormalizer 4 = 4 * Real.log (2 : ℝ) ∧
    carryCameraWeight 2 4 = (1 : ℝ) / 2 ∧
    carryCameraWeight 4 4 = (1 : ℝ) / 2 ∧
    greenMass carryPartition 2 4 = (1 : ℝ) / 4 ∧
    residualMass carryPartition 2 4 = (1 : ℝ) / 4 :=
  ⟨positionalDepth_two_four,
    allBaseNormalizer_four,
    carryCameraWeight_two_four,
    carryCameraWeight_four_four,
    greenMass_two_four,
    residualMass_two_four⟩
end GreenFrame.Concrete
