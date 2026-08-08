import GreenFrame.Concrete.Arithmetic.PositionalDepth

/-!
# Infinite all-bases partitions

The base camera is indexed by a natural code r, representing the base
r + 2. State coordinates are positive natural numbers.

Summability is deliberately not a field of AdmissibleInfinitePartition.
It is derived from the arithmetic support condition.
-/

open scoped BigOperators

namespace GreenFrame.Concrete

/-- Natural base represented by camera code r. -/
def baseNat (r : ℕ) : ℕ :=
  r + 2

/-- Every coded base is at least two. -/
theorem baseNat_ge_two (r : ℕ) :
    2 ≤ baseNat r := by
  simp [baseNat]

/-- Every coded base is positive. -/
theorem baseNat_pos (r : ℕ) :
    0 < baseNat r := by
  simp [baseNat]

/-- Positive-natural realization of a coded base. -/
def basePNat (r : ℕ) : PNat :=
  ⟨baseNat r, baseNat_pos r⟩

@[simp]
theorem basePNat_coe (r : ℕ) :
    (basePNat r : ℕ) = baseNat r :=
  rfl

/-- Real realization of a coded base. -/
def baseReal (r : ℕ) : ℝ :=
  (baseNat r : ℝ)

@[simp]
theorem baseReal_def (r : ℕ) :
    baseReal r = (baseNat r : ℝ) :=
  rfl

/-- Real coded bases are strictly positive. -/
theorem baseReal_pos (r : ℕ) :
    0 < baseReal r := by
  unfold baseReal
  exact_mod_cast baseNat_pos r

/-- Real coded bases are nonnegative. -/
theorem baseReal_nonneg (r : ℕ) :
    0 ≤ baseReal r :=
  (baseReal_pos r).le

/-- An infinite Green event consists of a base code and a positive parent. -/
abbrev GreenEvent :=
  ℕ × PNat

/-- State coordinate reached by the event (r,m). -/
def eventNumber (e : GreenEvent) : PNat :=
  basePNat e.1 * e.2

@[simp]
theorem eventNumber_eq (r : ℕ) (m : PNat) :
    eventNumber (r, m) = basePNat r * m :=
  rfl

@[simp]
theorem eventNumber_coe (e : GreenEvent) :
    (eventNumber e : ℕ) = baseNat e.1 * (e.2 : ℕ) := by
  simp [eventNumber]

/--
Finite set containing every camera code that can be active at coordinate
n. The range 0, …, n-2 corresponds exactly to bases 2, …, n.
-/
def cameraCodes (n : PNat) : Finset ℕ :=
  Finset.range ((n : ℕ) - 1)

/-- A positive natural differs from one exactly when its value is above one. -/
theorem pnat_one_lt_iff_ne_one (n : PNat) :
    1 < (n : ℕ) ↔ n ≠ 1 := by
  constructor
  · intro h hEq
    subst n
    norm_num at h
  · intro hn
    have hpos : 0 < (n : ℕ) := n.property
    have hne : (n : ℕ) ≠ 1 := by
      intro hEq
      apply hn
      exact PNat.eq hEq
    omega

/-- Membership in cameraCodes n is equivalent to the coded base lying below n. -/
theorem mem_cameraCodes_iff {r : ℕ} {n : PNat} :
    r ∈ cameraCodes n ↔ baseNat r ≤ (n : ℕ) := by
  simp only [cameraCodes, Finset.mem_range, baseNat]
  have hpos : 0 < (n : ℕ) := n.property
  omega

/-- Reindex the finite code interval r by the corresponding base r + 2. -/
theorem sum_cameraCodes_shift_two (f : ℕ → ℝ) (n : ℕ) :
    (∑ r in Finset.range (n - 1), f (baseNat r)) =
      ∑ b in Finset.Icc 2 n, f b := by
  classical
  refine Finset.sum_bij (fun r _ => baseNat r) ?_ ?_ ?_ ?_
  · intro r hr
    have hr' : r < n - 1 := Finset.mem_range.mp hr
    exact Finset.mem_Icc.mpr
      ⟨baseNat_ge_two r, by
        simp only [baseNat]
        omega⟩
  · intro r₁ _ r₂ _ h
    simp only [baseNat] at h
    omega
  · intro b hb
    obtain ⟨hb₂, hbn⟩ := Finset.mem_Icc.mp hb
    refine ⟨b - 2, Finset.mem_range.mpr ?_, ?_⟩
    · omega
    · simp only [baseNat]
      omega
  · intro r _
    rfl

/--
Admissible infinite all-bases partition.

Only pointwise nonnegativity, arithmetic support, and a finite partition
identity are fields. Finite support, summability, and the infinite-sum
identity are consequences.
-/
structure AdmissibleInfinitePartition where
  weight : ℕ → PNat → ℝ
  weight_nonneg : ∀ r n, 0 ≤ weight r n
  support_dvd :
    ∀ {r : ℕ} {n : PNat},
      weight r n ≠ 0 → basePNat r ∣ n
  finite_sum_eq_one :
    ∀ {n : PNat}, n ≠ 1 →
      ∑ r in cameraCodes n, weight r n = 1

namespace AdmissibleInfinitePartition

/-- A nonzero camera belongs to the explicit finite code interval. -/
theorem mem_cameraCodes_of_weight_ne_zero
    (P : AdmissibleInfinitePartition) {r : ℕ} {n : PNat}
    (h : P.weight r n ≠ 0) :
    r ∈ cameraCodes n := by
  have hle : basePNat r ≤ n :=
    PNat.le_of_dvd (P.support_dvd h)
  have hleNat : (basePNat r : ℕ) ≤ (n : ℕ) :=
    (PNat.coe_le_coe (basePNat r) n).2 hle
  apply mem_cameraCodes_iff.mpr
  simpa only [basePNat_coe] using hleNat

/-- Every camera outside the explicit finite interval has zero weight. -/
theorem weight_eq_zero_of_not_mem_cameraCodes
    (P : AdmissibleInfinitePartition) {r : ℕ} {n : PNat}
    (hr : r ∉ cameraCodes n) :
    P.weight r n = 0 := by
  by_contra h
  exact hr (P.mem_cameraCodes_of_weight_ne_zero h)

/-- The function support is contained in cameraCodes n. -/
theorem weight_support_subset_cameraCodes
    (P : AdmissibleInfinitePartition) (n : PNat) :
    Function.support (fun r => P.weight r n)
      ⊆ (cameraCodes n : Set ℕ) := by
  intro r hr
  change P.weight r n ≠ 0 at hr
  exact P.mem_cameraCodes_of_weight_ne_zero hr

/-- Every coordinate has finitely many nonzero camera weights. -/
theorem weight_hasFiniteSupport
    (P : AdmissibleInfinitePartition) (n : PNat) :
    (fun r => P.weight r n).HasFiniteSupport := by
  change (Function.support (fun r => P.weight r n)).Finite
  exact (cameraCodes n).finite_toSet.subset
    (P.weight_support_subset_cameraCodes n)

/-- Camera weights are summable; this is derived rather than assumed. -/
theorem weight_summable
    (P : AdmissibleInfinitePartition) (n : PNat) :
    Summable (fun r => P.weight r n) := by
  apply summable_of_ne_finset_zero (s := cameraCodes n)
  intro r hr
  exact P.weight_eq_zero_of_not_mem_cameraCodes hr

/-- The infinite camera sum equals one away from the unit seed. -/
theorem weight_tsum_eq_one
    (P : AdmissibleInfinitePartition) {n : PNat} (hn : n ≠ 1) :
    (∑' r : ℕ, P.weight r n) = 1 := by
  calc
    (∑' r : ℕ, P.weight r n) =
        ∑ r in cameraCodes n, P.weight r n := by
      exact tsum_eq_sum (s := cameraCodes n)
        (fun r hr =>
          P.weight_eq_zero_of_not_mem_cameraCodes hr)
    _ = 1 := P.finite_sum_eq_one hn

/-- Every camera weight vanishes at the unit seed. -/
@[simp]
theorem weight_one_eq_zero
    (P : AdmissibleInfinitePartition) (r : ℕ) :
    P.weight r (1 : PNat) = 0 := by
  apply P.weight_eq_zero_of_not_mem_cameraCodes
  simp [cameraCodes]

/-- No admissible infinite camera carries more than unit mass. -/
theorem weight_le_one
    (P : AdmissibleInfinitePartition) (r : ℕ) (n : PNat) :
    P.weight r n ≤ 1 := by
  by_cases hn : n = 1
  · subst n
    simp
  · by_cases hz : P.weight r n = 0
    · simp [hz]
    · have hr : r ∈ cameraCodes n :=
        P.mem_cameraCodes_of_weight_ne_zero hz
      calc
        P.weight r n ≤
            ∑ s in cameraCodes n, P.weight s n := by
          exact Finset.single_le_sum
            (fun s _ => P.weight_nonneg s n) hr
        _ = 1 := P.finite_sum_eq_one hn

end AdmissibleInfinitePartition

/-- Canonical carry weight reindexed by the base code r. -/
noncomputable def carryCameraWeightByCode
    (r : ℕ) (n : PNat) : ℝ :=
  carryCameraWeight (baseNat r) (n : ℕ)

/-- Reindexed canonical weights are nonnegative. -/
theorem carryCameraWeightByCode_nonneg (r : ℕ) (n : PNat) :
    0 ≤ carryCameraWeightByCode r n := by
  simpa only [carryCameraWeightByCode] using
    carryCameraWeight_nonneg (baseNat r) (n : ℕ)

/-- Nonzero reindexed canonical weights are genuine positive divisibility events. -/
theorem carryCameraWeightByCode_support_dvd
    {r : ℕ} {n : PNat}
    (h : carryCameraWeightByCode r n ≠ 0) :
    basePNat r ∣ n := by
  have hs := carryCameraWeight_support
    (b := baseNat r) (n := (n : ℕ))
    (by simpa only [carryCameraWeightByCode] using h)
  apply PNat.dvd_iff.mpr
  simpa only [basePNat_coe] using hs.2.2.2

/-- The finite reindexed canonical weights form a partition of unity. -/
theorem carryCameraWeightByCode_finite_sum_eq_one
    {n : PNat} (hn : n ≠ 1) :
    ∑ r in cameraCodes n, carryCameraWeightByCode r n = 1 := by
  calc
    (∑ r in cameraCodes n, carryCameraWeightByCode r n) =
        ∑ b in Finset.Icc 2 (n : ℕ),
          carryCameraWeight b (n : ℕ) := by
      simpa only [cameraCodes, carryCameraWeightByCode] using
        sum_cameraCodes_shift_two
          (fun b => carryCameraWeight b (n : ℕ)) (n : ℕ)
    _ = 1 :=
      carryCameraWeight_sum_eq_one
        ((pnat_one_lt_iff_ne_one n).2 hn)

/--
Canonical admissible infinite partition obtained from the positional
log-depth carry weights.
-/
noncomputable def canonicalCarryInfinitePartition :
    AdmissibleInfinitePartition where
  weight := carryCameraWeightByCode
  weight_nonneg := carryCameraWeightByCode_nonneg
  support_dvd := carryCameraWeightByCode_support_dvd
  finite_sum_eq_one := carryCameraWeightByCode_finite_sum_eq_one

@[simp]
theorem canonicalCarryInfinitePartition_weight
    (r : ℕ) (n : PNat) :
    canonicalCarryInfinitePartition.weight r n =
      carryCameraWeight (baseNat r) (n : ℕ) :=
  rfl

end GreenFrame.Concrete
