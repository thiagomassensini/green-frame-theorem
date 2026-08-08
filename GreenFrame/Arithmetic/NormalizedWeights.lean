import GreenFrame.Arithmetic.AdmissiblePartition

/-!
# Normalization of nonnegative finite activities
-/

namespace GreenFrame

section NormalizedWeights

variable {ι : Type*}

/-- Total activity on a finite family. -/
def activityNormalizer (s : Finset ι) (activity : ι → ℝ) : ℝ :=
  s.sum activity

/-- Normalize an activity on `s`, and put zero outside `s`. -/
noncomputable def normalizedWeight [DecidableEq ι]
    (s : Finset ι) (activity : ι → ℝ) (i : ι) : ℝ :=
  if i ∈ s then activity i / activityNormalizer s activity else 0

/-- A nonnegative activity has a nonnegative normalizer. -/
theorem activityNormalizer_nonneg (s : Finset ι) (activity : ι → ℝ)
    (hactivity : ∀ i ∈ s, 0 ≤ activity i) :
    0 ≤ activityNormalizer s activity := by
  simpa [activityNormalizer] using Finset.sum_nonneg hactivity

/-- Every normalized weight is nonnegative. -/
theorem normalizedWeight_nonneg [DecidableEq ι]
    (s : Finset ι) (activity : ι → ℝ)
    (hactivity : ∀ i ∈ s, 0 ≤ activity i)
    (hpos : 0 < activityNormalizer s activity) (i : ι) :
    0 ≤ normalizedWeight s activity i := by
  by_cases hi : i ∈ s
  · simp [normalizedWeight, hi, div_nonneg (hactivity i hi) hpos.le]
  · simp [normalizedWeight, hi]

/-- The normalized weight is zero outside the active family. -/
theorem normalizedWeight_eq_zero_of_not_mem [DecidableEq ι]
    (s : Finset ι) (activity : ι → ℝ) {i : ι} (hi : i ∉ s) :
    normalizedWeight s activity i = 0 := by
  simp [normalizedWeight, hi]

/-- Normalized nonnegative activities form a partition of unity. -/
theorem normalizedWeight_sum_eq_one [DecidableEq ι]
    (s : Finset ι) (activity : ι → ℝ)
    (hpos : 0 < activityNormalizer s activity) :
    s.sum (fun i => normalizedWeight s activity i) = 1 := by
  calc
    s.sum (fun i => normalizedWeight s activity i) =
        s.sum (fun i => activity i / activityNormalizer s activity) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [normalizedWeight, hi]
    _ = 1 := by
      rw [← Finset.sum_div]
      exact div_self hpos.ne'

/-- Every normalized weight is at most one. -/
theorem normalizedWeight_le_one [DecidableEq ι]
    (s : Finset ι) (activity : ι → ℝ)
    (hactivity : ∀ i ∈ s, 0 ≤ activity i)
    (hpos : 0 < activityNormalizer s activity) {i : ι} (hi : i ∈ s) :
    normalizedWeight s activity i ≤ 1 := by
  have hle : activity i ≤ activityNormalizer s activity := by
    simpa [activityNormalizer] using Finset.single_le_sum hactivity hi
  simp only [normalizedWeight, hi, if_true]
  rw [div_le_iff₀ hpos]
  simpa using hle

end NormalizedWeights

end GreenFrame
