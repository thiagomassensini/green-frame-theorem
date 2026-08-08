import GreenFrame.Concrete.Arithmetic.CanonicalDepthOneCharge

/-!
# Canonical depth-one share of the log-depth activity

The source states the one-third share as the immediate consequence of
`ABGF-AR-003`.  This checkpoint names both the exact decomposition of the
canonical normalizer and that consequence.
-/

open scoped BigOperators

namespace GreenFrame.Concrete

/-- The canonical activity normalizer is the disjoint depth-one/bulk sum. -/
theorem allBaseNormalizer_eq_depthOneActivity_add_bulkActivity (n : ℕ) :
    allBaseNormalizer n = depthOneActivity n + bulkActivity n := by
  classical
  rw [allBaseNormalizer, depthOneActivity, bulkActivity, depthOneBases,
    bulkBases, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hone : positionalDepth b n = 1
  · simp [hone]
  · by_cases hbulk : 2 ≤ positionalDepth b n
    · simp [hone, hbulk]
    · have hzero : positionalDepth b n = 0 := by omega
      simp [allBaseActivity, hzero]

/-- Algebraic one-third consequence of a positive normalizer and the bulk bound. -/
theorem one_third_le_depthOneActivity_div_normalizer_of_bulk_bound
    {n : ℕ} (hpos : 0 < allBaseNormalizer n)
    (hbulk : bulkActivity n ≤ 2 * depthOneActivity n) :
    (1 : ℝ) / 3 ≤ depthOneActivity n / allBaseNormalizer n := by
  rw [le_div_iff₀ hpos,
    allBaseNormalizer_eq_depthOneActivity_add_bulkActivity]
  nlinarith

/-- The canonical depth-one activity carries at least one third of the normalizer. -/
theorem canonical_one_third_le_depthOneActivity_div_normalizer
    {n : ℕ} (hn : 1 < n) :
    (1 : ℝ) / 3 ≤ depthOneActivity n / allBaseNormalizer n :=
  one_third_le_depthOneActivity_div_normalizer_of_bulk_bound
    (allBaseNormalizer_pos hn)
    (canonical_bulkActivity_le_two_mul_depthOneActivity hn)

end GreenFrame.Concrete
