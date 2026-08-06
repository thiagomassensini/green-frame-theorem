import Mathlib

/-!
# Admissible finite camera partitions

This module isolates the only abstract arithmetic input needed by the frame
argument: nonnegative camera weights whose total mass is one.
-/

namespace GreenFrame

/-- A finite family of nonnegative camera weights with total mass one. -/
structure AdmissibleCameraPartition (ι : Type*) [Fintype ι] where
  weight : ι → ℝ
  nonneg : ∀ i, 0 ≤ weight i
  sum_eq_one : ∑ i, weight i = 1

namespace AdmissibleCameraPartition

variable {ι : Type*} [Fintype ι] (ω : AdmissibleCameraPartition ι)

/-- Every admissible camera weight is nonnegative. -/
theorem admissible_weight_nonneg (i : ι) : 0 ≤ ω.weight i :=
  ω.nonneg i

/-- The admissible weights sum to one. -/
theorem admissible_weight_sum_eq_one : ∑ i, ω.weight i = 1 :=
  ω.sum_eq_one

/-- No individual camera can carry more than the full unit mass. -/
theorem admissible_weight_le_one (i : ι) : ω.weight i ≤ 1 := by
  classical
  calc
    ω.weight i ≤ ∑ j, ω.weight j := by
      exact Finset.single_le_sum (fun j _ => ω.nonneg j) (Finset.mem_univ i)
    _ = 1 := ω.sum_eq_one

/-- The finite support used by the abstract atlas. -/
noncomputable def support : Finset ι :=
  Finset.univ.filter fun i => ω.weight i ≠ 0

/-- Membership in the support is exactly nonvanishing of the weight. -/
theorem mem_support_iff (i : ι) : i ∈ ω.support ↔ ω.weight i ≠ 0 := by
  simp [support]

/-- Outside the support the camera weight vanishes. -/
theorem admissible_weight_eq_zero_of_not_mem_support {i : ι}
    (hi : i ∉ ω.support) : ω.weight i = 0 := by
  by_contra hne
  exact hi ((ω.mem_support_iff i).2 hne)

end AdmissibleCameraPartition

end GreenFrame
