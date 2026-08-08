import GreenFrame.Concrete.Analysis.ElementaryAtlasCoordinates

/-!
# Elementary atlas: Tonelli and summability

Second checkpoint for `ABGF-AN-001`: camera density, product summability, and
summability of the literal coordinate norm squares.
-/

open scoped ENNReal lp

namespace GreenFrame.Concrete

/-- Camera-summed elementary energy at one state coordinate. -/
noncomputable def elementaryAtlasCameraDensity
    (omega : AdmissibleInfinitePartition) (f : State) (n : PNat) : ℝ :=
  ∑' r : ℕ, omega.weight r n * Complex.normSq (f n)

/-- Camera density is zero at the seed and equals state density elsewhere. -/
theorem elementaryAtlasCameraDensity_eq
    (omega : AdmissibleInfinitePartition) (f : State) (n : PNat) :
    elementaryAtlasCameraDensity omega f n =
      if n = 1 then 0 else Complex.normSq (f n) := by
  by_cases hn : n = 1
  · subst n
    simp [elementaryAtlasCameraDensity]
  · simp only [elementaryAtlasCameraDensity, tsum_mul_right,
      omega.weight_tsum_eq_one hn, one_mul, if_false, hn]

/-- Camera-summed elementary density is nonnegative. -/
theorem elementaryAtlasCameraDensity_nonneg
    (omega : AdmissibleInfinitePartition) (f : State) (n : PNat) :
    0 ≤ elementaryAtlasCameraDensity omega f n := by
  rw [elementaryAtlasCameraDensity_eq]
  split_ifs
  · exact le_rfl
  · exact Complex.normSq_nonneg _

/-- Camera-summed elementary density is dominated by state density. -/
theorem elementaryAtlasCameraDensity_le
    (omega : AdmissibleInfinitePartition) (f : State) (n : PNat) :
    elementaryAtlasCameraDensity omega f n ≤ Complex.normSq (f n) := by
  rw [elementaryAtlasCameraDensity_eq]
  split_ifs
  · exact Complex.normSq_nonneg _
  · exact le_rfl

/-- The elementary camera density is summable over state coordinates. -/
theorem elementaryAtlasCameraDensity_summable
    (omega : AdmissibleInfinitePartition) (f : State) :
    Summable (fun n => elementaryAtlasCameraDensity omega f n) := by
  exact Summable.of_nonneg_of_le
    (fun n => elementaryAtlasCameraDensity_nonneg omega f n)
    (fun n => elementaryAtlasCameraDensity_le omega f n)
    (residualL2_normSq_summable f)

/-- Tonelli summability of all elementary camera energies. -/
theorem elementaryAtlasEnergyTerm_summable
    (omega : AdmissibleInfinitePartition) (f : State) :
    Summable (fun e : ElementaryAtlasEvent =>
      elementaryAtlasEnergyTerm omega f e) := by
  refine (summable_prod_of_nonneg
    (fun e => elementaryAtlasEnergyTerm_nonneg omega f e)).2 ?_
  constructor
  · intro n
    simpa only [elementaryAtlasEnergyTerm] using
      (omega.weight_summable n).mul_right (Complex.normSq (f n))
  · simpa only [elementaryAtlasEnergyTerm,
      elementaryAtlasCameraDensity] using
      elementaryAtlasCameraDensity_summable omega f

/-- Literal elementary-atlas coordinate norm squares are summable. -/
theorem elementaryAtlasCoordinate_normSq_summable
    (omega : AdmissibleInfinitePartition) (f : State) :
    Summable (fun e : ElementaryAtlasEvent =>
      Complex.normSq (elementaryAtlasCoordinate omega e f)) := by
  exact (elementaryAtlasEnergyTerm_summable omega f).congr fun e =>
    (elementaryAtlasCoordinate_normSq_eq omega e f).symm

end GreenFrame.Concrete
