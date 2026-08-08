import GreenFrame.Concrete.Analysis.HorizontalResolutionSubspace

/-!
# Off-base elementary-atlas energy

This checkpoint removes one elementary camera row and records the two boundary
indices explicitly: the selected row is zero by definition, and every camera
weight is zero at the seed `n = 1`.
-/

open scoped ENNReal lp

namespace GreenFrame.Concrete

/-- Energy after deleting the elementary camera with code `r`. -/
noncomputable def offBaseAtlasEnergyTerm
    (omega : AdmissibleInfinitePartition) (r : ℕ) (f : State)
    (e : ElementaryAtlasEvent) : ℝ :=
  if e.2 = r then 0
  else omega.weight e.2 e.1 * Complex.normSq (f e.1)

/-- Every off-base elementary-atlas energy term is nonnegative. -/
theorem offBaseAtlasEnergyTerm_nonneg
    (omega : AdmissibleInfinitePartition) (r : ℕ) (f : State)
    (e : ElementaryAtlasEvent) :
    0 ≤ offBaseAtlasEnergyTerm omega r f e := by
  by_cases h : e.2 = r
  · simp [offBaseAtlasEnergyTerm, h]
  · simp only [offBaseAtlasEnergyTerm, h, if_false]
    exact mul_nonneg (omega.weight_nonneg _ _) (Complex.normSq_nonneg _)

/-- Deleting one camera row can only decrease elementary-atlas energy. -/
theorem offBaseAtlasEnergyTerm_le
    (omega : AdmissibleInfinitePartition) (r : ℕ) (f : State)
    (e : ElementaryAtlasEvent) :
    offBaseAtlasEnergyTerm omega r f e ≤
      elementaryAtlasEnergyTerm omega f e := by
  by_cases h : e.2 = r
  · simp only [offBaseAtlasEnergyTerm, elementaryAtlasEnergyTerm,
      h, if_pos]
    exact mul_nonneg (omega.weight_nonneg _ _)
      (Complex.normSq_nonneg _)
  · simp [offBaseAtlasEnergyTerm, elementaryAtlasEnergyTerm, h]

/-- Off-base elementary-atlas energy is summable. -/
theorem offBaseAtlasEnergyTerm_summable
    (omega : AdmissibleInfinitePartition) (r : ℕ) (f : State) :
    Summable (fun e : ElementaryAtlasEvent =>
      offBaseAtlasEnergyTerm omega r f e) := by
  exact Summable.of_nonneg_of_le
    (fun e => offBaseAtlasEnergyTerm_nonneg omega r f e)
    (fun e => offBaseAtlasEnergyTerm_le omega r f e)
    (elementaryAtlasEnergyTerm_summable omega f)

/-- The deleted elementary-camera row is identically zero. -/
@[simp]
theorem offBaseAtlasEnergyTerm_ownCamera_eq_zero
    (omega : AdmissibleInfinitePartition) (r : ℕ) (f : State)
    (n : PNat) :
    offBaseAtlasEnergyTerm omega r f (n, r) = 0 := by
  simp [offBaseAtlasEnergyTerm]

/-- Camera energy has no seed contribution, also after deleting one row. -/
@[simp]
theorem offBaseAtlasEnergyTerm_seed_eq_zero
    (omega : AdmissibleInfinitePartition) (r s : ℕ) (f : State) :
    offBaseAtlasEnergyTerm omega r f ((1 : PNat), s) = 0 := by
  simp [offBaseAtlasEnergyTerm]

/-- On a horizontal state, deleting the own-base row changes no energy. -/
theorem elementaryAtlasEnergyTerm_eq_offBase_on_horizontal
    (omega : AdmissibleInfinitePartition) (r : ℕ)
    (f : horizontalState r) (e : ElementaryAtlasEvent) :
    elementaryAtlasEnergyTerm omega (f : State) e =
      offBaseAtlasEnergyTerm omega r (f : State) e := by
  rcases e with ⟨n, s⟩
  by_cases hcode : s = r
  · subst s
    simp only [offBaseAtlasEnergyTerm, if_pos]
    by_cases hw : omega.weight r n = 0
    · simp [elementaryAtlasEnergyTerm, hw]
    · have hdvd : basePNat r ∣ n := omega.support_dvd hw
      have hfzero : (f : State) n = 0 :=
        horizontalState_vanishes_on_base r f n hdvd
      simp [elementaryAtlasEnergyTerm, hfzero]
  · simp [elementaryAtlasEnergyTerm, offBaseAtlasEnergyTerm, hcode]

end GreenFrame.Concrete
