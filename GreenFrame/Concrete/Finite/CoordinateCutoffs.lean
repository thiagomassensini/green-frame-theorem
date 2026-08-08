import GreenFrame.Concrete.Analysis.ConcreteSplitAnalysis

/-!
# Coordinate cutoffs for concrete finite sections

This checkpoint fixes the exact masks used by `T_N`.  It deliberately does
not identify the historical scalar theorem `uniform_section_bounds` with a
finite operator.
-/

open scoped ENNReal lp

namespace GreenFrame.Concrete

/-- State coordinates retained at cutoff `N`. -/
def stateIndexRetained (N : ℕ) (n : PNat) : Prop :=
  (n : ℕ) ≤ N

instance stateIndexRetainedDecidable (N : ℕ) (n : PNat) :
    Decidable (stateIndexRetained N n) := by unfold stateIndexRetained; infer_instance

/-- Residual rows retained at cutoff `N`. -/
def residualEventRetained (N : ℕ) (e : ResidualEvent) : Prop :=
  (e.1 : ℕ) ≤ N ∧ baseNat e.2 ≤ N

instance residualEventRetainedDecidable (N : ℕ) (e : ResidualEvent) :
    Decidable (residualEventRetained N e) := by unfold residualEventRetained; infer_instance

/-- Green rows retained at cutoff `N`. -/
def greenEventRetained (N : ℕ) (e : GreenEvent) : Prop :=
  (eventNumber e : ℕ) ≤ N ∧ baseNat e.1 ≤ N

instance greenEventRetainedDecidable (N : ℕ) (e : GreenEvent) :
    Decidable (greenEventRetained N e) := by unfold greenEventRetained; infer_instance

/-- Literal depth-one rows retained by the finite Green cutoff. -/
def depthOneEventRetained (N : ℕ) (e : DepthOneGreenEvent) : Prop :=
  greenEventRetained N e.1

instance depthOneEventRetainedDecidable (N : ℕ) (e : DepthOneGreenEvent) :
    Decidable (depthOneEventRetained N e) := by unfold depthOneEventRetained; infer_instance

/-- Literal bulk rows retained by the finite Green cutoff. -/
def bulkEventRetained (N : ℕ) (e : BulkGreenEvent) : Prop :=
  greenEventRetained N e.1

instance bulkEventRetainedDecidable (N : ℕ) (e : BulkGreenEvent) :
    Decidable (bulkEventRetained N e) := by unfold bulkEventRetained; infer_instance

/-! Literal retained index types.  `FiniteIndexSets` proves all five are
finite without choosing an enumeration for the ambient masks. -/

abbrev RetainedStateIndex (N : ℕ) :=
  ↥({n : PNat | stateIndexRetained N n} : Set PNat)

abbrev RetainedResidualEvent (N : ℕ) :=
  ↥({e : ResidualEvent | residualEventRetained N e} : Set ResidualEvent)

abbrev RetainedGreenEvent (N : ℕ) :=
  ↥({e : GreenEvent | greenEventRetained N e} : Set GreenEvent)

abbrev RetainedDepthOneEvent (N : ℕ) :=
  ↥({e : DepthOneGreenEvent | depthOneEventRetained N e} :
    Set DepthOneGreenEvent)

abbrev RetainedBulkEvent (N : ℕ) :=
  ↥({e : BulkGreenEvent | bulkEventRetained N e} : Set BulkGreenEvent)

/-- States supported on the first `N` positive coordinates. -/
def FiniteState (N : ℕ) : Submodule ℂ State where
  carrier := {f | ∀ n : PNat, ¬ stateIndexRetained N n → f n = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg n hn
    simp [hf n hn, hg n hn]
  smul_mem' := by
    intro c f hf n hn
    simp [hf n hn]

/-- Residual vectors supported on rows with number at most `N`. -/
def FiniteResidualSpace (N : ℕ) : Submodule ℂ ResidualSpace where
  carrier := {y | ∀ e : ResidualEvent,
    ¬ residualEventRetained N e → y e = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy e he
    simp [hx e he, hy e he]
  smul_mem' := by
    intro c x hx e he
    simp [hx e he]

/-- Green vectors supported on rows whose current number is at most `N`. -/
def FiniteGreenSpace (N : ℕ) : Submodule ℂ (ℓ²(GreenEvent, ℂ)) where
  carrier := {y | ∀ e : GreenEvent,
    ¬ greenEventRetained N e → y e = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy e he
    simp [hx e he, hy e he]
  smul_mem' := by
    intro c x hx e he
    simp [hx e he]

/-- Literal depth-one vectors supported on the retained rows. -/
def FiniteDepthOneSpace (N : ℕ) : Submodule ℂ DepthOneGreenSpace where
  carrier := {y | ∀ e : DepthOneGreenEvent,
    ¬ depthOneEventRetained N e → y e = 0}
  zero_mem' := by intro e _; rfl
  add_mem' := by
    intro x y hx hy e he
    simp [hx e he, hy e he]
  smul_mem' := by
    intro c x hx e he
    simp [hx e he]

/-- Literal bulk vectors supported on the retained rows. -/
def FiniteBulkSpace (N : ℕ) : Submodule ℂ BulkGreenSpace where
  carrier := {y | ∀ e : BulkGreenEvent,
    ¬ bulkEventRetained N e → y e = 0}
  zero_mem' := by intro e _; rfl
  add_mem' := by
    intro x y hx hy e he
    simp [hx e he, hy e he]
  smul_mem' := by
    intro c x hx e he
    simp [hx e he]

/-- Every nonzero camera at a retained state coordinate has physical base at most `N`. -/
theorem active_camera_base_le_cutoff
    (omega : AdmissibleInfinitePartition) {N r : ℕ} {n : PNat}
    (hn : stateIndexRetained N n) (hw : omega.weight r n ≠ 0) :
    baseNat r ≤ N := by
  have hdvd : basePNat r ∣ n := omega.support_dvd hw
  have hle : basePNat r ≤ n := PNat.le_of_dvd hdvd
  have hleNat : baseNat r ≤ (n : ℕ) := by
    simpa only [basePNat_coe] using
      (PNat.coe_le_coe (basePNat r) n).mpr hle
  exact hleNat.trans hn

/-- Every nonzero camera at `n ≤ N` lies in the finite code interval for `N`. -/
theorem active_camera_mem_cutoff_codes
    (omega : AdmissibleInfinitePartition) {N r : ℕ} {n : PNat}
    (hN : 0 < N) (hn : stateIndexRetained N n)
    (hw : omega.weight r n ≠ 0) :
    r ∈ Finset.range (N - 1) := by
  have hbase := active_camera_base_le_cutoff omega hn hw
  simp only [Finset.mem_range, baseNat] at *
  omega

/-- Retained Green rows have retained current state coordinates. -/
theorem greenEventRetained_current
    {N : ℕ} {e : GreenEvent} (he : greenEventRetained N e) :
    stateIndexRetained N (eventNumber e) :=
  he.1

/-- The parent of a retained Green row also lies below the cutoff. -/
theorem greenEventRetained_parent
    {N : ℕ} {e : GreenEvent} (he : greenEventRetained N e) :
    stateIndexRetained N e.2 := by
  have hdiv : e.2 ∣ eventNumber e := by
    refine ⟨basePNat e.1, ?_⟩
    simp [eventNumber, mul_comm]
  have hle : e.2 ≤ eventNumber e := PNat.le_of_dvd hdiv
  have hleNat : (e.2 : ℕ) ≤ (eventNumber e : ℕ) :=
    (PNat.coe_le_coe e.2 (eventNumber e)).mp hle
  exact hleNat.trans he.1

/-- The second ancestor of a retained depth-at-least-two row is retained. -/
theorem greenEventRetained_grandparent
    {N : ℕ} {e : GreenEvent} (he : greenEventRetained N e)
    (hg : HasGrandparent e) :
    stateIndexRetained N (grandparentIndex e) := by
  have hdivParent : grandparentIndex e ∣ e.2 := by
    refine ⟨basePNat e.1, ?_⟩
    simpa [mul_comm] using (base_mul_grandparentIndex hg).symm
  have hleParent : grandparentIndex e ≤ e.2 :=
    PNat.le_of_dvd hdivParent
  have hleNat : (grandparentIndex e : ℕ) ≤ (e.2 : ℕ) :=
    (PNat.coe_le_coe (grandparentIndex e) e.2).mp hleParent
  exact hleNat.trans (greenEventRetained_parent he)

end GreenFrame.Concrete
