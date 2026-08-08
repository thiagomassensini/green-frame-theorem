import GreenFrame.Concrete.Analysis.ConcreteSplitAnalysis

/-!
# Arithmetic data for the canonical paper-bulk witness at `(2,4)`

This first checkpoint fixes the bulk event, the delta state, and the exact
base-two parent/grandparent arithmetic.  It intentionally contains no Green
coordinate or CFC argument.
-/

noncomputable section

open scoped ENNReal InnerProductSpace lp

namespace GreenFrame.Concrete

/-- Base-two Green event with parent `2` and current number `4`. -/
def twoFourGreenEvent : GreenEvent :=
  (0, (2 : PNat))

/-- Unit delta state at the current node `4`. -/
noncomputable def twoFourWitnessState : State :=
  lp.single 2 (4 : PNat) (1 : ℂ)

@[simp]
theorem twoFourGreenEvent_eventNumber :
    eventNumber twoFourGreenEvent = (4 : PNat) := by
  apply PNat.eq
  norm_num [twoFourGreenEvent, eventNumber, basePNat, baseNat]

@[simp]
theorem twoFourGreenEvent_hasGrandparent :
    HasGrandparent twoFourGreenEvent := by
  norm_num [HasGrandparent, twoFourGreenEvent, basePNat, baseNat]

/-- The same event bundled in the literal paper bulk index type. -/
def twoFourBulkEvent : BulkGreenEvent :=
  ⟨twoFourGreenEvent, twoFourGreenEvent_hasGrandparent⟩

@[simp]
theorem twoFourBulkEvent_val :
    (twoFourBulkEvent : GreenEvent) = twoFourGreenEvent :=
  rfl

@[simp]
theorem twoFourGreenEvent_grandparentIndex :
    grandparentIndex twoFourGreenEvent = (1 : PNat) := by
  apply PNat.eq
  have hnat := congrArg (fun n : PNat => (n : ℕ))
    (base_mul_grandparentIndex twoFourGreenEvent_hasGrandparent)
  change 2 * (grandparentIndex twoFourGreenEvent : ℕ) = 2 at hnat
  omega

@[simp]
theorem twoFourWitnessState_at_four :
    twoFourWitnessState (4 : PNat) = (1 : ℂ) := by
  exact lp.single_apply_self 2 (4 : PNat) (1 : ℂ)

@[simp]
theorem twoFourWitnessState_at_two :
    twoFourWitnessState (2 : PNat) = (0 : ℂ) := by
  exact lp.single_apply_ne 2 (4 : PNat) (1 : ℂ) (by norm_num)

@[simp]
theorem twoFourWitnessState_at_one :
    twoFourWitnessState (1 : PNat) = (0 : ℂ) := by
  exact lp.single_apply_ne 2 (4 : PNat) (1 : ℂ) (by norm_num)

@[simp]
theorem twoFourWitnessState_norm :
    ‖twoFourWitnessState‖ = 1 := by
  simpa only [twoFourWitnessState, norm_one] using
    (lp.norm_single (p := (2 : ℝ≥0∞)) (by norm_num)
      (4 : PNat) (1 : ℂ))

end GreenFrame.Concrete
