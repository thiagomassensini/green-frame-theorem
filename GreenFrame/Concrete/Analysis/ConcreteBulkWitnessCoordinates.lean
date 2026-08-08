import GreenFrame.Concrete.Analysis.ConcreteBulkWitnessArithmetic

/-!
# Exact Green coordinate of the canonical `(2,4)` witness

This checkpoint evaluates the stencil, canonical weight, Green mass,
amplitude, and final raw Green coordinate.  It does not yet form or estimate
the complete bulk vector.
-/

noncomputable section

open scoped ENNReal InnerProductSpace lp

namespace GreenFrame.Concrete

@[simp]
theorem currentTerm_twoFourWitness :
    currentTerm twoFourGreenEvent twoFourWitnessState = (1 : ℂ) := by
  rw [currentTerm, twoFourGreenEvent_eventNumber,
    twoFourWitnessState_at_four]

@[simp]
theorem parentTerm_twoFourWitness :
    parentTerm twoFourGreenEvent twoFourWitnessState = (0 : ℂ) := by
  simp [parentTerm, twoFourGreenEvent, twoFourWitnessState_at_two]

@[simp]
theorem grandparentTerm_twoFourWitness :
    grandparentTerm twoFourGreenEvent twoFourWitnessState = (0 : ℂ) := by
  simp [grandparentTerm, twoFourGreenEvent_hasGrandparent,
    twoFourGreenEvent_grandparentIndex, twoFourWitnessState_at_one]

/-- The delta state kills both ancestor terms and leaves the current term. -/
@[simp]
theorem verticalGreenStencil_twoFourWitness :
    verticalGreenStencil twoFourGreenEvent twoFourWitnessState = (1 : ℂ) := by
  simp [verticalGreenStencil]

/-- Exact canonical code-reindexed weight `ω₂(4)=1/2`. -/
theorem canonicalCarry_twoFour_weight :
    canonicalCarryInfinitePartition.weight 0
      (eventNumber twoFourGreenEvent) = (1 / 2 : ℝ) := by
  rw [canonicalCarryInfinitePartition_weight,
    twoFourGreenEvent_eventNumber]
  simpa [baseNat] using carryCameraWeight_two_four

/-- Exact transmitted Green mass `μ_G(2,4)=1/4`. -/
theorem canonicalCarry_twoFour_greenEventMass :
    greenEventMass canonicalCarryInfinitePartition twoFourGreenEvent =
      (1 / 4 : ℝ) := by
  change canonicalCarryInfinitePartition.weight 0 (eventNumber twoFourGreenEvent) / baseReal 0 = (1 / 4 : ℝ)
  rw [canonicalCarry_twoFour_weight]; norm_num [baseReal, baseNat]

/-- Exact canonical Green amplitude at the paper-bulk witness. -/
theorem canonicalCarry_twoFour_greenAmplitude :
    greenAmplitude canonicalCarryInfinitePartition twoFourGreenEvent =
      (1 / 2 : ℝ) := by
  rw [greenAmplitude, canonicalCarry_twoFour_greenEventMass]
  norm_num

/-- The raw Green coordinate on `e₄` is exactly `1/2`. -/
theorem canonicalCarry_twoFour_greenCoordinate :
    greenCoordinate canonicalCarryInfinitePartition twoFourGreenEvent
      twoFourWitnessState = (1 / 2 : ℂ) := by
  rw [greenCoordinate, canonicalCarry_twoFour_greenAmplitude,
    verticalGreenStencil_twoFourWitness]
  norm_num

end GreenFrame.Concrete
