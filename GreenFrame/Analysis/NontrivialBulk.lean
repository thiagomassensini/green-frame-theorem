import GreenFrame.Analysis.GraphRange

/-!
# Nontriviality of the Green bulk and Poisson return
-/

namespace GreenFrame

namespace PoissonData

variable {H E B : Type*}
  [AddCommGroup H] [Module ℝ H]
  [AddCommGroup E] [Module ℝ E]
  [AddCommGroup B] [Module ℝ B]
  (P : PoissonData H E B)

/-- A single nonzero bulk coordinate certifies that the bulk map is nonzero. -/
theorem rawBulk_nonzero (h : ∃ x, P.bulk x ≠ 0) : P.bulk ≠ 0 := by
  rintro hzero
  obtain ⟨x, hx⟩ := h
  apply hx
  rw [hzero]
  rfl

/-- Nonzero coherent bulk forces the Poisson operator itself to be nonzero. -/
theorem poisson_nonzero (h : ∃ x, P.bulk x ≠ 0) : P.poissonOperator ≠ 0 := by
  rintro hzero
  obtain ⟨x, hx⟩ := h
  apply hx
  calc
    P.bulk x = P.poissonOperator (P.external x) := (P.poisson_apply_external x).symm
    _ = 0 := by rw [hzero]; rfl

end PoissonData

end GreenFrame
