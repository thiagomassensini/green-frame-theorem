import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Generic inverse square root of a Hilbert-space endomorphism

This tiny generic wrapper lets the CFC instance be elaborated in the same
complete Hilbert-space context used by the canonical frame normalization.
-/

noncomputable section

open scoped InnerProduct InnerProductSpace

namespace GreenFrame.Concrete

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Continuous-functional-calculus inverse square root of an endomorphism. -/
noncomputable def operatorInverseSqrt (F : H →L[ℂ] H) : H →L[ℂ] H :=
  CFC.rpow F (-(1 / 2 : ℝ))

end GreenFrame.Concrete
