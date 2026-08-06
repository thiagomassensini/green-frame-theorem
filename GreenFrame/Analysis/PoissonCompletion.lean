import GreenFrame.Analysis.CanonicalParseval

/-!
# Exact Poisson completion
-/

namespace GreenFrame

variable (H E B : Type*)
  [AddCommGroup H] [Module ℝ H]
  [AddCommGroup E] [Module ℝ E]
  [AddCommGroup B] [Module ℝ B]

/-- External/bulk analysis together with an exact external left inverse. -/
structure PoissonData where
  external : H →ₗ[ℝ] E
  bulk : H →ₗ[ℝ] B
  leftInverse : E →ₗ[ℝ] H
  leftInverse_external : leftInverse.comp external = LinearMap.id

namespace PoissonData

variable {H E B}
  [AddCommGroup H] [Module ℝ H]
  [AddCommGroup E] [Module ℝ E]
  [AddCommGroup B] [Module ℝ B]
  (P : PoissonData H E B)

/-- The Poisson operator reconstructs bulk from external data. -/
def poissonOperator : E →ₗ[ℝ] B :=
  P.bulk.comp P.leftInverse

/-- The chosen external synthesis is a left inverse pointwise. -/
theorem external_leftInverse (x : H) :
    P.leftInverse (P.external x) = x := by
  have h := congrArg (fun f : H →ₗ[ℝ] H => f x) P.leftInverse_external
  simpa using h

/-- Exact operator intertwining `M E = B`. -/
theorem poisson_intertwining :
    P.poissonOperator.comp P.external = P.bulk := by
  ext x
  simp [poissonOperator, P.external_leftInverse]

/-- Pointwise form of the Poisson identity. -/
theorem poisson_apply_external (x : H) :
    P.poissonOperator (P.external x) = P.bulk x := by
  simp [poissonOperator, P.external_leftInverse]

/-- External data killed by the left inverse has zero Poisson return. -/
theorem poisson_eq_zero_of_leftInverse_eq_zero {y : E}
    (hy : P.leftInverse y = 0) : P.poissonOperator y = 0 := by
  simp [poissonOperator, hy]

end PoissonData

end GreenFrame
