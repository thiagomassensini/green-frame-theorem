import GreenFrame.Concrete.Analysis.ExternalRange

/-!
# Static Poisson reconstruction on compatible external data
-/

noncomputable section

open scoped InnerProductSpace

namespace GreenFrame.Concrete

variable {H E B : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]

/-- Closed space of compatible normalized external data. -/
abbrev CompatibleExternal (T : H →L[ℂ] HilbertSum E B) :=
  (normalizedExternal T).range

/-- Static Poisson operator on the exact compatible external domain. -/
def restrictedPoisson
    {T : H →L[ℂ] HilbertSum E B}
    (bounds : SplitComplexFrameBounds T) :
    CompatibleExternal T →L[ℂ] B :=
  (normalizedBulk T).comp (normalizedExternalRangeInverse bounds)

/-- Pointwise Poisson intertwining. -/
@[simp]
theorem restrictedPoisson_apply_external
    {T : H →L[ℂ] HilbertSum E B}
    (bounds : SplitComplexFrameBounds T) (x : H) :
    restrictedPoisson bounds ((normalizedExternal T).rangeRestrict x) =
      normalizedBulk T x := by
  change normalizedBulk T
      (normalizedExternalRangeInverse bounds
        ((normalizedExternal T).rangeRestrict x)) =
    normalizedBulk T x
  rw [normalizedExternalRangeInverse_apply]

/-- Operator form of the static Poisson identity. -/
theorem restrictedPoisson_intertwining
    {T : H →L[ℂ] HilbertSum E B}
    (bounds : SplitComplexFrameBounds T) :
    (restrictedPoisson bounds).comp (normalizedExternal T).rangeRestrict =
      normalizedBulk T := by
  apply ContinuousLinearMap.ext
  intro x
  change restrictedPoisson bounds ((normalizedExternal T).rangeRestrict x) =
    normalizedBulk T x
  exact restrictedPoisson_apply_external bounds x

/-- Coherent normalized analysis written in compatible external/bulk
coordinates. -/
def coherentPair
    {T : H →L[ℂ] HilbertSum E B} :
    H →L[ℂ] CompatibleExternal T × B :=
  (normalizedExternal T).rangeRestrict.prod (normalizedBulk T)

end GreenFrame.Concrete
