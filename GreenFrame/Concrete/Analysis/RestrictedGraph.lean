import GreenFrame.Concrete.Analysis.StaticPoisson

/-!
# The coherent atlas is a closed restricted graph
-/

noncomputable section

open scoped InnerProductSpace

namespace GreenFrame.Concrete

variable {H E B : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]

/-- Graph over the compatible external range. -/
def restrictedPoissonGraph
    {T : H →L[ℂ] HilbertSum E B}
    (bounds : SplitComplexFrameBounds T) :
    Set (CompatibleExternal T × B) :=
  {p | p.2 = restrictedPoisson bounds p.1}

/-- Every coherent state lies on the static Poisson graph. -/
theorem coherentPair_range_subset_graph
    {T : H →L[ℂ] HilbertSum E B}
    (bounds : SplitComplexFrameBounds T) :
    Set.range (coherentPair (T := T)) ⊆ restrictedPoissonGraph bounds := by
  rintro _ ⟨x, rfl⟩
  change normalizedBulk T x =
    restrictedPoisson bounds ((normalizedExternal T).rangeRestrict x)
  exact (restrictedPoisson_apply_external bounds x).symm

/-- Every graph point over the compatible range comes from one global state. -/
theorem graph_subset_coherentPair_range
    {T : H →L[ℂ] HilbertSum E B}
    (bounds : SplitComplexFrameBounds T) :
    restrictedPoissonGraph bounds ⊆ Set.range (coherentPair (T := T)) := by
  intro y hy
  change y.2 = restrictedPoisson bounds y.1 at hy
  obtain ⟨x, hx⟩ : ∃ x : H, normalizedExternal T x = (y.1 : E) := y.1.property
  have he : (normalizedExternal T).rangeRestrict x = y.1 := by
    apply Subtype.ext
    exact hx
  refine ⟨x, Prod.ext ?_ ?_⟩
  · exact he
  · change normalizedBulk T x = y.2
    calc
      normalizedBulk T x =
          restrictedPoisson bounds ((normalizedExternal T).rangeRestrict x) :=
        (restrictedPoisson_apply_external bounds x).symm
      _ = restrictedPoisson bounds y.1 :=
        congrArg (fun e ↦ restrictedPoisson bounds e) he
      _ = y.2 := hy.symm

/-- Exact graph description of the coherent normalized range. -/
theorem coherentPair_range_eq_graph
    {T : H →L[ℂ] HilbertSum E B}
    (bounds : SplitComplexFrameBounds T) :
    Set.range (coherentPair (T := T)) = restrictedPoissonGraph bounds :=
  Set.Subset.antisymm
    (coherentPair_range_subset_graph bounds)
    (graph_subset_coherentPair_range bounds)

/-- The restricted Poisson graph is closed because it is the kernel of a
continuous linear map. -/
theorem restrictedPoissonGraph_isClosed
    {T : H →L[ℂ] HilbertSum E B}
    (bounds : SplitComplexFrameBounds T) :
    IsClosed (restrictedPoissonGraph bounds) := by
  let D : CompatibleExternal T × B →L[ℂ] B :=
    ContinuousLinearMap.snd ℂ (CompatibleExternal T) B -
      (restrictedPoisson bounds).comp
        (ContinuousLinearMap.fst ℂ (CompatibleExternal T) B)
  have hgraph :
      restrictedPoissonGraph bounds =
        (D.ker : Set (CompatibleExternal T × B)) := by
    ext p
    change
      (p.2 = restrictedPoisson bounds p.1) ↔
        p.2 - restrictedPoisson bounds p.1 = 0
    exact sub_eq_zero.symm
  rw [hgraph]
  exact D.isClosed_ker

end GreenFrame.Concrete
