import GreenFrame.Analysis.PoissonCompletion

/-!
# The coherent atlas is a graph
-/

namespace GreenFrame

namespace PoissonData

variable {H E B : Type*}
  [AddCommGroup H] [Module ℝ H]
  [AddCommGroup E] [Module ℝ E]
  [AddCommGroup B] [Module ℝ B]
  (P : PoissonData H E B)

/-- Full coherent analysis into external and bulk coordinates. -/
def coherentAnalysis (x : H) : E × B :=
  (P.external x, P.bulk x)

/-- Graph over the compatible external range. -/
def coherentGraph : Set (E × B) :=
  {y | y.1 ∈ Set.range P.external ∧ y.2 = P.poissonOperator y.1}

/-- Every coherent state lies on the Poisson graph. -/
theorem coherentRange_subset_graph :
    Set.range P.coherentAnalysis ⊆ P.coherentGraph := by
  rintro y ⟨x, rfl⟩
  exact ⟨⟨x, rfl⟩, (P.poisson_apply_external x).symm⟩

/-- Conversely every compatible point on the graph is a coherent analysis state. -/
theorem coherentRange_eq_graph :
    Set.range P.coherentAnalysis = P.coherentGraph := by
  apply Set.Subset.antisymm P.coherentRange_subset_graph
  rintro y ⟨⟨x, hx⟩, hy⟩
  refine ⟨x, ?_⟩
  apply Prod.ext
  · exact hx
  · calc
      P.bulk x = P.poissonOperator (P.external x) := (P.poisson_apply_external x).symm
      _ = P.poissonOperator y.1 := by rw [hx]
      _ = y.2 := hy.symm

end PoissonData

end GreenFrame
