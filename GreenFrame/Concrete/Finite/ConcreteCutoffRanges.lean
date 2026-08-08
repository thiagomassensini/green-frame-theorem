import GreenFrame.Concrete.Finite.FiniteCutoffRetention
import GreenFrame.Concrete.Finite.FiniteIndexSets

/-!
# Ranges of the ambient coordinate cutoffs

The actual operators are common-space masks, but their ranges are exactly the
paper's finite state space and the finite retained row spaces.  Together with
the `Finite` instances in `FiniteIndexSets`, these equalities certify that the
ambient presentation is equivalent to a literal finite-coordinate model.
-/

noncomputable section

open scoped ENNReal InnerProductSpace lp

namespace GreenFrame.Concrete

theorem stateCoordinateCutoff_range (N : ℕ) :
    LinearMap.range (stateCoordinateCutoff N).toLinearMap = FiniteState N := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    intro n hn
    simp [stateCoordinateCutoff, hn]
  · intro hf
    refine ⟨f, ?_⟩
    exact stateCoordinateCutoff_fixes_finite ⟨f, hf⟩

theorem residualCoordinateCutoff_range (N : ℕ) :
    LinearMap.range (residualCoordinateCutoff N).toLinearMap =
      FiniteResidualSpace N := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    intro e he
    simp [residualCoordinateCutoff, he]
  · intro hy
    refine ⟨y, ?_⟩
    apply lp.ext
    funext e
    by_cases he : residualEventRetained N e
    · simp [residualCoordinateCutoff, he]
    · simp [residualCoordinateCutoff, he, hy e he]

theorem depthOneCoordinateCutoff_range (N : ℕ) :
    LinearMap.range (depthOneCoordinateCutoff N).toLinearMap =
      FiniteDepthOneSpace N := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    intro e he
    simp [depthOneCoordinateCutoff, he]
  · intro hy
    refine ⟨y, ?_⟩
    apply lp.ext
    funext e
    by_cases he : depthOneEventRetained N e
    · simp [depthOneCoordinateCutoff, he]
    · simp [depthOneCoordinateCutoff, he, hy e he]

theorem bulkCoordinateCutoff_range (N : ℕ) :
    LinearMap.range (bulkCoordinateCutoff N).toLinearMap =
      FiniteBulkSpace N := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    intro e he
    simp [bulkCoordinateCutoff, he]
  · intro hy
    refine ⟨y, ?_⟩
    apply lp.ext
    funext e
    by_cases he : bulkEventRetained N e
    · simp [bulkCoordinateCutoff, he]
    · simp [bulkCoordinateCutoff, he, hy e he]

/-- The residual component of every `Q_N y` lies in the finite residual rows. -/
theorem concreteCoefficientCutoff_residual_mem
    (N : ℕ) (y : ConcreteAnalysisSpace) :
    (WithLp.ofLp
      (WithLp.ofLp
        (WithLp.ofLp (concreteCoefficientCutoff N y)).1).1).2 ∈
      FiniteResidualSpace N := by
  intro e he
  simp [concreteCoefficientCutoff, externalCoordinateCutoff,
    seedResidualCoordinateCutoff, residualCoordinateCutoff,
    l2ProductMap_apply, he]

/-- The depth-one component of every `Q_N y` lies in finite retained rows. -/
theorem concreteCoefficientCutoff_depthOne_mem
    (N : ℕ) (y : ConcreteAnalysisSpace) :
    (WithLp.ofLp
      (WithLp.ofLp (concreteCoefficientCutoff N y)).1).2 ∈
      FiniteDepthOneSpace N := by
  intro e he
  simp [concreteCoefficientCutoff, externalCoordinateCutoff,
    depthOneCoordinateCutoff, l2ProductMap_apply, he]

/-- The bulk component of every `Q_N y` lies in finite retained rows. -/
theorem concreteCoefficientCutoff_bulk_mem
    (N : ℕ) (y : ConcreteAnalysisSpace) :
    (WithLp.ofLp (concreteCoefficientCutoff N y)).2 ∈
      FiniteBulkSpace N := by
  intro e he
  simp [concreteCoefficientCutoff, bulkCoordinateCutoff,
    l2ProductMap_apply, he]

end GreenFrame.Concrete
