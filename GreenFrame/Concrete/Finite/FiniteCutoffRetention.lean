import GreenFrame.Concrete.Finite.AnalysisSection
import GreenFrame.Concrete.Finite.ConcreteCoordinateCutoffMaps

/-!
# Retention laws and the canonical finite analysis

This checkpoint proves directly that the literal masks fix `H_N`, retain all
seed-residual rows needed for the lower bound, and give the uniform finite
bounds.  No existential cutoff proposition or abstract cutoff-data record is
used: `P_N`, `Q_N`, and `T_N = Q_N T P_N` are concrete definitions.
-/

noncomputable section

open scoped ENNReal InnerProductSpace lp

namespace GreenFrame.Concrete

theorem stateCoordinateCutoff_fixes_finite
    {N : ℕ} (f : FiniteState N) :
    stateCoordinateCutoff N (f : State) = (f : State) := by
  apply lp.ext
  funext n
  by_cases hn : stateIndexRetained N n
  · simp [stateCoordinateCutoff, hn]
  · simp [stateCoordinateCutoff, hn, f.property n hn]

theorem residualCoordinateCutoff_fixes_analysis
    (omega : AdmissibleInfinitePartition) {N : ℕ}
    (f : FiniteState N) :
    residualCoordinateCutoff N (residualAnalysis omega (f : State)) =
      residualAnalysis omega (f : State) := by
  apply lp.ext
  funext e
  by_cases he : residualEventRetained N e
  · simp [residualCoordinateCutoff, he]
  · have hzero : residualCoordinate omega e (f : State) = 0 := by
      by_cases hn : stateIndexRetained N e.1
      · have hbase : ¬ baseNat e.2 ≤ N := by
          intro hb
          exact he ⟨hn, hb⟩
        have hw : omega.weight e.2 e.1 = 0 := by
          by_contra hw
          exact hbase (active_camera_base_le_cutoff omega hn hw)
        simp [residualCoordinate, residualAmplitude,
          residualEventMass, hw]
      · have hf : (f : State) e.1 = 0 := f.property e.1 hn
        simp [residualCoordinate, hf]
    simp [residualCoordinateCutoff, he, residualAnalysis_apply, hzero]

theorem seedResidualCoordinateCutoff_fixes_analysis
    (omega : AdmissibleInfinitePartition) {N : ℕ}
    (f : FiniteState N) :
    seedResidualCoordinateCutoff N
        (seedResidualAnalysis omega (f : State)) =
      seedResidualAnalysis omega (f : State) := by
  simp only [seedResidualCoordinateCutoff, l2ProductMap_apply,
    seedResidualAnalysis,
    ContinuousLinearMap.id_apply,
    residualCoordinateCutoff_fixes_analysis omega f]

/-- The literal common-space section `T_N = Q_N T P_N`. -/
noncomputable def concreteEmbeddedFiniteAnalysis
    (omega : AdmissibleInfinitePartition) (N : ℕ) :
    State →L[ℂ] ConcreteAnalysisSpace :=
  embeddedAnalysisSection omega
    (stateCoordinateCutoff N) (concreteCoefficientCutoff N)

@[simp]
theorem concreteEmbeddedFiniteAnalysis_apply
    (omega : AdmissibleInfinitePartition) (N : ℕ) (f : State) :
    concreteEmbeddedFiniteAnalysis omega N f =
      concreteCoefficientCutoff N
        (concreteAnalysisOperator omega (stateCoordinateCutoff N f)) :=
  rfl

theorem concreteCutoff_retains_seedResidual
    (omega : AdmissibleInfinitePartition) {N : ℕ}
    (f : FiniteState N) :
    concreteSeedResidualProjection
        (concreteEmbeddedFiniteAnalysis omega N (f : State)) =
      seedResidualAnalysis omega (f : State) := by
  rw [concreteEmbeddedFiniteAnalysis_apply,
    stateCoordinateCutoff_fixes_finite f]
  simp only [concreteAnalysisOperator_apply,
    concreteExternalAnalysisOperator_apply,
    concreteCoefficientCutoff, externalCoordinateCutoff,
    concreteSeedResidualProjection,
    l2ProductMap_apply]
  exact seedResidualCoordinateCutoff_fixes_analysis omega f

/-- The literal finite analysis, with domain bundled as `H_N`. -/
noncomputable def concreteFiniteAnalysisOperator
    (omega : AdmissibleInfinitePartition) (N : ℕ) :
    FiniteState N →L[ℂ] ConcreteAnalysisSpace :=
  (concreteEmbeddedFiniteAnalysis omega N).comp (FiniteState N).subtypeL

@[simp]
theorem concreteFiniteAnalysisOperator_apply
    (omega : AdmissibleInfinitePartition) (N : ℕ) (f : FiniteState N) :
    concreteFiniteAnalysisOperator omega N f =
      concreteEmbeddedFiniteAnalysis omega N (f : State) :=
  rfl

/-- Uniform upper bound, independent of `N`. -/
theorem concreteEmbeddedFiniteAnalysis_upper
    (omega : AdmissibleInfinitePartition) {N : ℕ}
    (f : FiniteState N) :
    ‖concreteEmbeddedFiniteAnalysis omega N (f : State)‖ ^ 2 ≤
      (1 + greenBesselConstant) * ‖(f : State)‖ ^ 2 := by
  have hQ :
      ‖concreteEmbeddedFiniteAnalysis omega N (f : State)‖ ≤
        ‖concreteAnalysisOperator omega
          (stateCoordinateCutoff N (f : State))‖ := by
    exact concreteCoefficientCutoff_contracts N _
  have hQsq :
      ‖concreteEmbeddedFiniteAnalysis omega N (f : State)‖ ^ 2 ≤
        ‖concreteAnalysisOperator omega
          (stateCoordinateCutoff N (f : State))‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hQ
  calc
    ‖concreteEmbeddedFiniteAnalysis omega N (f : State)‖ ^ 2 ≤
        ‖concreteAnalysisOperator omega
          (stateCoordinateCutoff N (f : State))‖ ^ 2 := hQsq
    _ = ‖concreteAnalysisOperator omega (f : State)‖ ^ 2 := by
      rw [stateCoordinateCutoff_fixes_finite f]
    _ ≤ (1 + greenBesselConstant) * ‖(f : State)‖ ^ 2 :=
      (concreteAnalysisOperator_norm_sq_bounds omega (f : State)).2

/-- Uniform lower bound from literal seed-residual retention. -/
theorem concreteEmbeddedFiniteAnalysis_lower
    (omega : AdmissibleInfinitePartition) {N : ℕ}
    (f : FiniteState N) :
    (1 / 2 : ℝ) * ‖(f : State)‖ ^ 2 ≤
      ‖concreteEmbeddedFiniteAnalysis omega N (f : State)‖ ^ 2 := by
  have hseed :
      ‖seedResidualAnalysis omega (f : State)‖ ≤
        ‖concreteEmbeddedFiniteAnalysis omega N (f : State)‖ := by
    rw [← concreteCutoff_retains_seedResidual omega f]
    exact concreteSeedResidualProjection_contracts _
  have hseedSq :
      ‖seedResidualAnalysis omega (f : State)‖ ^ 2 ≤
        ‖concreteEmbeddedFiniteAnalysis omega N (f : State)‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hseed
  exact (seedResidualAnalysis_norm_sq_bounds omega (f : State)).1.trans hseedSq

/-- `ABGF-FS-001`: the literal common-space sections have uniform bounds. -/
theorem concreteEmbeddedFiniteAnalysis_norm_sq_bounds
    (omega : AdmissibleInfinitePartition) {N : ℕ}
    (f : FiniteState N) :
    (1 / 2 : ℝ) * ‖(f : State)‖ ^ 2 ≤
        ‖concreteEmbeddedFiniteAnalysis omega N (f : State)‖ ^ 2 ∧
      ‖concreteEmbeddedFiniteAnalysis omega N (f : State)‖ ^ 2 ≤
        (1 + greenBesselConstant) * ‖(f : State)‖ ^ 2 :=
  ⟨concreteEmbeddedFiniteAnalysis_lower omega f,
    concreteEmbeddedFiniteAnalysis_upper omega f⟩

/-- Operator-bundled `H_N` form of `ABGF-FS-001`. -/
theorem concreteFiniteAnalysisOperator_norm_sq_bounds
    (omega : AdmissibleInfinitePartition) {N : ℕ}
    (f : FiniteState N) :
    (1 / 2 : ℝ) * ‖f‖ ^ 2 ≤
        ‖concreteFiniteAnalysisOperator omega N f‖ ^ 2 ∧
      ‖concreteFiniteAnalysisOperator omega N f‖ ^ 2 ≤
        (1 + greenBesselConstant) * ‖f‖ ^ 2 := by
  rw [concreteFiniteAnalysisOperator_apply]
  change
    (1 / 2 : ℝ) * ‖(f : State)‖ ^ 2 ≤
        ‖concreteEmbeddedFiniteAnalysis omega N (f : State)‖ ^ 2 ∧
      ‖concreteEmbeddedFiniteAnalysis omega N (f : State)‖ ^ 2 ≤
        (1 + greenBesselConstant) * ‖(f : State)‖ ^ 2
  exact concreteEmbeddedFiniteAnalysis_norm_sq_bounds omega f

end GreenFrame.Concrete
