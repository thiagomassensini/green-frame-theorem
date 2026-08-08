import GreenFrame.Concrete.Analysis.GreenAnalysisVector

/-!
# The bounded global Green analysis operator

The already packaged global Green vector is promoted to a complex continuous
linear map with certified norm bound `sqrt greenBesselConstant`.
-/

open scoped ENNReal lp

namespace GreenFrame.Concrete

/-- Linear form of the global Green analysis map. -/
noncomputable def greenAnalysisLinearMap
    (omega : AdmissibleInfinitePartition) :
    State →ₗ[ℂ] ℓ²(GreenEvent, ℂ) where
  toFun := greenAnalysis omega
  map_add' f g := by
    apply lp.ext
    funext e
    exact greenCoordinate_add omega e f g
  map_smul' c f := by
    apply lp.ext
    funext e
    exact greenCoordinate_smul omega e c f

/-- Norm bound in the form required by `LinearMap.mkContinuous`. -/
theorem greenAnalysis_norm_le
    (omega : AdmissibleInfinitePartition) (f : State) :
    ‖greenAnalysis omega f‖ ≤ Real.sqrt greenBesselConstant * ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  calc
    ‖greenAnalysis omega f‖ ^ 2 ≤ greenBesselConstant * ‖f‖ ^ 2 :=
      greenAnalysis_norm_sq_le omega f
    _ = (Real.sqrt greenBesselConstant * ‖f‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt greenBesselConstant_nonneg]

/-- Bounded global Green analysis operator with an explicit norm certificate. -/
noncomputable def greenAnalysisOperator
    (omega : AdmissibleInfinitePartition) :
    State →L[ℂ] ℓ²(GreenEvent, ℂ) :=
  (greenAnalysisLinearMap omega).mkContinuous
    (Real.sqrt greenBesselConstant) (greenAnalysis_norm_le omega)

@[simp]
theorem greenAnalysisOperator_apply
    (omega : AdmissibleInfinitePartition) (f : State) :
    greenAnalysisOperator omega f = greenAnalysis omega f :=
  rfl

/-- Operator-norm version of the explicit Green Bessel certificate. -/
theorem greenAnalysisOperator_norm_le
    (omega : AdmissibleInfinitePartition) :
    ‖greenAnalysisOperator omega‖ ≤ Real.sqrt greenBesselConstant := by
  simpa only [greenAnalysisOperator] using
    LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _)
      (greenAnalysis_norm_le omega)

end GreenFrame.Concrete
