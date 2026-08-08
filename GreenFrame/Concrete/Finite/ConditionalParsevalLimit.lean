import GreenFrame.Concrete.Finite.ConcreteStrongAnalysisLimit
import GreenFrame.Concrete.Analysis.CanonicalParseval
import GreenFrame.Concrete.Analysis.OperatorInverseSqrt
/-!
# Conditional strong limit of the normalized finite analyses

This module records the exact conditional boundary of `ABGF-FS-003`.  All
finite operators live on the common ambient `State` space.  The only unproved
mathematical input is strong convergence of the continuous-functional-calculus
inverse square roots of the extended finite frame operators.

The conclusion follows from the concrete `ABGF-FS-002` limit and the uniform
operator bound supplied directly by the contractive state/coefficient masks.
-/

noncomputable section

open scoped ENNReal InnerProduct InnerProductSpace lp Topology
open Filter

namespace GreenFrame.Concrete

/-- Common-space finite frame operator, made nondegenerate on the complement
of `H_N` by the identity-minus-state-cutoff term. -/
noncomputable def extendedFiniteFrameOperator
    (omega : AdmissibleInfinitePartition) (N : ℕ) :
    State →L[ℂ] State :=
  frameOperator (concreteEmbeddedFiniteAnalysis omega N) +
    (1 - stateCoordinateCutoff N)

/-- Continuous-functional-calculus inverse square root of the common-space
finite frame operator. -/
noncomputable def extendedFiniteInverseSqrt
    (omega : AdmissibleInfinitePartition) (N : ℕ) :
    State →L[ℂ] State :=
  operatorInverseSqrt (extendedFiniteFrameOperator omega N)

/-- Embedded normalized finite analysis `S_N R_N` in the fixed coefficient
space. -/
noncomputable def concreteEmbeddedCanonicalAnalysis
    (omega : AdmissibleInfinitePartition) (N : ℕ) :
    State →L[ℂ] ConcreteAnalysisSpace :=
  (concreteEmbeddedFiniteAnalysis omega N).comp
    (extendedFiniteInverseSqrt omega N)

/-- `ABGF-FS-003`, explicitly conditional on the missing common-space CFC
limit.  If the extended inverse square roots converge strongly, then the
embedded normalized finite analyses converge strongly to the canonical
Parseval analysis. -/
theorem concreteEmbeddedCanonicalAnalysis_tendsto_of_extendedInverseSqrt_tendsto
    (omega : AdmissibleInfinitePartition)
    (hCFC : ∀ f : State,
      Tendsto (fun N => extendedFiniteInverseSqrt omega N f) atTop
        (𝓝 (inverseSqrtFrame (concreteAnalysisOperator omega) f)))
    (f : State) :
    Tendsto (fun N => concreteEmbeddedCanonicalAnalysis omega N f) atTop
      (𝓝 (canonicalAnalysis (concreteAnalysisOperator omega) f)) := by
  let T : State →L[ℂ] ConcreteAnalysisSpace :=
    concreteAnalysisOperator omega
  let R : State →L[ℂ] State := inverseSqrtFrame T
  have hsection (N : ℕ) (x : State) :
      ‖concreteEmbeddedFiniteAnalysis omega N x‖ ≤ ‖T‖ * ‖x‖ := by
    rw [concreteEmbeddedFiniteAnalysis_apply]
    calc
      ‖concreteCoefficientCutoff N
          (T (stateCoordinateCutoff N x))‖ ≤
          ‖T (stateCoordinateCutoff N x)‖ :=
        concreteCoefficientCutoff_contracts N _
      _ ≤ ‖T‖ * ‖stateCoordinateCutoff N x‖ := T.le_opNorm _
      _ ≤ ‖T‖ * ‖x‖ :=
        mul_le_mul_of_nonneg_left
          (stateCoordinateCutoff_contracts N x) (norm_nonneg T)
  have hdelta :
      Tendsto
        (fun N => extendedFiniteInverseSqrt omega N f - R f)
        atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => R f) atTop (𝓝 (R f)) :=
      tendsto_const_nhds
    simpa only [T, R, sub_self] using (hCFC f).sub hconst
  have hmajorant :
      Tendsto
        (fun N => ‖T‖ *
          ‖extendedFiniteInverseSqrt omega N f - R f‖)
        atTop (𝓝 0) := by
    simpa only [mul_zero, norm_zero] using hdelta.norm.const_mul ‖T‖
  have hvarying :
      Tendsto
        (fun N => concreteEmbeddedFiniteAnalysis omega N
          (extendedFiniteInverseSqrt omega N f - R f))
        atTop (𝓝 0) :=
    squeeze_zero_norm
      (fun N => hsection N
        (extendedFiniteInverseSqrt omega N f - R f))
      hmajorant
  have hfixed :
      Tendsto
        (fun N => concreteEmbeddedFiniteAnalysis omega N (R f))
        atTop (𝓝 (T (R f))) := by
    simpa only [T, R] using
      concreteEmbeddedFiniteAnalysis_tendsto omega (R f)
  simpa only [concreteEmbeddedCanonicalAnalysis,
    ContinuousLinearMap.comp_apply, canonicalAnalysis, T, R, map_sub,
    sub_add_cancel, zero_add] using hvarying.add hfixed

end GreenFrame.Concrete
