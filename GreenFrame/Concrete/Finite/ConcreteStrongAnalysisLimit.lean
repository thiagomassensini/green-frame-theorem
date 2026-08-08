import GreenFrame.Concrete.Finite.StrongAnalysisLimit
import GreenFrame.Concrete.Finite.FiniteCutoffRetention
import GreenFrame.Concrete.Finite.ConcreteCoordinateCutoffLimits

/-!
# Concrete strong analysis limit

Final checkpoint for `ABGF-FS-002`: substitute the literal masks into the
two-term estimate.  Both convergence inputs are the preceding `ℓ²` tail
theorems; no existence proposition or convergence field is assumed.
-/

noncomputable section

open scoped ENNReal InnerProductSpace lp Topology
open Filter

namespace GreenFrame.Concrete

/-- `ABGF-FS-002`: `Q_N T P_N` converges strongly to the concrete analysis. -/
theorem concreteEmbeddedFiniteAnalysis_tendsto
    (omega : AdmissibleInfinitePartition) (f : State) :
    Tendsto (fun N => concreteEmbeddedFiniteAnalysis omega N f)
      atTop (nhds (concreteAnalysisOperator omega f)) := by
  simpa only [concreteEmbeddedFiniteAnalysis] using
    embeddedAnalysisSection_tendsto omega
      stateCoordinateCutoff concreteCoefficientCutoff
      stateCoordinateCutoff_tendsto
      concreteCoefficientCutoff_tendsto
      concreteCoefficientCutoff_contracts f

end GreenFrame.Concrete
