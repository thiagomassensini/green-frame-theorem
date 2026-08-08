import GreenFrame.Concrete.Finite.CoordinateCutoffs

/-!
# Embedded concrete analysis sections

The paper's common-space section is literally `Q_N T P_N`.  This checkpoint
contains only that generic composition.  The concrete maps `P_N` and `Q_N`,
their range certificates, the uniform bounds, and their strong limits are
constructed in the subsequent finite-section checkpoints.

In particular there is no `ConcreteFiniteCutoffsExist` proposition and no
cutoff-data structure whose fields could hide the mathematical obligations.
-/

open scoped ENNReal lp

namespace GreenFrame.Concrete

/-- Common-space embedded section `Q T P`. -/
noncomputable def embeddedAnalysisSection
    (omega : AdmissibleInfinitePartition)
    (P : State →L[ℂ] State)
    (Q : ConcreteAnalysisSpace →L[ℂ] ConcreteAnalysisSpace) :
    State →L[ℂ] ConcreteAnalysisSpace :=
  Q.comp ((concreteAnalysisOperator omega).comp P)

@[simp]
theorem embeddedAnalysisSection_apply
    (omega : AdmissibleInfinitePartition)
    (P : State →L[ℂ] State)
    (Q : ConcreteAnalysisSpace →L[ℂ] ConcreteAnalysisSpace)
    (f : State) :
    embeddedAnalysisSection omega P Q f =
      Q (concreteAnalysisOperator omega (P f)) :=
  rfl

end GreenFrame.Concrete
