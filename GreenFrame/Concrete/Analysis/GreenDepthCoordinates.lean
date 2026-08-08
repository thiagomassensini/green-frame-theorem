import GreenFrame.Concrete.Analysis.GreenAnalysisOperator

/-!
# Canonical Green depth split: masked coordinates

This checkpoint defines the two complementary Green row masks and proves
their pointwise energy decomposition and summability.
-/

noncomputable section

open scoped ENNReal lp

namespace GreenFrame.Concrete

/-- A Green row belongs to the depth-one sector precisely when it has no
second ancestor. -/
noncomputable def greenDepthOneCoordinate
    (omega : AdmissibleInfinitePartition) (e : GreenEvent) (f : State) : ℂ :=
  if HasGrandparent e then 0 else greenCoordinate omega e f

/-- A Green row belongs to the paper bulk precisely when it has a second
ancestor. -/
noncomputable def greenBulkCoordinate
    (omega : AdmissibleInfinitePartition) (e : GreenEvent) (f : State) : ℂ :=
  if HasGrandparent e then greenCoordinate omega e f else 0

@[simp]
theorem greenDepthOneCoordinate_eq_zero_of_hasGrandparent
    (omega : AdmissibleInfinitePartition) (e : GreenEvent) (f : State)
    (h : HasGrandparent e) :
    greenDepthOneCoordinate omega e f = 0 := by
  simp [greenDepthOneCoordinate, h]

@[simp]
theorem greenBulkCoordinate_eq_zero_of_not_hasGrandparent
    (omega : AdmissibleInfinitePartition) (e : GreenEvent) (f : State)
    (h : ¬ HasGrandparent e) :
    greenBulkCoordinate omega e f = 0 := by
  simp [greenBulkCoordinate, h]

/-- The two masked coordinates recombine to the original Green coordinate. -/
theorem greenDepthOneCoordinate_add_greenBulkCoordinate
    (omega : AdmissibleInfinitePartition) (e : GreenEvent) (f : State) :
    greenDepthOneCoordinate omega e f + greenBulkCoordinate omega e f =
      greenCoordinate omega e f := by
  by_cases h : HasGrandparent e <;>
    simp [greenDepthOneCoordinate, greenBulkCoordinate, h]

/-- Pointwise orthogonality of the two masks, stated at the energy level. -/
theorem greenCoordinate_normSq_eq_depthOne_add_bulk
    (omega : AdmissibleInfinitePartition) (e : GreenEvent) (f : State) :
    Complex.normSq (greenCoordinate omega e f) =
      Complex.normSq (greenDepthOneCoordinate omega e f) +
        Complex.normSq (greenBulkCoordinate omega e f) := by
  by_cases h : HasGrandparent e <;>
    simp [greenDepthOneCoordinate, greenBulkCoordinate, h]

/-- The depth-one mask is pointwise dominated by the global Green energy. -/
theorem greenDepthOneCoordinate_normSq_le
    (omega : AdmissibleInfinitePartition) (e : GreenEvent) (f : State) :
    Complex.normSq (greenDepthOneCoordinate omega e f) ≤
      Complex.normSq (greenCoordinate omega e f) := by
  by_cases h : HasGrandparent e <;>
    simp [greenDepthOneCoordinate, h, Complex.normSq_nonneg]

/-- The bulk mask is pointwise dominated by the global Green energy. -/
theorem greenBulkCoordinate_normSq_le
    (omega : AdmissibleInfinitePartition) (e : GreenEvent) (f : State) :
    Complex.normSq (greenBulkCoordinate omega e f) ≤
      Complex.normSq (greenCoordinate omega e f) := by
  by_cases h : HasGrandparent e <;>
    simp [greenBulkCoordinate, h, Complex.normSq_nonneg]

/-- Depth-one Green energies are summable. -/
theorem greenDepthOneCoordinate_normSq_summable
    (omega : AdmissibleInfinitePartition) (f : State) :
    Summable (fun e : GreenEvent =>
      Complex.normSq (greenDepthOneCoordinate omega e f)) :=
  Summable.of_nonneg_of_le
    (fun e => Complex.normSq_nonneg _)
    (fun e => greenDepthOneCoordinate_normSq_le omega e f)
    (greenCoordinate_normSq_summable omega f)

/-- Bulk Green energies are summable. -/
theorem greenBulkCoordinate_normSq_summable
    (omega : AdmissibleInfinitePartition) (f : State) :
    Summable (fun e : GreenEvent =>
      Complex.normSq (greenBulkCoordinate omega e f)) :=
  Summable.of_nonneg_of_le
    (fun e => Complex.normSq_nonneg _)
    (fun e => greenBulkCoordinate_normSq_le omega e f)
    (greenCoordinate_normSq_summable omega f)

end GreenFrame.Concrete
