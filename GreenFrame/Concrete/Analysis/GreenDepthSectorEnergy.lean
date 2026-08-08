import GreenFrame.Concrete.Analysis.GreenDepthMaskedOperator

/-!
# Canonical Green depth split: literal sector energy

This checkpoint exposes the literal subtype-indexed paper sectors and proves
their exact energy recombination and the depth-one bound.
-/

noncomputable section

open scoped ENNReal lp

namespace GreenFrame.Concrete

@[simp]
theorem greenBulkAnalysisOperator_apply
    (omega : AdmissibleInfinitePartition) (f : State) :
    greenBulkAnalysisOperator omega f = greenBulkAnalysis omega f :=
  rfl

/-- Operator-norm certificate for `G₁`. -/
theorem greenDepthOneAnalysisOperator_norm_le
    (omega : AdmissibleInfinitePartition) :
    ‖greenDepthOneAnalysisOperator omega‖ ≤
      Real.sqrt greenBesselConstant := by
  simpa only [greenDepthOneAnalysisOperator] using
    LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _)
      (greenDepthOneAnalysis_norm_le omega)

/-- Operator-norm certificate for the paper bulk `G≥2`. -/
theorem greenBulkAnalysisOperator_norm_le
    (omega : AdmissibleInfinitePartition) :
    ‖greenBulkAnalysisOperator omega‖ ≤
      Real.sqrt greenBesselConstant := by
  simpa only [greenBulkAnalysisOperator] using
    LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _)
      (greenBulkAnalysis_norm_le omega)

/-! ## Literal subtype-indexed paper sectors

The zero-padded maps above make the pointwise split and estimates elementary.
For the public concrete operator we additionally expose the literal paper
index spaces.  This avoids treating extra zero coordinates as an editorial
equivalence.
-/

/-- Literal paper depth-one event type. -/
abbrev DepthOneGreenEvent :=
  ↥({e : GreenEvent | ¬ HasGrandparent e} : Set GreenEvent)

/-- Literal paper depth-at-least-two event type. -/
abbrev BulkGreenEvent :=
  ↥({e : GreenEvent | HasGrandparent e} : Set GreenEvent)

/-- Literal depth-one Green coefficient Hilbert space. -/
abbrev DepthOneGreenSpace := ℓ²(DepthOneGreenEvent, ℂ)

/-- Literal bulk Green coefficient Hilbert space. -/
abbrev BulkGreenSpace := ℓ²(BulkGreenEvent, ℂ)

/-- Restriction of the global Green coordinates to literal depth-one rows. -/
noncomputable def greenDepthOneSectorAnalysis
    (omega : AdmissibleInfinitePartition) (f : State) :
    DepthOneGreenSpace :=
  ⟨fun e => greenCoordinate omega e.1 f, by
    apply memℓp_gen
    have hs : Summable (fun e : DepthOneGreenEvent =>
        Complex.normSq (greenCoordinate omega e.1 f)) := by
      exact (greenCoordinate_normSq_summable omega f).subtype
        {e : GreenEvent | ¬ HasGrandparent e}
    apply hs.congr
    intro e
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (Complex.sq_norm (greenCoordinate omega e.1 f)).symm⟩

/-- Restriction of the global Green coordinates to literal bulk rows. -/
noncomputable def greenBulkSectorAnalysis
    (omega : AdmissibleInfinitePartition) (f : State) :
    BulkGreenSpace :=
  ⟨fun e => greenCoordinate omega e.1 f, by
    apply memℓp_gen
    have hs : Summable (fun e : BulkGreenEvent =>
        Complex.normSq (greenCoordinate omega e.1 f)) := by
      exact (greenCoordinate_normSq_summable omega f).subtype
        {e : GreenEvent | HasGrandparent e}
    apply hs.congr
    intro e
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (Complex.sq_norm (greenCoordinate omega e.1 f)).symm⟩

@[simp]
theorem greenDepthOneSectorAnalysis_apply
    (omega : AdmissibleInfinitePartition) (f : State)
    (e : DepthOneGreenEvent) :
    greenDepthOneSectorAnalysis omega f e = greenCoordinate omega e.1 f :=
  rfl

@[simp]
theorem greenBulkSectorAnalysis_apply
    (omega : AdmissibleInfinitePartition) (f : State)
    (e : BulkGreenEvent) :
    greenBulkSectorAnalysis omega f e = greenCoordinate omega e.1 f :=
  rfl

/-- Squared norm of the literal depth-one restriction. -/
theorem greenDepthOneSectorAnalysis_norm_sq_eq
    (omega : AdmissibleInfinitePartition) (f : State) :
    ‖greenDepthOneSectorAnalysis omega f‖ ^ 2 =
      ∑' e : DepthOneGreenEvent,
        Complex.normSq (greenCoordinate omega e.1 f) := by
  calc
    ‖greenDepthOneSectorAnalysis omega f‖ ^ 2 =
        ∑' e : DepthOneGreenEvent,
          ‖greenCoordinate omega e.1 f‖ ^ (2 : ℕ) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
        greenDepthOneSectorAnalysis_apply] using
        lp.norm_rpow_eq_tsum
          (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
          (greenDepthOneSectorAnalysis omega f)
    _ = ∑' e : DepthOneGreenEvent,
        Complex.normSq (greenCoordinate omega e.1 f) := by
      apply tsum_congr
      intro e
      exact Complex.sq_norm _

/-- Squared norm of the literal bulk restriction. -/
theorem greenBulkSectorAnalysis_norm_sq_eq
    (omega : AdmissibleInfinitePartition) (f : State) :
    ‖greenBulkSectorAnalysis omega f‖ ^ 2 =
      ∑' e : BulkGreenEvent,
        Complex.normSq (greenCoordinate omega e.1 f) := by
  calc
    ‖greenBulkSectorAnalysis omega f‖ ^ 2 =
        ∑' e : BulkGreenEvent,
          ‖greenCoordinate omega e.1 f‖ ^ (2 : ℕ) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
        greenBulkSectorAnalysis_apply] using
        lp.norm_rpow_eq_tsum
          (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
          (greenBulkSectorAnalysis omega f)
    _ = ∑' e : BulkGreenEvent,
        Complex.normSq (greenCoordinate omega e.1 f) := by
      apply tsum_congr
      intro e
      exact Complex.sq_norm _

/-- Literal paper-sector recombination of the global Green energy. -/
theorem greenAnalysis_norm_sq_eq_depthOneSector_add_bulkSector
    (omega : AdmissibleInfinitePartition) (f : State) :
    ‖greenAnalysis omega f‖ ^ 2 =
      ‖greenDepthOneSectorAnalysis omega f‖ ^ 2 +
        ‖greenBulkSectorAnalysis omega f‖ ^ 2 := by
  rw [greenAnalysis_norm_sq_eq, greenDepthOneSectorAnalysis_norm_sq_eq,
    greenBulkSectorAnalysis_norm_sq_eq]
  have hsplit :=
    (greenCoordinate_normSq_summable omega f).tsum_subtype_add_tsum_subtype_compl
        {e : GreenEvent | HasGrandparent e}
  have hcompl :
      ({e : GreenEvent | HasGrandparent e} : Set GreenEvent)ᶜ =
        {e : GreenEvent | ¬ HasGrandparent e} := by
    ext e
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
  rw [hcompl] at hsplit
  simpa only [Set.mem_setOf_eq, add_comm] using hsplit.symm

/-- The literal depth-one restriction inherits the global Green bound. -/
theorem greenDepthOneSectorAnalysis_norm_sq_le
    (omega : AdmissibleInfinitePartition) (f : State) :
    ‖greenDepthOneSectorAnalysis omega f‖ ^ 2 ≤
      greenBesselConstant * ‖f‖ ^ 2 := by
  calc
    ‖greenDepthOneSectorAnalysis omega f‖ ^ 2 ≤
        ‖greenDepthOneSectorAnalysis omega f‖ ^ 2 +
          ‖greenBulkSectorAnalysis omega f‖ ^ 2 :=
      le_add_of_nonneg_right (sq_nonneg _)
    _ = ‖greenAnalysis omega f‖ ^ 2 :=
      (greenAnalysis_norm_sq_eq_depthOneSector_add_bulkSector omega f).symm
    _ ≤ greenBesselConstant * ‖f‖ ^ 2 :=
      greenAnalysis_norm_sq_le omega f

end GreenFrame.Concrete