import GreenFrame.Concrete.Analysis.GreenDepthCoordinates

/-!
# Canonical Green depth split: zero-padded energy

This checkpoint packages the two masks in the ambient Green coefficient space
and proves their exact energy recombination and inherited bounds.
-/

noncomputable section

open scoped ENNReal lp

namespace GreenFrame.Concrete

/-- Zero-padded depth-one Green vector `G₁ f`. -/
noncomputable def greenDepthOneAnalysis
    (omega : AdmissibleInfinitePartition) (f : State) :
    ℓ²(GreenEvent, ℂ) :=
  ⟨fun e => greenDepthOneCoordinate omega e f, by
    apply memℓp_gen
    apply (greenDepthOneCoordinate_normSq_summable omega f).congr
    intro e
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (Complex.sq_norm (greenDepthOneCoordinate omega e f)).symm⟩

/-- Zero-padded depth-at-least-two Green vector `G≥2 f`. -/
noncomputable def greenBulkAnalysis
    (omega : AdmissibleInfinitePartition) (f : State) :
    ℓ²(GreenEvent, ℂ) :=
  ⟨fun e => greenBulkCoordinate omega e f, by
    apply memℓp_gen
    apply (greenBulkCoordinate_normSq_summable omega f).congr
    intro e
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (Complex.sq_norm (greenBulkCoordinate omega e f)).symm⟩

@[simp]
theorem greenDepthOneAnalysis_apply
    (omega : AdmissibleInfinitePartition) (f : State) (e : GreenEvent) :
    greenDepthOneAnalysis omega f e = greenDepthOneCoordinate omega e f :=
  rfl

@[simp]
theorem greenBulkAnalysis_apply
    (omega : AdmissibleInfinitePartition) (f : State) (e : GreenEvent) :
    greenBulkAnalysis omega f e = greenBulkCoordinate omega e f :=
  rfl

/-- Coordinate formula for the squared norm of `G₁ f`. -/
theorem greenDepthOneAnalysis_norm_sq_eq
    (omega : AdmissibleInfinitePartition) (f : State) :
    ‖greenDepthOneAnalysis omega f‖ ^ 2 =
      ∑' e : GreenEvent,
        Complex.normSq (greenDepthOneCoordinate omega e f) := by
  calc
    ‖greenDepthOneAnalysis omega f‖ ^ 2 =
        ∑' e : GreenEvent,
          ‖greenDepthOneCoordinate omega e f‖ ^ (2 : ℕ) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
        greenDepthOneAnalysis_apply] using
        lp.norm_rpow_eq_tsum
          (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
          (greenDepthOneAnalysis omega f)
    _ = ∑' e : GreenEvent,
        Complex.normSq (greenDepthOneCoordinate omega e f) := by
      apply tsum_congr
      intro e
      exact Complex.sq_norm _

/-- Coordinate formula for the squared norm of `G≥2 f`. -/
theorem greenBulkAnalysis_norm_sq_eq
    (omega : AdmissibleInfinitePartition) (f : State) :
    ‖greenBulkAnalysis omega f‖ ^ 2 =
      ∑' e : GreenEvent,
        Complex.normSq (greenBulkCoordinate omega e f) := by
  calc
    ‖greenBulkAnalysis omega f‖ ^ 2 =
        ∑' e : GreenEvent,
          ‖greenBulkCoordinate omega e f‖ ^ (2 : ℕ) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
        greenBulkAnalysis_apply] using
        lp.norm_rpow_eq_tsum
          (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
          (greenBulkAnalysis omega f)
    _ = ∑' e : GreenEvent,
        Complex.normSq (greenBulkCoordinate omega e f) := by
      apply tsum_congr
      intro e
      exact Complex.sq_norm _

/-- Exact orthogonal recombination of the two depth sectors. -/
theorem greenAnalysis_norm_sq_eq_depthOne_add_bulk
    (omega : AdmissibleInfinitePartition) (f : State) :
    ‖greenAnalysis omega f‖ ^ 2 =
      ‖greenDepthOneAnalysis omega f‖ ^ 2 +
        ‖greenBulkAnalysis omega f‖ ^ 2 := by
  rw [greenAnalysis_norm_sq_eq, greenDepthOneAnalysis_norm_sq_eq,
    greenBulkAnalysis_norm_sq_eq,
    ← (greenDepthOneCoordinate_normSq_summable omega f).tsum_add
      (greenBulkCoordinate_normSq_summable omega f)]
  apply tsum_congr
  intro e
  exact greenCoordinate_normSq_eq_depthOne_add_bulk omega e f

/-- The depth-one sector is bounded by the already certified global Green
energy. -/
theorem greenDepthOneAnalysis_norm_sq_le_green
    (omega : AdmissibleInfinitePartition) (f : State) :
    ‖greenDepthOneAnalysis omega f‖ ^ 2 ≤
      ‖greenAnalysis omega f‖ ^ 2 := by
  rw [greenAnalysis_norm_sq_eq_depthOne_add_bulk]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- The paper bulk is bounded by the already certified global Green energy. -/
theorem greenBulkAnalysis_norm_sq_le_green
    (omega : AdmissibleInfinitePartition) (f : State) :
    ‖greenBulkAnalysis omega f‖ ^ 2 ≤
      ‖greenAnalysis omega f‖ ^ 2 := by
  rw [greenAnalysis_norm_sq_eq_depthOne_add_bulk]
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- Explicit Bessel bound for the depth-one Green sector. -/
theorem greenDepthOneAnalysis_norm_sq_le
    (omega : AdmissibleInfinitePartition) (f : State) :
    ‖greenDepthOneAnalysis omega f‖ ^ 2 ≤
      greenBesselConstant * ‖f‖ ^ 2 :=
  (greenDepthOneAnalysis_norm_sq_le_green omega f).trans
    (greenAnalysis_norm_sq_le omega f)

end GreenFrame.Concrete