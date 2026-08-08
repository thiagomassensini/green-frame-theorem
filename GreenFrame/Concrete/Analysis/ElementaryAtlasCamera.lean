import GreenFrame.Concrete.Analysis.ElementaryAtlasSummability

/-!
# Elementary atlas: camera vector

Third checkpoint for `ABGF-AN-001`: the product coordinates as an actual
`ℓ²` vector, its linearity, and its exact norm-square formula.
-/

open scoped ENNReal lp

namespace GreenFrame.Concrete

/-- All elementary camera coordinates as an actual `ℓ²` vector. -/
noncomputable def elementaryAtlasCamera
    (omega : AdmissibleInfinitePartition) (f : State) :
    ElementaryAtlasCameraSpace :=
  ⟨fun e => elementaryAtlasCoordinate omega e f, by
    apply memℓp_gen
    apply (elementaryAtlasCoordinate_normSq_summable omega f).congr
    intro e
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (Complex.sq_norm (elementaryAtlasCoordinate omega e f)).symm⟩

/-- Evaluation of the packaged camera vector returns its literal coordinate. -/
@[simp]
theorem elementaryAtlasCamera_apply
    (omega : AdmissibleInfinitePartition) (f : State)
    (e : ElementaryAtlasEvent) :
    elementaryAtlasCamera omega f e =
      elementaryAtlasCoordinate omega e f :=
  rfl

/-- The packaged elementary camera vector is additive. -/
theorem elementaryAtlasCamera_add
    (omega : AdmissibleInfinitePartition) (f g : State) :
    elementaryAtlasCamera omega (f + g) =
      elementaryAtlasCamera omega f + elementaryAtlasCamera omega g := by
  apply lp.ext
  funext e
  exact elementaryAtlasCoordinate_add omega e f g

/-- The packaged elementary camera vector is complex homogeneous. -/
theorem elementaryAtlasCamera_smul
    (omega : AdmissibleInfinitePartition) (c : ℂ) (f : State) :
    elementaryAtlasCamera omega (c • f) =
      c • elementaryAtlasCamera omega f := by
  apply lp.ext
  funext e
  exact elementaryAtlasCoordinate_smul omega e c f

/-- Camera-sector energy is the sum of the camera densities. -/
theorem elementaryAtlasCamera_norm_sq_eq
    (omega : AdmissibleInfinitePartition) (f : State) :
    ‖elementaryAtlasCamera omega f‖ ^ 2 =
      ∑' n : PNat, elementaryAtlasCameraDensity omega f n := by
  calc
    ‖elementaryAtlasCamera omega f‖ ^ 2 =
        ∑' e : ElementaryAtlasEvent,
          Complex.normSq (elementaryAtlasCamera omega f e) :=
      (residualL2_normSq_tsum_eq_norm_sq
        (elementaryAtlasCamera omega f)).symm
    _ = ∑' e : ElementaryAtlasEvent,
        elementaryAtlasEnergyTerm omega f e := by
      apply tsum_congr
      intro e
      simpa only [elementaryAtlasCamera_apply,
        elementaryAtlasEnergyTerm] using
        elementaryAtlasCoordinate_normSq_eq omega e f
    _ = ∑' n : PNat, ∑' r : ℕ,
        elementaryAtlasEnergyTerm omega f (n, r) :=
      (elementaryAtlasEnergyTerm_summable omega f).tsum_prod
    _ = ∑' n : PNat, elementaryAtlasCameraDensity omega f n := by
      rfl

end GreenFrame.Concrete
