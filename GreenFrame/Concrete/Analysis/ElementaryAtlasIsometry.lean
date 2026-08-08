import GreenFrame.Concrete.Analysis.ElementaryAtlasCamera
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Elementary atlas: exact isometry

Fourth checkpoint for `ABGF-AN-001`: seed-plus-camera packaging, exact energy
identity, bundled linear isometry, bounded operator, and canonical log-depth
specialization.
-/

open scoped ENNReal lp

namespace GreenFrame.Concrete

/-- The literal seed-plus-camera elementary atlas. -/
noncomputable def elementaryAtlas
    (omega : AdmissibleInfinitePartition) (f : State) :
    ElementaryAtlasSpace :=
  WithLp.toLp 2 (f (1 : PNat), elementaryAtlasCamera omega f)

/-- The seed-plus-camera elementary atlas is additive. -/
theorem elementaryAtlas_add
    (omega : AdmissibleInfinitePartition) (f g : State) :
    elementaryAtlas omega (f + g) =
      elementaryAtlas omega f + elementaryAtlas omega g := by
  apply WithLp.ofLp_injective 2
  simp only [elementaryAtlas, WithLp.ofLp_toLp,
    WithLp.ofLp_add, lp.coeFn_add, Pi.add_apply,
    elementaryAtlasCamera_add]
  ext <;> simp

/-- The seed-plus-camera elementary atlas is complex homogeneous. -/
theorem elementaryAtlas_smul
    (omega : AdmissibleInfinitePartition) (c : ℂ) (f : State) :
    elementaryAtlas omega (c • f) = c • elementaryAtlas omega f := by
  apply WithLp.ofLp_injective 2
  simp only [elementaryAtlas, WithLp.ofLp_toLp,
    WithLp.ofLp_smul, lp.coeFn_smul, Pi.smul_apply,
    elementaryAtlasCamera_smul, smul_eq_mul]
  ext <;> simp [smul_eq_mul]

/-- Pointwise seed-plus-camera density is exactly the state density. -/
theorem seed_add_elementaryAtlasCameraDensity
    (omega : AdmissibleInfinitePartition) (f : State) (n : PNat) :
    seedEnergyDensity f n + elementaryAtlasCameraDensity omega f n =
      Complex.normSq (f n) := by
  by_cases hn : n = 1
  · subst n
    simp [seedEnergyDensity, elementaryAtlasCameraDensity_eq]
  · simp [seedEnergyDensity, elementaryAtlasCameraDensity_eq, hn]

/-- Orthogonal component formula for the elementary atlas norm. -/
theorem elementaryAtlas_norm_sq_eq_components
    (omega : AdmissibleInfinitePartition) (f : State) :
    ‖elementaryAtlas omega f‖ ^ 2 =
      Complex.normSq (f (1 : PNat)) +
        ‖elementaryAtlasCamera omega f‖ ^ 2 := by
  simpa [elementaryAtlas, Complex.sq_norm] using
    WithLp.prod_norm_sq_eq_of_L2 (elementaryAtlas omega f)

/-- `ABGF-AN-001`: the elementary atlas preserves the norm square exactly. -/
theorem elementaryAtlas_norm_sq_eq
    (omega : AdmissibleInfinitePartition) (f : State) :
    ‖elementaryAtlas omega f‖ ^ 2 = ‖f‖ ^ 2 := by
  calc
    ‖elementaryAtlas omega f‖ ^ 2 =
        Complex.normSq (f (1 : PNat)) +
          ‖elementaryAtlasCamera omega f‖ ^ 2 :=
      elementaryAtlas_norm_sq_eq_components omega f
    _ = (∑' n : PNat, seedEnergyDensity f n) +
        ∑' n : PNat, elementaryAtlasCameraDensity omega f n := by
      rw [seedEnergyDensity_tsum_eq,
        elementaryAtlasCamera_norm_sq_eq]
    _ = ∑' n : PNat,
        (seedEnergyDensity f n +
          elementaryAtlasCameraDensity omega f n) := by
      rw [(seedEnergyDensity_summable f).tsum_add
        (elementaryAtlasCameraDensity_summable omega f)]
    _ = ∑' n : PNat, Complex.normSq (f n) := by
      apply tsum_congr
      intro n
      exact seed_add_elementaryAtlasCameraDensity omega f n
    _ = ‖f‖ ^ 2 := residualL2_normSq_tsum_eq_norm_sq f

/-- Norm-form isometry statement for the elementary atlas. -/
theorem elementaryAtlas_isometry
    (omega : AdmissibleInfinitePartition) (f : State) :
    ‖elementaryAtlas omega f‖ = ‖f‖ := by
  nlinarith [elementaryAtlas_norm_sq_eq omega f,
    norm_nonneg (elementaryAtlas omega f), norm_nonneg f]

/-- The elementary atlas bundled directly as a complex linear isometry.

This packaging uses only the pointwise partition-of-unity calculation above;
it does not pass through a frame operator or a Parseval normalization.
-/
noncomputable def elementaryAtlasLinearIsometry
    (omega : AdmissibleInfinitePartition) :
    State →ₗᵢ[ℂ] ElementaryAtlasSpace where
  toFun := elementaryAtlas omega
  map_add' := elementaryAtlas_add omega
  map_smul' := elementaryAtlas_smul omega
  norm_map' := elementaryAtlas_isometry omega

/-- Evaluation of the bundled linear isometry is the elementary atlas. -/
@[simp]
theorem elementaryAtlasLinearIsometry_apply
    (omega : AdmissibleInfinitePartition) (f : State) :
    elementaryAtlasLinearIsometry omega f = elementaryAtlas omega f :=
  rfl

/-- Function-level isometry supplied by the bundled elementary atlas. -/
theorem elementaryAtlas_isometryMap
    (omega : AdmissibleInfinitePartition) :
    Isometry (elementaryAtlas omega) :=
  (elementaryAtlasLinearIsometry omega).isometry

/-- The atlas packaged as a bounded complex linear map. -/
noncomputable def elementaryAtlasOperator
    (omega : AdmissibleInfinitePartition) :
    State →L[ℂ] ElementaryAtlasSpace :=
  (elementaryAtlasLinearIsometry omega).toContinuousLinearMap

/-- Canonical all-bases elementary atlas as a bundled linear isometry. -/
noncomputable def canonicalCarryElementaryAtlas :
    State →ₗᵢ[ℂ] ElementaryAtlasSpace :=
  elementaryAtlasLinearIsometry canonicalCarryInfinitePartition

/-- Evaluation of the canonical bundled atlas uses the canonical partition. -/
@[simp]
theorem canonicalCarryElementaryAtlas_apply (f : State) :
    canonicalCarryElementaryAtlas f =
      elementaryAtlas canonicalCarryInfinitePartition f :=
  rfl

/-- Canonical log-depth specialization of the elementary isometry. -/
theorem canonicalCarryElementaryAtlas_isometry (f : State) :
    ‖elementaryAtlas canonicalCarryInfinitePartition f‖ = ‖f‖ :=
  by
    simpa only [canonicalCarryElementaryAtlas_apply] using
      canonicalCarryElementaryAtlas.norm_map f

end GreenFrame.Concrete
