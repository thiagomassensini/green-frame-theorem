import GreenFrame.Concrete.Finite.L2CoordinateMask
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Contractive maps on Hilbert L2 products

Reusable product checkpoint for assembling the nested finite coefficient
cutoff and its seed-residual projection.
-/

noncomputable section

open scoped InnerProductSpace lp

namespace GreenFrame.Concrete

variable {E B : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [NormedAddCommGroup B] [InnerProductSpace ℂ B]

abbrev L2Product (E B : Type*) := WithLp 2 (E × B)

/-- Apply one continuous linear map in each orthogonal product sector. -/
noncomputable def l2ProductMap
    (A : E →L[ℂ] E) (C : B →L[ℂ] B) :
    L2Product E B →L[ℂ] L2Product E B :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ E B).symm.toContinuousLinearMap.comp
    ((A.prodMap C).comp
      (WithLp.prodContinuousLinearEquiv 2 ℂ E B).toContinuousLinearMap)

@[simp]
theorem l2ProductMap_apply
    (A : E →L[ℂ] E) (C : B →L[ℂ] B)
    (y : L2Product E B) :
    l2ProductMap A C y =
      WithLp.toLp 2 (A (WithLp.ofLp y).1, C (WithLp.ofLp y).2) := by
  rfl

/-- Componentwise contractions give an L2-product contraction. -/
theorem l2ProductMap_norm_le
    (A : E →L[ℂ] E) (C : B →L[ℂ] B)
    (hA : ∀ x, ‖A x‖ ≤ ‖x‖) (hC : ∀ z, ‖C z‖ ≤ ‖z‖)
    (y : L2Product E B) :
    ‖l2ProductMap A C y‖ ≤ ‖y‖ := by
  have hAsq : ‖A (WithLp.ofLp y).1‖ ^ 2 ≤ ‖(WithLp.ofLp y).1‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hA _)
  have hCsq : ‖C (WithLp.ofLp y).2‖ ^ 2 ≤ ‖(WithLp.ofLp y).2‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hC _)
  have hout := WithLp.prod_norm_sq_eq_of_L2 (l2ProductMap A C y)
  have hin := WithLp.prod_norm_sq_eq_of_L2 y
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [hout, hin]
  change ‖A (WithLp.ofLp y).1‖ ^ 2 + ‖C (WithLp.ofLp y).2‖ ^ 2 ≤ ‖(WithLp.ofLp y).1‖ ^ 2 + ‖(WithLp.ofLp y).2‖ ^ 2
  exact add_le_add hAsq hCsq

/-- Componentwise idempotence gives product idempotence. -/
theorem l2ProductMap_idempotent
    (A : E →L[ℂ] E) (C : B →L[ℂ] B)
    (hA : A.comp A = A) (hC : C.comp C = C) :
    (l2ProductMap A C).comp (l2ProductMap A C) = l2ProductMap A C := by
  ext y; simpa only [ContinuousLinearMap.comp_apply, l2ProductMap_apply, WithLp.toLp_fst, WithLp.toLp_snd] using congrArg (WithLp.toLp 2) (Prod.ext (by simpa only [ContinuousLinearMap.comp_apply] using DFunLike.congr_fun hA (WithLp.ofLp y).1) (by simpa only [ContinuousLinearMap.comp_apply] using DFunLike.congr_fun hC (WithLp.ofLp y).2))

/-- First orthogonal coordinate as a bounded projection. -/
noncomputable def l2FirstProjection : L2Product E B →L[ℂ] E :=
  WithLp.fstL 2 ℂ E B

@[simp]
theorem l2FirstProjection_apply (y : L2Product E B) :
    l2FirstProjection y = (WithLp.ofLp y).1 :=
  rfl

/-- The first-coordinate projection is contractive. -/
theorem l2FirstProjection_norm_le (y : L2Product E B) :
    ‖l2FirstProjection y‖ ≤ ‖y‖ := by
  have hsum := WithLp.prod_norm_sq_eq_of_L2 y
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [hsum]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Strong convergence in both factors gives strong convergence of the product maps. -/
theorem l2ProductMap_tendsto
    (A : ℕ → E →L[ℂ] E) (C : ℕ → B →L[ℂ] B)
    (hA : ∀ x, Filter.Tendsto (fun N => A N x) Filter.atTop (nhds x))
    (hC : ∀ z, Filter.Tendsto (fun N => C N z) Filter.atTop (nhds z))
    (y : L2Product E B) :
    Filter.Tendsto (fun N => l2ProductMap (A N) (C N) y)
      Filter.atTop (nhds y) := by
  have hpair := (hA (WithLp.ofLp y).1).prodMk
    (hC (WithLp.ofLp y).2)
  rw [← nhds_prod_eq] at hpair
  have hmap := (WithLp.prodContinuousLinearEquiv 2 ℂ E B).symm.continuous.continuousAt.tendsto.comp
    hpair
  change Filter.Tendsto
    (fun N => WithLp.toLp 2
      (A N (WithLp.ofLp y).1, C N (WithLp.ofLp y).2))
    Filter.atTop (nhds y) at hmap
  exact hmap

end GreenFrame.Concrete
