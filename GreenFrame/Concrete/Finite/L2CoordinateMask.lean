import GreenFrame.Concrete.Analysis.ResidualAnalysis

/-!
# Contractive coordinate masks on complex `ℓ²`

Reusable analytic checkpoint for the concrete finite sections.  A decidable
coordinate predicate is packaged as an idempotent contractive continuous
linear map.
-/

open scoped ENNReal lp

namespace GreenFrame.Concrete

/-- Zero every coordinate outside a decidable predicate. -/
noncomputable def l2CoordinateMask
    {iota : Type*} (keep : iota → Prop) [DecidablePred keep]
    (x : ℓ²(iota, ℂ)) : ℓ²(iota, ℂ) :=
  ⟨fun i => if keep i then x i else 0, by
    apply memℓp_gen
    have hs : Summable (fun i =>
        Complex.normSq (if keep i then x i else 0)) := by
      exact Summable.of_nonneg_of_le
        (fun i => Complex.normSq_nonneg _)
        (fun i => by
          by_cases hi : keep i <;>
            simp [hi, Complex.normSq_nonneg])
        (residualL2_normSq_summable x)
    apply hs.congr
    intro i
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (Complex.sq_norm (if keep i then x i else 0)).symm⟩

@[simp]
theorem l2CoordinateMask_apply
    {iota : Type*} (keep : iota → Prop) [DecidablePred keep]
    (x : ℓ²(iota, ℂ)) (i : iota) :
    l2CoordinateMask keep x i = if keep i then x i else 0 :=
  rfl

theorem l2CoordinateMask_add
    {iota : Type*} (keep : iota → Prop) [DecidablePred keep]
    (x y : ℓ²(iota, ℂ)) :
    l2CoordinateMask keep (x + y) =
      l2CoordinateMask keep x + l2CoordinateMask keep y := by
  apply lp.ext
  funext i
  by_cases hi : keep i <;> simp [hi]

theorem l2CoordinateMask_smul
    {iota : Type*} (keep : iota → Prop) [DecidablePred keep]
    (c : ℂ) (x : ℓ²(iota, ℂ)) :
    l2CoordinateMask keep (c • x) = c • l2CoordinateMask keep x := by
  apply lp.ext
  funext i
  by_cases hi : keep i <;> simp [hi]

theorem l2CoordinateMask_norm_sq_le
    {iota : Type*} (keep : iota → Prop) [DecidablePred keep]
    (x : ℓ²(iota, ℂ)) :
    ‖l2CoordinateMask keep x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [← residualL2_normSq_tsum_eq_norm_sq,
    ← residualL2_normSq_tsum_eq_norm_sq]
  exact (residualL2_normSq_summable (l2CoordinateMask keep x)).tsum_le_tsum
    (fun i => by
      by_cases hi : keep i <;>
        simp [hi, Complex.normSq_nonneg])
    (residualL2_normSq_summable x)

theorem l2CoordinateMask_norm_le
    {iota : Type*} (keep : iota → Prop) [DecidablePred keep]
    (x : ℓ²(iota, ℂ)) :
    ‖l2CoordinateMask keep x‖ ≤ ‖x‖ :=
  (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    (l2CoordinateMask_norm_sq_le keep x)

noncomputable def l2CoordinateMaskLinearMap
    {iota : Type*} (keep : iota → Prop) [DecidablePred keep] :
    ℓ²(iota, ℂ) →ₗ[ℂ] ℓ²(iota, ℂ) where
  toFun := l2CoordinateMask keep
  map_add' := l2CoordinateMask_add keep
  map_smul' := l2CoordinateMask_smul keep

noncomputable def l2CoordinateMaskCLM
    {iota : Type*} (keep : iota → Prop) [DecidablePred keep] :
    ℓ²(iota, ℂ) →L[ℂ] ℓ²(iota, ℂ) :=
  (l2CoordinateMaskLinearMap keep).mkContinuous 1 fun x => by
    change ‖l2CoordinateMask keep x‖ ≤ 1 * ‖x‖
    simpa using l2CoordinateMask_norm_le keep x

@[simp]
theorem l2CoordinateMaskCLM_apply
    {iota : Type*} (keep : iota → Prop) [DecidablePred keep]
    (x : ℓ²(iota, ℂ)) :
    l2CoordinateMaskCLM keep x = l2CoordinateMask keep x :=
  rfl

theorem l2CoordinateMask_idempotent
    {iota : Type*} (keep : iota → Prop) [DecidablePred keep] :
    (l2CoordinateMaskCLM keep).comp (l2CoordinateMaskCLM keep) =
      l2CoordinateMaskCLM keep := by
  ext x i
  by_cases hi : keep i <;> simp [hi]

end GreenFrame.Concrete
