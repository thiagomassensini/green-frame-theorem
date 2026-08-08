import GreenFrame.Concrete.Analysis.ResidualCoordinates
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Global residual analysis and seed-return bounds

This is the second residual checkpoint.  It uses Tonelli for the nonnegative
residual energy, packages the pointwise coordinates in an actual `ℓ²` vector,
constructs bounded linear residual and seed-residual analyses, and proves the
exact universal bounds `1/2` and `1` without a frame-bound hypothesis.
-/

open scoped ENNReal lp

namespace GreenFrame.Concrete

/-- Complex norm squares of every `ℓ²` vector form a summable family. -/
theorem residualL2_normSq_summable {iota : Type*} (x : ℓ²(iota, ℂ)) :
    Summable (fun i => Complex.normSq (x i)) := by
  apply ((lp.memℓp x).summable
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).congr
  intro i
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    Complex.sq_norm (x i)

/-- The `ℓ²` norm square is exactly the sum of coordinate norm squares. -/
theorem residualL2_normSq_tsum_eq_norm_sq {iota : Type*} (x : ℓ²(iota, ℂ)) :
    (∑' i, Complex.normSq (x i)) = ‖x‖ ^ 2 := by
  calc
    (∑' i, Complex.normSq (x i)) =
        ∑' i, ‖x i‖ ^ (2 : ℕ) := by
      apply tsum_congr
      intro i
      simpa only using (Complex.sq_norm (x i)).symm
    _ = ‖x‖ ^ 2 := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (lp.norm_rpow_eq_tsum
          (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x).symm

/-- Nonnegative summand on the full number-camera residual product. -/
noncomputable def residualEnergyTerm
    (omega : AdmissibleInfinitePartition) (f : State)
    (e : ResidualEvent) : ℝ :=
  residualEventMass omega e.2 e.1 * Complex.normSq (f e.1)

/-- Every residual energy summand is nonnegative. -/
theorem residualEnergyTerm_nonneg
    (omega : AdmissibleInfinitePartition) (f : State)
    (e : ResidualEvent) :
    0 ≤ residualEnergyTerm omega f e := by
  exact mul_nonneg
    (residualEventMass_nonneg omega e.2 e.1)
    (Complex.normSq_nonneg _)

/-- Residual energy after summing all cameras at one number. -/
noncomputable def residualEnergyDensity
    (omega : AdmissibleInfinitePartition) (f : State) (n : PNat) : ℝ :=
  residualCameraMass omega n * Complex.normSq (f n)

/-- Every camera-summed residual energy density is nonnegative. -/
theorem residualEnergyDensity_nonneg
    (omega : AdmissibleInfinitePartition) (f : State) (n : PNat) :
    0 ≤ residualEnergyDensity omega f n := by
  exact mul_nonneg
    (residualCameraMass_nonneg omega n)
    (Complex.normSq_nonneg _)

/-- Camera-summed residual energy is bounded by the original coordinate energy. -/
theorem residualEnergyDensity_le
    (omega : AdmissibleInfinitePartition) (f : State) (n : PNat) :
    residualEnergyDensity omega f n ≤ Complex.normSq (f n) := by
  exact mul_le_of_le_one_left
    (Complex.normSq_nonneg _)
    (residualCameraMass_le_one omega n)

/-- The camera-summed residual energy is summable over state coordinates. -/
theorem residualEnergyDensity_summable
    (omega : AdmissibleInfinitePartition) (f : State) :
    Summable (fun n => residualEnergyDensity omega f n) := by
  exact Summable.of_nonneg_of_le
    (fun n => residualEnergyDensity_nonneg omega f n)
    (fun n => residualEnergyDensity_le omega f n)
    (residualL2_normSq_summable f)

/-- Tonelli summability of the complete residual array. -/
theorem residualEnergyTerm_summable
    (omega : AdmissibleInfinitePartition) (f : State) :
    Summable (fun e : ResidualEvent => residualEnergyTerm omega f e) := by
  refine
    (summable_prod_of_nonneg
      (fun e => residualEnergyTerm_nonneg omega f e)).2 ?_
  constructor
  · intro n
    simpa only [residualEnergyTerm] using
      (residualEventMass_summable omega n).mul_right
        (Complex.normSq (f n))
  · simpa only [residualEnergyTerm, residualEnergyDensity,
      residualCameraMass, tsum_mul_right] using
      residualEnergyDensity_summable omega f

/-- The actual pointwise residual coordinate norm squares are summable. -/
theorem residualCoordinate_normSq_summable
    (omega : AdmissibleInfinitePartition) (f : State) :
    Summable
      (fun e : ResidualEvent =>
        Complex.normSq (residualCoordinate omega e f)) := by
  exact (residualEnergyTerm_summable omega f).congr fun e =>
    (residualCoordinate_normSq_eq omega e f).symm

/-- The raw residual coordinates packaged as an actual `ℓ²` vector. -/
noncomputable def residualAnalysis
    (omega : AdmissibleInfinitePartition) (f : State) : ResidualSpace :=
  ⟨fun e => residualCoordinate omega e f, by
    apply memℓp_gen
    apply (residualCoordinate_normSq_summable omega f).congr
    intro e
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (Complex.sq_norm (residualCoordinate omega e f)).symm⟩

/-- Evaluation formula for the packaged residual analysis. -/
@[simp]
theorem residualAnalysis_apply
    (omega : AdmissibleInfinitePartition) (f : State)
    (e : ResidualEvent) :
    residualAnalysis omega f e = residualCoordinate omega e f :=
  rfl

/-- Residual analysis is additive. -/
theorem residualAnalysis_add
    (omega : AdmissibleInfinitePartition) (f g : State) :
    residualAnalysis omega (f + g) =
      residualAnalysis omega f + residualAnalysis omega g := by
  apply lp.ext
  funext e
  exact residualCoordinate_add omega e f g

/-- Residual analysis is complex homogeneous. -/
theorem residualAnalysis_smul
    (omega : AdmissibleInfinitePartition) (c : ℂ) (f : State) :
    residualAnalysis omega (c • f) =
      c • residualAnalysis omega f := by
  apply lp.ext
  funext e
  exact residualCoordinate_smul omega e c f

/-- Residual analysis packaged as a complex linear map. -/
noncomputable def residualAnalysisLinearMap
    (omega : AdmissibleInfinitePartition) :
    State →ₗ[ℂ] ResidualSpace where
  toFun := residualAnalysis omega
  map_add' := residualAnalysis_add omega
  map_smul' := residualAnalysis_smul omega

/-- Exact Tonelli/camera formula for residual energy. -/
theorem residualAnalysis_norm_sq_eq_camera_tsum
    (omega : AdmissibleInfinitePartition) (f : State) :
    ‖residualAnalysis omega f‖ ^ 2 =
      ∑' n : PNat, residualEnergyDensity omega f n := by
  calc
    ‖residualAnalysis omega f‖ ^ 2 =
        ∑' e : ResidualEvent,
          Complex.normSq (residualAnalysis omega f e) :=
      (residualL2_normSq_tsum_eq_norm_sq
        (residualAnalysis omega f)).symm
    _ = ∑' e : ResidualEvent, residualEnergyTerm omega f e := by
      apply tsum_congr
      intro e
      simpa only [residualAnalysis_apply, residualEnergyTerm] using
        residualCoordinate_normSq_eq omega e f
    _ = ∑' n : PNat, ∑' r : ℕ,
        residualEnergyTerm omega f (n, r) :=
      (residualEnergyTerm_summable omega f).tsum_prod
    _ = ∑' n : PNat, residualEnergyDensity omega f n := by
      apply tsum_congr
      intro n
      simp only [residualEnergyTerm, residualEnergyDensity,
        residualCameraMass, tsum_mul_right]

/-- The residual operator is a contraction. -/
theorem residualAnalysis_norm_sq_le
    (omega : AdmissibleInfinitePartition) (f : State) :
    ‖residualAnalysis omega f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  rw [residualAnalysis_norm_sq_eq_camera_tsum]
  calc
    (∑' n : PNat, residualEnergyDensity omega f n)
        ≤ ∑' n : PNat, Complex.normSq (f n) :=
      (residualEnergyDensity_summable omega f).tsum_le_tsum
        (fun n => residualEnergyDensity_le omega f n)
        (residualL2_normSq_summable f)
    _ = ‖f‖ ^ 2 := residualL2_normSq_tsum_eq_norm_sq f

/-- Norm-form contraction bound for the residual operator. -/
theorem residualAnalysis_norm_le
    (omega : AdmissibleInfinitePartition) (f : State) :
    ‖residualAnalysis omega f‖ ≤ ‖f‖ :=
  (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    (residualAnalysis_norm_sq_le omega f)

/-- Residual analysis as a bounded complex linear map of norm at most one. -/
noncomputable def residualAnalysisCLM
    (omega : AdmissibleInfinitePartition) :
    State →L[ℂ] ResidualSpace :=
  (residualAnalysisLinearMap omega).mkContinuous 1 fun f => by
    change ‖residualAnalysis omega f‖ ≤ 1 * ‖f‖
    simpa using residualAnalysis_norm_le omega f

/-- Seed contribution, supported only at `n = 1`. -/
noncomputable def seedEnergyDensity (f : State) (n : PNat) : ℝ :=
  if n = 1 then Complex.normSq (f n) else 0

/-- The seed energy density is summable. -/
theorem seedEnergyDensity_summable (f : State) :
    Summable (fun n => seedEnergyDensity f n) := by
  exact Summable.of_nonneg_of_le
    (fun n => by
      by_cases hn : n = 1 <;>
        simp [seedEnergyDensity, hn, Complex.normSq_nonneg])
    (fun n => by
      by_cases hn : n = 1 <;>
        simp [seedEnergyDensity, hn, Complex.normSq_nonneg])
    (residualL2_normSq_summable f)

/-- Summing the seed density returns exactly the unit coordinate energy. -/
theorem seedEnergyDensity_tsum_eq (f : State) :
    (∑' n : PNat, seedEnergyDensity f n) =
      Complex.normSq (f (1 : PNat)) := by
  simp [seedEnergyDensity]

/-- Pointwise energy density of the orthogonal seed-residual sector. -/
noncomputable def seedResidualEnergyDensity
    (omega : AdmissibleInfinitePartition) (f : State) (n : PNat) : ℝ :=
  seedEnergyDensity f n + residualEnergyDensity omega f n

/-- Seed-residual energy density is summable. -/
theorem seedResidualEnergyDensity_summable
    (omega : AdmissibleInfinitePartition) (f : State) :
    Summable (fun n => seedResidualEnergyDensity omega f n) :=
  (seedEnergyDensity_summable f).add
    (residualEnergyDensity_summable omega f)

/-- Total seed-residual energy. -/
noncomputable def seedResidualEnergy
    (omega : AdmissibleInfinitePartition) (f : State) : ℝ :=
  ∑' n : PNat, seedResidualEnergyDensity omega f n

/-- The total density is exactly seed energy plus residual-analysis norm square. -/
theorem seedResidualEnergy_eq_seed_add_residual_norm_sq
    (omega : AdmissibleInfinitePartition) (f : State) :
    seedResidualEnergy omega f =
      Complex.normSq (f (1 : PNat)) +
        ‖residualAnalysis omega f‖ ^ 2 := by
  calc
    seedResidualEnergy omega f =
        (∑' n : PNat, seedEnergyDensity f n) +
          ∑' n : PNat, residualEnergyDensity omega f n := by
      exact (seedEnergyDensity_summable f).tsum_add
        (residualEnergyDensity_summable omega f)
    _ = Complex.normSq (f (1 : PNat)) +
        ‖residualAnalysis omega f‖ ^ 2 := by
      rw [seedEnergyDensity_tsum_eq,
        residualAnalysis_norm_sq_eq_camera_tsum]

/-- Pointwise lower bound by one half of the original state energy. -/
theorem half_state_density_le_seedResidual_density
    (omega : AdmissibleInfinitePartition) (f : State) (n : PNat) :
    (1 / 2 : ℝ) * Complex.normSq (f n) ≤
      seedResidualEnergyDensity omega f n := by
  by_cases hn : n = 1
  · subst n
    simp only [seedResidualEnergyDensity, seedEnergyDensity, if_pos,
      residualEnergyDensity, residualCameraMass_one, zero_mul, add_zero]
    nlinarith [Complex.normSq_nonneg (f (1 : PNat))]
  · simp only [seedResidualEnergyDensity, seedEnergyDensity, hn,
      if_false, zero_add, residualEnergyDensity]
    exact mul_le_mul_of_nonneg_right
      (residualCameraMass_half_le omega hn)
      (Complex.normSq_nonneg _)

/-- Pointwise seed-residual energy never exceeds the original state energy. -/
theorem seedResidual_density_le_state_density
    (omega : AdmissibleInfinitePartition) (f : State) (n : PNat) :
    seedResidualEnergyDensity omega f n ≤ Complex.normSq (f n) := by
  by_cases hn : n = 1
  · subst n
    simp [seedResidualEnergyDensity, seedEnergyDensity,
      residualEnergyDensity]
  · simp only [seedResidualEnergyDensity, seedEnergyDensity, hn,
      if_false, zero_add]
    exact residualEnergyDensity_le omega f n

/-- Universal lower seed-residual energy bound. -/
theorem seedResidualEnergy_lower
    (omega : AdmissibleInfinitePartition) (f : State) :
    (1 / 2 : ℝ) * ‖f‖ ^ 2 ≤ seedResidualEnergy omega f := by
  calc
    (1 / 2 : ℝ) * ‖f‖ ^ 2 =
        ∑' n : PNat, (1 / 2 : ℝ) * Complex.normSq (f n) := by
      rw [tsum_mul_left, residualL2_normSq_tsum_eq_norm_sq]
    _ ≤ ∑' n : PNat, seedResidualEnergyDensity omega f n :=
      ((residualL2_normSq_summable f).mul_left (1 / 2 : ℝ)).tsum_le_tsum
        (fun n => half_state_density_le_seedResidual_density omega f n)
        (seedResidualEnergyDensity_summable omega f)
    _ = seedResidualEnergy omega f := rfl

/-- Universal upper seed-residual energy bound. -/
theorem seedResidualEnergy_upper
    (omega : AdmissibleInfinitePartition) (f : State) :
    seedResidualEnergy omega f ≤ ‖f‖ ^ 2 := by
  calc
    seedResidualEnergy omega f =
        ∑' n : PNat, seedResidualEnergyDensity omega f n := rfl
    _ ≤ ∑' n : PNat, Complex.normSq (f n) :=
      (seedResidualEnergyDensity_summable omega f).tsum_le_tsum
        (fun n => seedResidual_density_le_state_density omega f n)
        (residualL2_normSq_summable f)
    _ = ‖f‖ ^ 2 := residualL2_normSq_tsum_eq_norm_sq f

/-- Seed-plus-residual bounds, derived without an assumed frame certificate. -/
theorem residual_seed_norm_sq_bounds_concrete
    (omega : AdmissibleInfinitePartition) (f : State) :
    (1 / 2 : ℝ) * ‖f‖ ^ 2 ≤
        Complex.normSq (f (1 : PNat)) +
          ‖residualAnalysis omega f‖ ^ 2 ∧
      Complex.normSq (f (1 : PNat)) +
          ‖residualAnalysis omega f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  constructor
  · calc
      (1 / 2 : ℝ) * ‖f‖ ^ 2
          ≤ seedResidualEnergy omega f :=
        seedResidualEnergy_lower omega f
      _ = Complex.normSq (f (1 : PNat)) +
          ‖residualAnalysis omega f‖ ^ 2 :=
        seedResidualEnergy_eq_seed_add_residual_norm_sq omega f
  · calc
      Complex.normSq (f (1 : PNat)) +
          ‖residualAnalysis omega f‖ ^ 2 =
          seedResidualEnergy omega f :=
        (seedResidualEnergy_eq_seed_add_residual_norm_sq omega f).symm
      _ ≤ ‖f‖ ^ 2 := seedResidualEnergy_upper omega f

/-- Orthogonal L² direct sum of seed and residual sectors. -/
noncomputable abbrev SeedResidualSpace :=
  WithLp 2 (ℂ × ResidualSpace)

/-- Concrete seed-residual analysis into its orthogonal L² direct sum. -/
noncomputable def seedResidualAnalysis
    (omega : AdmissibleInfinitePartition) (f : State) :
    SeedResidualSpace :=
  WithLp.toLp 2
    (f (1 : PNat), residualAnalysis omega f)

/-- Seed-residual analysis is additive. -/
theorem seedResidualAnalysis_add
    (omega : AdmissibleInfinitePartition) (f g : State) :
    seedResidualAnalysis omega (f + g) =
      seedResidualAnalysis omega f + seedResidualAnalysis omega g := by
  apply WithLp.ofLp_injective 2
  simp only [seedResidualAnalysis, WithLp.ofLp_toLp,
    WithLp.ofLp_add, lp.coeFn_add, Pi.add_apply,
    residualAnalysis_add]

/-- Seed-residual analysis is complex homogeneous. -/
theorem seedResidualAnalysis_smul
    (omega : AdmissibleInfinitePartition) (c : ℂ) (f : State) :
    seedResidualAnalysis omega (c • f) =
      c • seedResidualAnalysis omega f := by
  apply WithLp.ofLp_injective 2
  simp only [seedResidualAnalysis, WithLp.ofLp_toLp,
    WithLp.ofLp_smul, lp.coeFn_smul, Pi.smul_apply,
    residualAnalysis_smul, smul_eq_mul]

/-- Seed-residual analysis packaged as a complex linear map. -/
noncomputable def seedResidualAnalysisLinearMap
    (omega : AdmissibleInfinitePartition) :
    State →ₗ[ℂ] SeedResidualSpace where
  toFun := seedResidualAnalysis omega
  map_add' := seedResidualAnalysis_add omega
  map_smul' := seedResidualAnalysis_smul omega

/-- Exact orthogonal direct-sum norm identity. -/
theorem seedResidualAnalysis_norm_sq_eq
    (omega : AdmissibleInfinitePartition) (f : State) :
    ‖seedResidualAnalysis omega f‖ ^ 2 =
      Complex.normSq (f (1 : PNat)) +
        ‖residualAnalysis omega f‖ ^ 2 := by
  simpa [seedResidualAnalysis, Complex.sq_norm] using
    WithLp.prod_norm_sq_eq_of_L2
      (seedResidualAnalysis omega f)

/-- Operator-form seed-residual bounds `1/2` and `1`. -/
theorem seedResidualAnalysis_norm_sq_bounds
    (omega : AdmissibleInfinitePartition) (f : State) :
    (1 / 2 : ℝ) * ‖f‖ ^ 2 ≤
        ‖seedResidualAnalysis omega f‖ ^ 2 ∧
      ‖seedResidualAnalysis omega f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  rw [seedResidualAnalysis_norm_sq_eq]
  exact residual_seed_norm_sq_bounds_concrete omega f

/-- Norm-form contraction bound for the combined seed-residual analysis. -/
theorem seedResidualAnalysis_norm_le
    (omega : AdmissibleInfinitePartition) (f : State) :
    ‖seedResidualAnalysis omega f‖ ≤ ‖f‖ :=
  (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    (seedResidualAnalysis_norm_sq_bounds omega f).2

/-- Seed-residual analysis as a bounded complex linear map of norm at most one. -/
noncomputable def seedResidualAnalysisCLM
    (omega : AdmissibleInfinitePartition) :
    State →L[ℂ] SeedResidualSpace :=
  (seedResidualAnalysisLinearMap omega).mkContinuous 1 fun f => by
    change ‖seedResidualAnalysis omega f‖ ≤ 1 * ‖f‖
    simpa using seedResidualAnalysis_norm_le omega f

end GreenFrame.Concrete
