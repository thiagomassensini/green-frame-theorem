import GreenFrame.Concrete.Analysis.ResidualAnalysis

/-!
# Elementary atlas: pointwise coordinates

First checkpoint for `ABGF-AN-001`: coefficient spaces, square-root camera
weights, pointwise linearity, and exact coordinate energy.
-/

open scoped ENNReal lp

namespace GreenFrame.Concrete

/-- Camera coordinates are ordered by `(number, camera code)`. -/
abbrev ElementaryAtlasEvent := PNat × ℕ

/-- The non-seed camera sector of the elementary atlas. -/
noncomputable abbrev ElementaryAtlasCameraSpace :=
  ℓ²(ElementaryAtlasEvent, ℂ)

/-- Seed plus every elementary camera coordinate. -/
noncomputable abbrev ElementaryAtlasSpace :=
  WithLp 2 (ℂ × ElementaryAtlasCameraSpace)

/-- Square-root amplitude of one elementary camera coordinate. -/
noncomputable def elementaryAtlasAmplitude
    (omega : AdmissibleInfinitePartition) (r : ℕ) (n : PNat) : ℝ :=
  Real.sqrt (omega.weight r n)

/-- Every elementary-atlas amplitude is nonnegative. -/
theorem elementaryAtlasAmplitude_nonneg
    (omega : AdmissibleInfinitePartition) (r : ℕ) (n : PNat) :
    0 ≤ elementaryAtlasAmplitude omega r n :=
  Real.sqrt_nonneg _

/-- Squaring an elementary-atlas amplitude recovers its camera weight. -/
theorem elementaryAtlasAmplitude_sq
    (omega : AdmissibleInfinitePartition) (r : ℕ) (n : PNat) :
    elementaryAtlasAmplitude omega r n ^ 2 = omega.weight r n := by
  exact Real.sq_sqrt (omega.weight_nonneg r n)

/-- The paper coordinate `sqrt(ω_r(n)) f(n)`. -/
noncomputable def elementaryAtlasCoordinate
    (omega : AdmissibleInfinitePartition)
    (e : ElementaryAtlasEvent) (f : State) : ℂ :=
  ((elementaryAtlasAmplitude omega e.2 e.1 : ℝ) : ℂ) * f e.1

/-- Every elementary-atlas coordinate vanishes on the zero state. -/
@[simp]
theorem elementaryAtlasCoordinate_zero
    (omega : AdmissibleInfinitePartition) (e : ElementaryAtlasEvent) :
    elementaryAtlasCoordinate omega e (0 : State) = 0 := by
  simp [elementaryAtlasCoordinate]

/-- Each elementary-atlas coordinate is additive in the state. -/
theorem elementaryAtlasCoordinate_add
    (omega : AdmissibleInfinitePartition) (e : ElementaryAtlasEvent)
    (f g : State) :
    elementaryAtlasCoordinate omega e (f + g) =
      elementaryAtlasCoordinate omega e f +
        elementaryAtlasCoordinate omega e g := by
  simp [elementaryAtlasCoordinate, mul_add]

/-- Each elementary-atlas coordinate is complex homogeneous in the state. -/
theorem elementaryAtlasCoordinate_smul
    (omega : AdmissibleInfinitePartition) (e : ElementaryAtlasEvent)
    (c : ℂ) (f : State) :
    elementaryAtlasCoordinate omega e (c • f) =
      c • elementaryAtlasCoordinate omega e f := by
  simp [elementaryAtlasCoordinate, smul_eq_mul]
  ring

/-- Exact energy of one elementary camera coordinate. -/
theorem elementaryAtlasCoordinate_normSq_eq
    (omega : AdmissibleInfinitePartition)
    (e : ElementaryAtlasEvent) (f : State) :
    Complex.normSq (elementaryAtlasCoordinate omega e f) =
      omega.weight e.2 e.1 * Complex.normSq (f e.1) := by
  calc
    Complex.normSq (elementaryAtlasCoordinate omega e f) =
        (elementaryAtlasAmplitude omega e.2 e.1 *
          elementaryAtlasAmplitude omega e.2 e.1) *
          Complex.normSq (f e.1) := by
      rw [elementaryAtlasCoordinate, Complex.normSq_mul,
        Complex.normSq_ofReal]
    _ = omega.weight e.2 e.1 * Complex.normSq (f e.1) := by
      rw [← pow_two, elementaryAtlasAmplitude_sq]

/-- Nonnegative elementary energy on the full number-camera product. -/
noncomputable def elementaryAtlasEnergyTerm
    (omega : AdmissibleInfinitePartition) (f : State)
    (e : ElementaryAtlasEvent) : ℝ :=
  omega.weight e.2 e.1 * Complex.normSq (f e.1)

/-- Every elementary-atlas energy term is nonnegative. -/
theorem elementaryAtlasEnergyTerm_nonneg
    (omega : AdmissibleInfinitePartition) (f : State)
    (e : ElementaryAtlasEvent) :
    0 ≤ elementaryAtlasEnergyTerm omega f e := by
  exact mul_nonneg (omega.weight_nonneg _ _)
    (Complex.normSq_nonneg _)

end GreenFrame.Concrete
