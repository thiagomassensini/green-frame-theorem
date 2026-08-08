import GreenFrame.Concrete.Analysis.InfinitePartition

/-!
# The complex all-bases Green stencil

This file contains the exact pointwise Green/TFVD formula.  It deliberately
stops before the global summability argument: later modules sum the pointwise
majorant proved here over the countable event space.
-/

open scoped ENNReal lp

namespace GreenFrame.Concrete

/-- The complex state space on the positive integers. -/
abbrev State := ℓ²(PositiveIndex, ℂ)

/-- The carry-normalizing ratio `b⁻¹⁄²`, written in a form convenient
for exact square-root algebra. -/
noncomputable def carryRatio (r : ℕ) : ℝ :=
  (Real.sqrt (baseReal r))⁻¹

/-- Every carry ratio is strictly positive. -/
theorem carryRatio_pos (r : ℕ) : 0 < carryRatio r := by
  exact inv_pos.mpr (Real.sqrt_pos.2 (baseReal_pos r))

/-- Every carry ratio is nonnegative. -/
theorem carryRatio_nonneg (r : ℕ) : 0 ≤ carryRatio r :=
  (carryRatio_pos r).le

/-- The square-root definition is exactly the real power `b⁻¹⁄²`. -/
theorem carryRatio_eq_rpow_neg_half (r : ℕ) :
    carryRatio r = baseReal r ^ (-(1 : ℝ) / 2) := by
  calc
    carryRatio r = (Real.sqrt (baseReal r))⁻¹ := rfl
    _ = Real.sqrt (baseReal r) ^ (-1 : ℝ) :=
      (Real.rpow_neg_one _).symm
    _ = baseReal r ^ ((-1 : ℝ) / 2) :=
      (Real.rpow_div_two_eq_sqrt (-1) (baseReal_nonneg r)).symm

/-- Squaring the carry ratio gives the reciprocal base. -/
theorem carryRatio_sq (r : ℕ) :
    carryRatio r ^ 2 = (baseReal r)⁻¹ := by
  rw [carryRatio, inv_pow, Real.sq_sqrt (baseReal_nonneg r)]

/-- Division-form restatement of `carryRatio_sq`. -/
theorem carryRatio_sq_eq_one_div (r : ℕ) :
    carryRatio r ^ 2 = 1 / baseReal r := by
  simpa [one_div] using carryRatio_sq r

/-- An event has a second ancestor precisely when its parent is again
divisible by the same base. -/
def HasGrandparent (e : GreenEvent) : Prop :=
  (basePNat e.1 : ℕ) ∣ (e.2 : ℕ)

/-- The parent-divisibility test is exactly the global indicator `b² ∣ n`
at the current event number. -/
theorem hasGrandparent_iff_base_sq_dvd_event (e : GreenEvent) :
    HasGrandparent e ↔ (basePNat e.1 : ℕ) ^ 2 ∣ (eventNumber e : ℕ) := by
  have hb : (basePNat e.1 : ℕ) ≠ 0 := PNat.ne_zero _
  simpa [HasGrandparent, eventNumber_coe, basePNat, pow_two] using
    (mul_dvd_mul_iff_left hb).symm

/-- The exact positive quotient used for the second ancestor. -/
def grandparentIndex (e : GreenEvent) : PositiveIndex :=
  PNat.divExact e.2 (basePNat e.1)

/-- On a depth-at-least-two event, multiplying the grandparent by the base
recovers the parent. -/
theorem base_mul_grandparentIndex {e : GreenEvent} (h : HasGrandparent e) :
    basePNat e.1 * grandparentIndex e = e.2 := by
  exact PNat.mul_div_exact (PNat.dvd_iff.mpr h)

/-- The current-node contribution to the stencil. -/
def currentTerm (e : GreenEvent) (f : State) : ℂ :=
  f (eventNumber e)

/-- The first-ancestor contribution `-2 q_b f(m)`. -/
noncomputable def parentTerm (e : GreenEvent) (f : State) : ℂ :=
  -(((2 * carryRatio e.1 : ℝ) : ℂ) * f e.2)

/-- The conditional second-ancestor contribution `q_b² f(m / b)`. -/
noncomputable def grandparentTerm (e : GreenEvent) (f : State) : ℂ :=
  if HasGrandparent e then
    ((carryRatio e.1 ^ 2 : ℝ) : ℂ) * f (grandparentIndex e)
  else
    0

/-- The exact three-point carry-normalized vertical Green stencil.  Since an
event is `(r,m)` with current node `b*m`, the indicator on the third term is
equivalent to the paper's condition `b² ∣ b*m`. -/
noncomputable def verticalGreenStencil (e : GreenEvent) (f : State) : ℂ :=
  currentTerm e f + parentTerm e f + grandparentTerm e f

/-- The vertical stencil vanishes on the zero state. -/
@[simp]
theorem verticalGreenStencil_zero (e : GreenEvent) :
    verticalGreenStencil e (0 : State) = 0 := by
  simp [verticalGreenStencil, currentTerm, parentTerm, grandparentTerm]

/-- The vertical stencil is additive. -/
theorem verticalGreenStencil_add (e : GreenEvent) (f g : State) :
    verticalGreenStencil e (f + g) =
      verticalGreenStencil e f + verticalGreenStencil e g := by
  by_cases h : HasGrandparent e <;>
    simp [verticalGreenStencil, currentTerm, parentTerm, grandparentTerm, h,
      mul_add] <;>
    ring

/-- The vertical stencil is complex homogeneous. -/
theorem verticalGreenStencil_smul (e : GreenEvent) (c : ℂ) (f : State) :
    verticalGreenStencil e (c • f) = c • verticalGreenStencil e f := by
  by_cases h : HasGrandparent e <;>
    simp [verticalGreenStencil, currentTerm, parentTerm, grandparentTerm, h,
      smul_eq_mul, mul_add] <;>
    ring

/-- The pointwise vertical stencil packaged as a complex linear map. -/
noncomputable def verticalGreenStencilLinearMap (e : GreenEvent) :
    State →ₗ[ℂ] ℂ where
  toFun := verticalGreenStencil e
  map_add' := verticalGreenStencil_add e
  map_smul' := verticalGreenStencil_smul e

/-- Evaluation formula for the packaged stencil map. -/
@[simp]
theorem verticalGreenStencilLinearMap_apply (e : GreenEvent) (f : State) :
    verticalGreenStencilLinearMap e f = verticalGreenStencil e f :=
  rfl

/-- Green-transmitted mass `ω_b(n) / b` at an event. -/
noncomputable def greenEventMass (omega : AdmissibleInfinitePartition) (e : GreenEvent) : ℝ :=
  omega.weight e.1 (eventNumber e) / baseReal e.1

/-- Green-transmitted mass is nonnegative. -/
theorem greenEventMass_nonneg (omega : AdmissibleInfinitePartition) (e : GreenEvent) :
    0 ≤ greenEventMass omega e := by
  exact div_nonneg (omega.weight_nonneg _ _) (baseReal_nonneg _)

/-- The Green amplitude `sqrt(ω_b(n) / b)`. -/
noncomputable def greenAmplitude
    (omega : AdmissibleInfinitePartition) (e : GreenEvent) : ℝ :=
  Real.sqrt (greenEventMass omega e)

/-- Every Green amplitude is nonnegative. -/
theorem greenAmplitude_nonneg
    (omega : AdmissibleInfinitePartition) (e : GreenEvent) :
    0 ≤ greenAmplitude omega e := by
  exact Real.sqrt_nonneg _

/-- The amplitude square recovers the transmitted Green mass exactly. -/
theorem greenAmplitude_sq
    (omega : AdmissibleInfinitePartition) (e : GreenEvent) :
    greenAmplitude omega e ^ 2 = greenEventMass omega e := by
  exact Real.sq_sqrt (greenEventMass_nonneg omega e)

/-- The pointwise weighted Green-analysis coordinate. -/
noncomputable def greenCoordinate
    (omega : AdmissibleInfinitePartition) (e : GreenEvent) (f : State) : ℂ :=
  ((greenAmplitude omega e : ℝ) : ℂ) * verticalGreenStencil e f

/-- A Green coordinate vanishes on the zero state. -/
@[simp]
theorem greenCoordinate_zero
    (omega : AdmissibleInfinitePartition) (e : GreenEvent) :
    greenCoordinate omega e (0 : State) = 0 := by
  simp [greenCoordinate]

/-- Each Green coordinate is additive in the state. -/
theorem greenCoordinate_add
    (omega : AdmissibleInfinitePartition) (e : GreenEvent) (f g : State) :
    greenCoordinate omega e (f + g) =
      greenCoordinate omega e f + greenCoordinate omega e g := by
  simp [greenCoordinate, verticalGreenStencil_add, mul_add]

/-- Each Green coordinate is complex homogeneous in the state. -/
theorem greenCoordinate_smul
    (omega : AdmissibleInfinitePartition) (e : GreenEvent) (c : ℂ) (f : State) :
    greenCoordinate omega e (c • f) = c • greenCoordinate omega e f := by
  simp [greenCoordinate, verticalGreenStencil_smul, smul_eq_mul]
  ring

/-- A pointwise Green coordinate packaged as a complex linear map. -/
noncomputable def greenCoordinateLinearMap
    (omega : AdmissibleInfinitePartition) (e : GreenEvent) : State →ₗ[ℂ] ℂ where
  toFun := greenCoordinate omega e
  map_add' := greenCoordinate_add omega e
  map_smul' := greenCoordinate_smul omega e

/-- Evaluation formula for the packaged Green-coordinate map. -/
@[simp]
theorem greenCoordinateLinearMap_apply
    (omega : AdmissibleInfinitePartition) (e : GreenEvent) (f : State) :
    greenCoordinateLinearMap omega e f = greenCoordinate omega e f :=
  rfl

/-- The norm square of a weighted coordinate is mass times the stencil norm
square. -/
theorem greenCoordinate_normSq_eq
    (omega : AdmissibleInfinitePartition) (e : GreenEvent) (f : State) :
    Complex.normSq (greenCoordinate omega e f) =
      greenEventMass omega e * Complex.normSq (verticalGreenStencil e f) := by
  calc
    Complex.normSq (greenCoordinate omega e f) =
        (greenAmplitude omega e * greenAmplitude omega e) *
          Complex.normSq (verticalGreenStencil e f) := by
      rw [greenCoordinate, Complex.normSq_mul, Complex.normSq_ofReal]
    _ = greenEventMass omega e * Complex.normSq (verticalGreenStencil e f) := by
      rw [← pow_two, greenAmplitude_sq]

/-- Elementary real three-term Cauchy inequality. -/
theorem real_sum_three_sq_le (x y z : ℝ) :
    (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]

/-- Three-term Cauchy inequality for complex norm squares. -/
theorem complex_sum_three_normSq_le (x y z : ℂ) :
    Complex.normSq (x + y + z) ≤
      3 * (Complex.normSq x + Complex.normSq y + Complex.normSq z) := by
  have hnorm : ‖x + y + z‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ := by
    calc
      ‖x + y + z‖ ≤ ‖x + y‖ + ‖z‖ := norm_add_le _ _
      _ ≤ (‖x‖ + ‖y‖) + ‖z‖ := add_le_add_right (norm_add_le _ _) _
      _ = ‖x‖ + ‖y‖ + ‖z‖ := rfl
  have hsquare :
      ‖x + y + z‖ ^ 2 ≤ (‖x‖ + ‖y‖ + ‖z‖) ^ 2 := by
    nlinarith [norm_nonneg (x + y + z), norm_nonneg x, norm_nonneg y, norm_nonneg z]
  calc
    Complex.normSq (x + y + z) = ‖x + y + z‖ ^ 2 :=
      (Complex.sq_norm _).symm
    _ ≤ (‖x‖ + ‖y‖ + ‖z‖) ^ 2 := hsquare
    _ ≤ 3 * (‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2) :=
      real_sum_three_sq_le _ _ _
    _ = 3 * (Complex.normSq x + Complex.normSq y + Complex.normSq z) := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]

/-- Exact norm square of the first-ancestor term. -/
theorem parentTerm_normSq (e : GreenEvent) (f : State) :
    Complex.normSq (parentTerm e f) =
      4 * carryRatio e.1 ^ 2 * Complex.normSq (f e.2) := by
  rw [parentTerm, Complex.normSq_neg, Complex.normSq_mul, Complex.normSq_ofReal]
  ring

/-- Exact norm square of the conditional second-ancestor term. -/
theorem grandparentTerm_normSq (e : GreenEvent) (f : State) :
    Complex.normSq (grandparentTerm e f) =
      if HasGrandparent e then
        carryRatio e.1 ^ 4 * Complex.normSq (f (grandparentIndex e))
      else
        0 := by
  by_cases h : HasGrandparent e
  · simp [grandparentTerm, h, Complex.normSq_mul, Complex.normSq_ofReal]
    ring
  · simp [grandparentTerm, h]

/-- The unweighted stencil satisfies the pointwise three-term norm-square
bound, with all carry coefficients exposed. -/
theorem verticalGreenStencil_normSq_le (e : GreenEvent) (f : State) :
    Complex.normSq (verticalGreenStencil e f) ≤
      3 *
        (Complex.normSq (f (eventNumber e)) +
          4 * carryRatio e.1 ^ 2 * Complex.normSq (f e.2) +
          if HasGrandparent e then
            carryRatio e.1 ^ 4 * Complex.normSq (f (grandparentIndex e))
          else
            0) := by
  calc
    Complex.normSq (verticalGreenStencil e f) ≤
        3 *
          (Complex.normSq (currentTerm e f) +
            Complex.normSq (parentTerm e f) +
            Complex.normSq (grandparentTerm e f)) := by
      exact complex_sum_three_normSq_le _ _ _
    _ = 3 *
        (Complex.normSq (f (eventNumber e)) +
          4 * carryRatio e.1 ^ 2 * Complex.normSq (f e.2) +
          if HasGrandparent e then
            carryRatio e.1 ^ 4 * Complex.normSq (f (grandparentIndex e))
          else
            0) := by
      rw [parentTerm_normSq, grandparentTerm_normSq]
      rfl

/-- The weighted Green coordinate satisfies the exact pointwise majorant
used by the global Bessel summation. -/
theorem greenCoordinate_normSq_le (omega : AdmissibleInfinitePartition)
    (e : GreenEvent) (f : State) :
    Complex.normSq (greenCoordinate omega e f) ≤
      3 * greenEventMass omega e *
        (Complex.normSq (f (eventNumber e)) +
          4 * carryRatio e.1 ^ 2 * Complex.normSq (f e.2) +
          if HasGrandparent e then
            carryRatio e.1 ^ 4 * Complex.normSq (f (grandparentIndex e))
          else
            0) := by
  rw [greenCoordinate_normSq_eq]
  calc
    greenEventMass omega e * Complex.normSq (verticalGreenStencil e f) ≤
        greenEventMass omega e *
          (3 *
            (Complex.normSq (f (eventNumber e)) +
              4 * carryRatio e.1 ^ 2 * Complex.normSq (f e.2) +
              if HasGrandparent e then
                carryRatio e.1 ^ 4 * Complex.normSq (f (grandparentIndex e))
              else
                0)) := by
      exact mul_le_mul_of_nonneg_left (verticalGreenStencil_normSq_le e f)
        (greenEventMass_nonneg omega e)
    _ = 3 * greenEventMass omega e *
        (Complex.normSq (f (eventNumber e)) +
          4 * carryRatio e.1 ^ 2 * Complex.normSq (f e.2) +
          if HasGrandparent e then
            carryRatio e.1 ^ 4 * Complex.normSq (f (grandparentIndex e))
          else
            0) := by ring

/-- Fully expanded amplitude version of the pointwise Green bound. -/
theorem greenCoordinate_normSq_le_explicit
    (omega : AdmissibleInfinitePartition) (e : GreenEvent) (f : State) :
    Complex.normSq (greenCoordinate omega e f) ≤
      3 * (omega.weight e.1 (eventNumber e) / baseReal e.1) *
        (Complex.normSq (f (eventNumber e)) +
          4 * carryRatio e.1 ^ 2 * Complex.normSq (f e.2) +
          if HasGrandparent e then
            carryRatio e.1 ^ 4 * Complex.normSq (f (grandparentIndex e))
          else
            0) := by
  simpa [greenEventMass] using greenCoordinate_normSq_le omega e f

end GreenFrame.Concrete
