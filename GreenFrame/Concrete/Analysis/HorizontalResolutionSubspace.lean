import GreenFrame.Concrete.Analysis.ElementaryAtlas

/-!
# Horizontal subspace for one elementary camera

This file isolates the literal subspace from `ABGF-AN-002`.  Camera indices
are codes `r : ℕ`; the corresponding physical base is `basePNat r = r + 2`.
Nothing in this checkpoint refers to the Green stencil: the disappearing row
is the elementary atlas coordinate `sqrt(omega_r(n)) f(n)`.
-/

open scoped ENNReal lp

namespace GreenFrame.Concrete

/-- The paper's literal `H_a^hor`, for a physical positive-natural base `a`. -/
def horizontalStateAtBase (a : PNat) : Submodule ℂ State where
  carrier := {f | ∀ n : PNat, a ∣ n → f n = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg n hn
    simp [hf n hn, hg n hn]
  smul_mem' := by
    intro c f hf n hn
    simp [hf n hn]

/-- Membership is exactly the divisibility condition defining `H_a^hor`. -/
theorem mem_horizontalStateAtBase_iff (a : PNat) (f : State) :
    f ∈ horizontalStateAtBase a ↔
      ∀ n : PNat, a ∣ n → f n = 0 :=
  Iff.rfl

/-- Code-indexed spelling of `H_(basePNat r)^hor` for the camera API. -/
abbrev horizontalState (r : ℕ) : Submodule ℂ State :=
  horizontalStateAtBase (basePNat r)

/-- The code-indexed spelling unfolds to the paper's divisibility condition. -/
theorem mem_horizontalState_iff (r : ℕ) (f : State) :
    f ∈ horizontalState r ↔
      ∀ n : PNat, basePNat r ∣ n → f n = 0 :=
  Iff.rfl

/-- A horizontal state vanishes at every multiple of its physical base. -/
theorem horizontalState_vanishes_on_base
    (r : ℕ) (f : horizontalState r) (n : PNat)
    (hn : basePNat r ∣ n) :
    (f : State) n = 0 :=
  f.property n hn

/-- In particular, the coordinate at the physical base itself is zero. -/
@[simp]
theorem horizontalState_own_base_eq_zero
    (r : ℕ) (f : horizontalState r) :
    (f : State) (basePNat r) = 0 :=
  f.property (basePNat r) (dvd_refl _)

/-- The selected elementary-camera row is zero on its horizontal subspace. -/
theorem ownCamera_coordinate_eq_zero_on_horizontal
    (omega : AdmissibleInfinitePartition) (r : ℕ)
    (f : horizontalState r) (n : PNat) :
    elementaryAtlasCoordinate omega (n, r) (f : State) = 0 := by
  by_cases hw : omega.weight r n = 0
  · simp [elementaryAtlasCoordinate, elementaryAtlasAmplitude, hw]
  · have hdvd : basePNat r ∣ n := omega.support_dvd hw
    have hfzero : (f : State) n = 0 :=
      horizontalState_vanishes_on_base r f n hdvd
    simp [elementaryAtlasCoordinate, hfzero]

end GreenFrame.Concrete
