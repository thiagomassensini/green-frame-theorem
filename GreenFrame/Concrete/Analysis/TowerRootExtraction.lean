import GreenFrame.Concrete.Analysis.TowerTFVDCoordinates

/-!
# Canonical tower-root extraction

Second physical checkpoint for `ABGF-GR-003`: strip the maximal power of a coded base
from an event parent and prove that the positive remainder is nondivisible.

No primality assumption occurs here.  Mathlib's `padicValNat b n` is used as
the maximal exponent of the *whole positional base* `b`, so the same
decomposition applies to composite bases such as `4`, `6`, and `9`.
-/

open scoped ENNReal lp

namespace GreenFrame.Concrete

/-- Maximal exponent of the coded base dividing the parent of a Green event. -/
def eventParentDepth (e : GreenEvent) : ℕ :=
  positionalDepth (baseNat e.1) (e.2 : ℕ)

/-- Natural root left after removing the maximal coded-base power from the parent. -/
def eventTowerRootNat (e : GreenEvent) : ℕ :=
  (e.2 : ℕ) / (baseNat e.1) ^ eventParentDepth e

/-- Parent depth is definitionally Mathlib's whole-base `padicValNat`. -/
@[simp]
theorem eventParentDepth_eq_padicValNat (e : GreenEvent) :
    eventParentDepth e = padicValNat (baseNat e.1) (e.2 : ℕ) :=
  rfl

/-- The maximal coded-base power divides the event parent. -/
theorem eventParentPower_dvd (e : GreenEvent) :
    (baseNat e.1) ^ eventParentDepth e ∣ (e.2 : ℕ) := by
  exact positionalDepth_pow_dvd (baseNat e.1) (e.2 : ℕ)

/-- Removing the maximal coded-base power gives an exact factorization. -/
theorem eventParent_factorization (e : GreenEvent) :
    (baseNat e.1) ^ eventParentDepth e * eventTowerRootNat e =
      (e.2 : ℕ) := by
  exact Nat.mul_div_cancel' (eventParentPower_dvd e)

/-- The extracted natural tower root is positive. -/
theorem eventTowerRootNat_pos (e : GreenEvent) :
    0 < eventTowerRootNat e := by
  apply Nat.div_pos
  · exact Nat.le_of_dvd e.2.property (eventParentPower_dvd e)
  · exact pow_pos (baseNat_pos e.1) _

/-- The paper's quotient root is Mathlib's canonical maximal-power remainder. -/
theorem eventTowerRootNat_eq_divMaxPow (e : GreenEvent) :
    eventTowerRootNat e =
      Nat.divMaxPow (e.2 : ℕ) (baseNat e.1) := by
  apply Nat.mul_left_cancel (pow_pos (baseNat_pos e.1) (eventParentDepth e))
  calc
    (baseNat e.1) ^ eventParentDepth e * eventTowerRootNat e =
        (e.2 : ℕ) := eventParent_factorization e
    _ = (baseNat e.1) ^ eventParentDepth e *
          Nat.divMaxPow (e.2 : ℕ) (baseNat e.1) := by
      symm
      simpa [eventParentDepth, positionalDepth] using
        (Nat.pow_padicValNat_mul_divMaxPow (baseNat e.1) (e.2 : ℕ))

/-- Positive-natural packaging of the extracted tower root. -/
def eventTowerRootPNat (e : GreenEvent) : PNat :=
  ⟨eventTowerRootNat e, eventTowerRootNat_pos e⟩

/-- The full coded base does not divide the extracted positive tower root. -/
theorem base_not_dvd_eventTowerRoot (e : GreenEvent) :
    ¬ basePNat e.1 ∣ eventTowerRootPNat e := by
  intro hdvd
  have hdvdNat : baseNat e.1 ∣ eventTowerRootNat e := by
    simpa only [basePNat_coe, eventTowerRootPNat] using
      PNat.dvd_iff.mp hdvd
  rw [eventTowerRootNat_eq_divMaxPow] at hdvdNat
  exact Nat.not_dvd_divMaxPow
    (by have := baseNat_ge_two e.1; omega)
    (Nat.ne_of_gt e.2.property) hdvdNat

/--
The maximal-power decomposition is unique for every coded base, including a
composite base.  In particular we do not decompose a composite base into
prime valuations; `k` counts powers of the base itself.
 -/
theorem eventParent_decomposition_unique
    (e : GreenEvent) {k root : ℕ}
    (hfactor : (baseNat e.1) ^ k * root = (e.2 : ℕ))
    (hroot : ¬ baseNat e.1 ∣ root) :
    k = eventParentDepth e ∧ root = eventTowerRootNat e := by
  have hpair := Nat.maxPowDvdDiv_of_pow_mul_eq
    (Nat.ne_of_gt e.2.property) hfactor hroot
  have hk : eventParentDepth e = k := by
    simpa [eventParentDepth, positionalDepth] using
      congrArg Prod.fst hpair
  have hroot' : Nat.divMaxPow (e.2 : ℕ) (baseNat e.1) = root := by
    simpa using congrArg Prod.snd hpair
  exact ⟨hk.symm,
    hroot'.symm.trans (eventTowerRootNat_eq_divMaxPow e).symm⟩

/-- Canonical nondivisible tower root attached to a global Green event. -/
def eventTowerRoot (e : GreenEvent) : TowerRoot e.1 where
  value := eventTowerRootPNat e
  not_dvd := base_not_dvd_eventTowerRoot e

end GreenFrame.Concrete
