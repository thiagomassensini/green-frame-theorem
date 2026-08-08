import GreenFrame.Concrete.Analysis.GreenStencilComplex

/-!
# Reindexing lemmas for the infinite Green camera

This module isolates the two arithmetic changes of variables used in the
global Bessel estimate:

* `(r,m) \mapsto (b_r m,r)` identifies Green events with divisibility pairs;
* `k \mapsto b_r k` identifies positive integers with the multiples of one
  fixed coded base.

Keeping these equivalences separate from the analytic estimate makes the
Tonelli steps in `GreenBessel` small and auditable.
-/

namespace GreenFrame.Concrete

/-- Number--camera pairs on which the coded camera is arithmetically active. -/
abbrev DivisibilityPair :=
  {p : PNat × ℕ // basePNat p.2 ∣ p.1}

/-- A Green event, viewed as its current number together with its camera. -/
def eventToDivisibilityPair (e : GreenEvent) : DivisibilityPair :=
  ⟨(eventNumber e, e.1), by
    rcases e with ⟨r, m⟩
    exact dvd_mul_right (basePNat r) m⟩

/-- Dividing the current number of an event by its base recovers its parent. -/
@[simp]
theorem divExact_eventNumber (e : GreenEvent) :
    PNat.divExact (eventNumber e) (basePNat e.1) = e.2 := by
  rcases e with ⟨r, m⟩
  apply mul_left_cancel (a := basePNat r)
  exact PNat.mul_div_exact (dvd_mul_right (basePNat r) m)

/-- Green events are exactly positive divisibility pairs. -/
def eventDivisibilityEquiv : GreenEvent ≃ DivisibilityPair where
  toFun := eventToDivisibilityPair
  invFun q := (q.1.2, PNat.divExact q.1.1 (basePNat q.1.2))
  left_inv e := by
    change (e.1, PNat.divExact (eventNumber e) (basePNat e.1)) = e
    apply Prod.ext
    · rfl
    · exact divExact_eventNumber e
  right_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · exact PNat.mul_div_exact q.property
    · rfl

@[simp]
theorem eventDivisibilityEquiv_apply_val (e : GreenEvent) :
    (eventDivisibilityEquiv e).1 = (eventNumber e, e.1) :=
  rfl

/--
Reindex a camera family supported on genuine divisibility events.  The right
hand side is written on the full product; the support hypothesis supplies the
zero extension off `DivisibilityPair`.
-/
theorem tsum_greenEvent_reindex
    (a : PNat → ℕ → ℝ)
    (ha : ∀ n r, a n r ≠ 0 → basePNat r ∣ n) :
    (∑' e : GreenEvent, a (eventNumber e) e.1) =
      ∑' p : PNat × ℕ, a p.1 p.2 := by
  calc
    (∑' e : GreenEvent, a (eventNumber e) e.1) =
        ∑' q : DivisibilityPair, a q.1.1 q.1.2 := by
      simpa only [eventDivisibilityEquiv_apply_val] using
        (eventDivisibilityEquiv.tsum_eq
          (fun q : DivisibilityPair => a q.1.1 q.1.2))
    _ = ∑' p : PNat × ℕ, a p.1 p.2 := by
      exact tsum_subtype_eq_of_support_subset
        (f := fun p : PNat × ℕ => a p.1 p.2)
        (s := {p : PNat × ℕ | basePNat p.2 ∣ p.1})
        (by
          intro p hp
          exact ha p.1 p.2 hp)

/-- Positive multiples of one coded base. -/
abbrev BaseMultiple (r : ℕ) :=
  {m : PNat // basePNat r ∣ m}

/-- Multiplication by a coded base, with codomain restricted to its multiples. -/
def multiplyIntoBaseMultiple (r : ℕ) (m : PNat) : BaseMultiple r :=
  ⟨basePNat r * m, dvd_mul_right (basePNat r) m⟩

/-- Exact division cancels multiplication by a coded base. -/
@[simp]
theorem divExact_base_mul (r : ℕ) (m : PNat) :
    PNat.divExact (basePNat r * m) (basePNat r) = m := by
  apply mul_left_cancel (a := basePNat r)
  exact PNat.mul_div_exact (dvd_mul_right (basePNat r) m)

/-- Multiplication by a fixed coded base is a bijection onto its multiples. -/
def baseMultipleEquiv (r : ℕ) : PNat ≃ BaseMultiple r where
  toFun := multiplyIntoBaseMultiple r
  invFun m := PNat.divExact m.1 (basePNat r)
  left_inv := divExact_base_mul r
  right_inv m := by
    apply Subtype.ext
    exact PNat.mul_div_exact m.property

@[simp]
theorem baseMultipleEquiv_apply_val (r : ℕ) (m : PNat) :
    (baseMultipleEquiv r m).1 = basePNat r * m :=
  rfl

/-- A function pulled back by exact division and extended by zero off the multiples. -/
noncomputable def divisiblePullback (r : ℕ) (a : PNat → ℝ) (m : PNat) : ℝ := by
  classical
  exact if basePNat r ∣ m then
    a (PNat.divExact m (basePNat r))
  else
    0

/-- Pullback by exact division preserves summability. -/
theorem divisiblePullback_summable (r : ℕ) {a : PNat → ℝ}
    (ha : Summable a) :
    Summable (divisiblePullback r a) := by
  classical
  let g : PNat → PNat := fun k => basePNat r * k
  have hg : Function.Injective g := by
    intro x y hxy
    exact mul_left_cancel hxy
  have hzero : ∀ m ∉ Set.range g, divisiblePullback r a m = 0 := by
    intro m hm
    by_cases hdiv : basePNat r ∣ m
    · exfalso
      apply hm
      rcases hdiv with ⟨k, hk⟩
      exact ⟨k, hk.symm⟩
    · simp [divisiblePullback, hdiv]
  apply (Function.Injective.summable_iff hg hzero).mp
  apply ha.congr
  intro k
  simp [Function.comp_apply, g, divisiblePullback]

/-- Pullback by exact division preserves the value of the infinite sum. -/
theorem tsum_divisiblePullback (r : ℕ) (a : PNat → ℝ) :
    (∑' m : PNat, divisiblePullback r a m) = ∑' k : PNat, a k := by
  classical
  let g : PNat → PNat := fun k => basePNat r * k
  have hg : Function.Injective g := by
    intro x y hxy
    exact mul_left_cancel hxy
  have hzero : ∀ m ∉ Set.range g, divisiblePullback r a m = 0 := by
    intro m hm
    by_cases hdiv : basePNat r ∣ m
    · exfalso
      apply hm
      rcases hdiv with ⟨k, hk⟩
      exact ⟨k, hk.symm⟩
    · simp [divisiblePullback, hdiv]
  by_cases ha : Summable a
  · have hcomp : HasSum ((divisiblePullback r a) ∘ g) (∑' k, a k) := by
      apply ha.hasSum.congr_fun
      intro k
      simp [Function.comp_apply, g, divisiblePullback]
    exact ((hg.hasSum_iff hzero).mp hcomp).tsum_eq
  · have hpull : ¬Summable (divisiblePullback r a) := by
      intro h
      apply ha
      have hcomp := (hg.summable_iff hzero).mpr h
      apply hcomp.congr
      intro k
      simp [Function.comp_apply, g, divisiblePullback]
    rw [tsum_eq_zero_of_not_summable hpull,
      tsum_eq_zero_of_not_summable ha]

end GreenFrame.Concrete
