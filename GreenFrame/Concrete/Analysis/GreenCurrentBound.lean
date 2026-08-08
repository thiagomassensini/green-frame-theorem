import GreenFrame.Concrete.Analysis.GreenCurrentCameraBound

/-!
# Global current-node Green bound

This checkpoint restricts the summable number--camera majorant to genuine
divisibility events, pulls it back along `eventDivisibilityEquiv`, and proves
the global `3/2` estimate.
-/

open scoped ENNReal lp

namespace GreenFrame.Concrete

/-- Current contribution on the original event space. -/
noncomputable def currentGreenMajorant
    (omega : AdmissibleInfinitePartition) (f : State) (e : GreenEvent) : ℝ :=
  currentCameraMajorant omega f (eventNumber e) e.1

theorem currentGreenMajorant_nonneg
    (omega : AdmissibleInfinitePartition) (f : State) (e : GreenEvent) :
    0 ≤ currentGreenMajorant omega f e :=
  currentCameraMajorant_nonneg omega f _ _

/-- The current event majorant is summable. -/
theorem currentGreenMajorant_summable
    (omega : AdmissibleInfinitePartition) (f : State) :
    Summable (currentGreenMajorant omega f) := by
  have hraw :=
    (currentCameraMajorant_prod_summable omega f).comp_injective
      (Subtype.val_injective : Function.Injective
        (fun q : DivisibilityPair => q.1))
  have hsub : Summable (fun q : DivisibilityPair =>
      currentCameraMajorant omega f q.1.1 q.1.2) := by
    apply hraw.congr
    intro q
    rfl
  have hpull := (eventDivisibilityEquiv.summable_iff).mpr hsub
  apply hpull.congr
  intro e
  rfl

/-- The global current contribution has the sharp elementary bound `3/2`. -/
theorem currentGreenMajorant_tsum_le
    (omega : AdmissibleInfinitePartition) (f : State) :
    (∑' e : GreenEvent, currentGreenMajorant omega f e) ≤
      (3 : ℝ) / 2 * ‖f‖ ^ 2 := by
  rw [show (∑' e : GreenEvent, currentGreenMajorant omega f e) =
      ∑' p : PNat × ℕ, currentCameraMajorant omega f p.1 p.2 by
    apply tsum_greenEvent_reindex
    intro n r h
    apply omega.support_dvd
    intro hw
    apply h
    simp [currentCameraMajorant, hw]]
  rw [(currentCameraMajorant_prod_summable omega f).tsum_prod]
  calc
    (∑' n : PNat, ∑' r : ℕ, currentCameraMajorant omega f n r) ≤
        ∑' n : PNat, ((3 : ℝ) / 2 * stateEnergy f n) := by
      exact ((summable_prod_of_nonneg
        (fun p => currentCameraMajorant_nonneg omega f p.1 p.2)).mp
          (currentCameraMajorant_prod_summable omega f)).2.tsum_le_tsum
        (currentCameraMajorant_tsum_le omega f)
        ((stateEnergy_summable f).mul_left _)
    _ = (3 : ℝ) / 2 * ‖f‖ ^ 2 := by
      rw [tsum_mul_left, stateEnergy_tsum_eq_norm_sq]

end GreenFrame.Concrete
