import GreenFrame.Concrete.Finite.L2CoordinateMask
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Strong limit of increasing `ℓ²` coordinate masks

Tannery's theorem turns eventual retention of every coordinate into norm
convergence of the contractive masks.  This is the analytic tail lemma needed
by `ABGF-FS-002`.
-/

open scoped ENNReal lp Topology
open Filter

namespace GreenFrame.Concrete

theorem l2CoordinateMask_energy_tendsto_zero
    {iota : Type*} (keep : ℕ → iota → Prop)
    [∀ N, DecidablePred (keep N)]
    (hkeep : ∀ i, ∀ᶠ N in atTop, keep N i)
    (x : ℓ²(iota, ℂ)) :
    Tendsto
      (fun N => ‖l2CoordinateMask (keep N) x - x‖ ^ 2)
      atTop (nhds 0) := by
  have hpoint : ∀ i,
      Tendsto
        (fun N => Complex.normSq
          (l2CoordinateMask (keep N) x i - x i))
        atTop (nhds 0) := by
    intro i; apply tendsto_const_nhds.congr'
    filter_upwards [hkeep i] with N hN
    simp [hN]
  have hbound : ∀ᶠ N in atTop, ∀ i,
      ‖Complex.normSq (l2CoordinateMask (keep N) x i - x i)‖ ≤
        Complex.normSq (x i) := by
    apply Filter.Eventually.of_forall
    intro N
    intro i
    by_cases hN : keep N i
    · simp [hN, Complex.normSq_nonneg]
    · simp [hN, Complex.normSq_neg, abs_of_nonneg (Complex.normSq_nonneg (x i))]
  have htsum := tendsto_tsum_of_dominated_convergence
    (residualL2_normSq_summable x) hpoint hbound
  simpa only [← residualL2_normSq_tsum_eq_norm_sq] using htsum

theorem l2CoordinateMask_tendsto
    {iota : Type*} (keep : ℕ → iota → Prop)
    [∀ N, DecidablePred (keep N)]
    (hkeep : ∀ i, ∀ᶠ N in atTop, keep N i)
    (x : ℓ²(iota, ℂ)) :
    Tendsto (fun N => l2CoordinateMask (keep N) x)
      atTop (nhds x) := by
  have hsquare := l2CoordinateMask_energy_tendsto_zero keep hkeep x
  rw [Metric.tendsto_atTop] at hsquare ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hsquare (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨N, ?_⟩
  intro n hn
  have hsq := hN n hn
  rw [Real.dist_eq] at hsq
  have hnonneg : 0 ≤ ‖l2CoordinateMask (keep n) x - x‖ ^ 2 := sq_nonneg _
  have hsq' : ‖l2CoordinateMask (keep n) x - x‖ ^ 2 < ε ^ 2 := by
    simpa [abs_of_nonneg hnonneg] using hsq
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (l2CoordinateMask (keep n) x - x)]

end GreenFrame.Concrete
