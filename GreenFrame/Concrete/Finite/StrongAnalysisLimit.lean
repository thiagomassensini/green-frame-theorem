import GreenFrame.Concrete.Finite.AnalysisSection

/-!
# Strong limit estimate for embedded analysis sections

This checkpoint proves the two-term `Q_N T P_N → T` estimate for explicit
families of state and coefficient maps.  It has no cutoff-data structure and
no `ConcreteStrongCutoffsExist` proposition.  The concrete coordinate masks
are substituted in `ConcreteStrongAnalysisLimit` after their `ℓ²` tail limits
have been proved.
-/

open scoped ENNReal lp Topology
open Filter

namespace GreenFrame.Concrete

/-- Strong convergence of `P_N` and `Q_N`, plus contractivity of `Q_N`, gives
strong convergence of the common-space sections `Q_N T P_N`. -/
theorem embeddedAnalysisSection_tendsto
    (omega : AdmissibleInfinitePartition)
    (P : ℕ → State →L[ℂ] State)
    (Q : ℕ → ConcreteAnalysisSpace →L[ℂ] ConcreteAnalysisSpace)
    (hP : ∀ f : State, Tendsto (fun N => P N f) atTop (nhds f))
    (hQ : ∀ y : ConcreteAnalysisSpace,
      Tendsto (fun N => Q N y) atTop (nhds y))
    (hQ_contracts : ∀ N y, ‖Q N y‖ ≤ ‖y‖)
    (f : State) :
    Tendsto (fun N => embeddedAnalysisSection omega (P N) (Q N) f)
      atTop (nhds (concreteAnalysisOperator omega f)) := by
  have hTP :
      Tendsto
        (fun N => concreteAnalysisOperator omega (P N f))
        atTop (nhds (concreteAnalysisOperator omega f)) :=
    (concreteAnalysisOperator omega).continuous.continuousAt.tendsto.comp
      (hP f)
  have hQy := hQ (concreteAnalysisOperator omega f)
  rw [Metric.tendsto_atTop] at hTP hQy ⊢
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := hTP (ε / 2) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hQy (ε / 2) (by linarith)
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN
  have hfirst := hN₁ N (le_trans (le_max_left _ _) hN)
  have hsecond := hN₂ N (le_trans (le_max_right _ _) hN)
  let yN := concreteAnalysisOperator omega (P N f)
  let y := concreteAnalysisOperator omega f
  calc
    dist (embeddedAnalysisSection omega (P N) (Q N) f) y =
        dist (Q N yN) y := by
      rfl
    _ ≤ dist (Q N yN) (Q N y) + dist (Q N y) y :=
      dist_triangle _ _ _
    _ = ‖Q N (yN - y)‖ + dist (Q N y) y := by
      rw [dist_eq_norm]
      simp only [map_sub]
    _ ≤ ‖yN - y‖ + dist (Q N y) y := by
      exact add_le_add (hQ_contracts N _) le_rfl
    _ = dist yN y + dist (Q N y) y := by
      simpa only [dist_eq_norm]
    _ < ε / 2 + ε / 2 := add_lt_add hfirst hsecond
    _ = ε := by ring

end GreenFrame.Concrete
