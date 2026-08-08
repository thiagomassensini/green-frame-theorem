import GreenFrame.Concrete.Analysis.HorizontalResolutionEnergy

/-!
# Horizontal resolution by the remaining elementary cameras

This checkpoint proves the final seed-plus-off-base identity.  Its public head
uses an explicit `n ≠ 1` guard, so the iterated sum is literally the paper's
sum over `n > 1`.  It concerns the elementary atlas, not the vertical Green
stencil.
-/

open scoped ENNReal lp

namespace GreenFrame.Concrete

/-- Event-space form of horizontal resolution. -/
theorem horizontal_offBase_resolution_event
    (omega : AdmissibleInfinitePartition) (r : ℕ)
    (f : horizontalState r) :
    ‖(f : State)‖ ^ 2 =
      Complex.normSq ((f : State) (1 : PNat)) +
        ∑' e : ElementaryAtlasEvent,
          offBaseAtlasEnergyTerm omega r (f : State) e := by
  calc
    ‖(f : State)‖ ^ 2 =
        ‖elementaryAtlas omega (f : State)‖ ^ 2 :=
      (elementaryAtlas_norm_sq_eq omega (f : State)).symm
    _ = Complex.normSq ((f : State) (1 : PNat)) +
        ‖elementaryAtlasCamera omega (f : State)‖ ^ 2 :=
      elementaryAtlas_norm_sq_eq_components omega (f : State)
    _ = Complex.normSq ((f : State) (1 : PNat)) +
        ∑' e : ElementaryAtlasEvent,
          elementaryAtlasEnergyTerm omega (f : State) e := by
      congr 1
      calc
        ‖elementaryAtlasCamera omega (f : State)‖ ^ 2 =
            ∑' n : PNat,
              elementaryAtlasCameraDensity omega (f : State) n :=
          elementaryAtlasCamera_norm_sq_eq omega (f : State)
        _ = ∑' e : ElementaryAtlasEvent,
            elementaryAtlasEnergyTerm omega (f : State) e := by
          simpa only [elementaryAtlasCameraDensity,
            elementaryAtlasEnergyTerm] using
            (elementaryAtlasEnergyTerm_summable
              omega (f : State)).tsum_prod.symm
    _ = Complex.normSq ((f : State) (1 : PNat)) +
        ∑' e : ElementaryAtlasEvent,
          offBaseAtlasEnergyTerm omega r (f : State) e := by
      congr 1
      apply tsum_congr
      intro e
      exact elementaryAtlasEnergyTerm_eq_offBase_on_horizontal omega r f e

/-- Product form before making the already-zero seed row explicit. -/
theorem horizontal_offBase_resolution_allPNat
    (omega : AdmissibleInfinitePartition) (r : ℕ)
    (f : horizontalState r) :
    ‖(f : State)‖ ^ 2 =
      Complex.normSq ((f : State) (1 : PNat)) +
        ∑' n : PNat, ∑' s : ℕ,
          if s = r then 0
          else omega.weight s n * Complex.normSq ((f : State) n) := by
  calc
    ‖(f : State)‖ ^ 2 =
        Complex.normSq ((f : State) (1 : PNat)) +
          ∑' e : ElementaryAtlasEvent,
            offBaseAtlasEnergyTerm omega r (f : State) e :=
      horizontal_offBase_resolution_event omega r f
    _ = Complex.normSq ((f : State) (1 : PNat)) +
        ∑' n : PNat, ∑' s : ℕ,
          if s = r then 0
          else omega.weight s n * Complex.normSq ((f : State) n) := by
      rw [(offBaseAtlasEnergyTerm_summable
        omega r (f : State)).tsum_prod]
      rfl

/--
`ABGF-AN-002`: seed energy plus the elementary cameras other than `r`
resolves `H_(basePNat r)^hor`.  Since `PNat` starts at one, the guard
`n = 1` is the literal encoding of the paper's restriction `n > 1`.
-/
theorem horizontal_offBase_resolution
    (omega : AdmissibleInfinitePartition) (r : ℕ)
    (f : horizontalState r) :
    ‖(f : State)‖ ^ 2 =
      Complex.normSq ((f : State) (1 : PNat)) +
        ∑' n : PNat, if n = 1 then 0 else
          ∑' s : ℕ, if s = r then 0
            else omega.weight s n * Complex.normSq ((f : State) n) := by
  calc
    ‖(f : State)‖ ^ 2 =
        Complex.normSq ((f : State) (1 : PNat)) +
          ∑' n : PNat, ∑' s : ℕ,
            if s = r then 0
            else omega.weight s n * Complex.normSq ((f : State) n) :=
      horizontal_offBase_resolution_allPNat omega r f
    _ = Complex.normSq ((f : State) (1 : PNat)) +
        ∑' n : PNat, if n = 1 then 0 else
          ∑' s : ℕ, if s = r then 0
            else omega.weight s n * Complex.normSq ((f : State) n) := by
      congr 1
      apply tsum_congr
      intro n
      by_cases hn : n = 1
      · subst n
        simp
      · simp [hn]

/-- Canonical log-depth specialization of the literal horizontal resolution. -/
theorem canonicalCarry_horizontal_offBase_resolution
    (r : ℕ) (f : horizontalState r) :
    ‖(f : State)‖ ^ 2 =
      Complex.normSq ((f : State) (1 : PNat)) +
        ∑' n : PNat, if n = 1 then 0 else
          ∑' s : ℕ, if s = r then 0
            else canonicalCarryInfinitePartition.weight s n *
              Complex.normSq ((f : State) n) :=
  horizontal_offBase_resolution canonicalCarryInfinitePartition r f

end GreenFrame.Concrete
