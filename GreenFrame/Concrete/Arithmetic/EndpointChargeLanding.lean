import GreenFrame.Concrete.Arithmetic.DepthOneChargeFramework

/-!
# Canonical endpoint charge: landing at depth one

Second checkpoint for `ABGF-AR-003`.  A bulk base `b` satisfies `b^2 ∣ n`.
If `b^2 = n`, it is charged to the depth-one base `n`; otherwise it is
charged to `n / b`, which lies strictly beyond `sqrt n` and therefore has
depth exactly one.  Nothing in the argument requires `b` to be prime.
-/

namespace GreenFrame.Concrete

/-- Every bulk base contributes a square divisor of the observed number. -/
theorem bulk_base_sq_dvd {b n : ℕ} (hb : b ∈ bulkBases n) :
    b ^ 2 ∣ n := by
  obtain ⟨hb2, hbn, hdepth⟩ := mem_bulkBases.mp hb
  have hn : 0 < n := by omega
  rw [Nat.pow_dvd_iff_le_padicValNat (by omega) (Nat.ne_of_gt hn)]
  simpa only [positionalDepth] using hdepth

/-- Hence the square of a bulk base lies below the observed number. -/
theorem bulk_base_sq_le {b n : ℕ} (hb : b ∈ bulkBases n) :
    b * b ≤ n := by
  have hn : 0 < n := by
    obtain ⟨_, hbn, _⟩ := mem_bulkBases.mp hb
    omega
  simpa only [pow_two] using Nat.le_of_dvd hn (bulk_base_sq_dvd hb)

/-- The canonical endpoint charge of every bulk base is a depth-one base. -/
theorem endpointCharge_mem_depthOneBases
    {b n : ℕ} (hb : b ∈ bulkBases n) :
    endpointCharge n b ∈ depthOneBases n := by
  obtain ⟨hb2, hbn, _⟩ := mem_bulkBases.mp hb
  have hn : 0 < n := by omega
  have hbdiv : b ∣ n :=
    (positionalDepth_pos_iff_dvd hb2 hn).mp (by omega)
  by_cases hsq : b * b = n
  · rw [endpointCharge_of_square hsq]
    exact mem_depthOneBases.mpr
      ⟨by omega, le_rfl, positionalDepth_self (by omega)⟩
  · let c := n / b
    have hmul : c * b = n := by
      dsimp [c]
      exact Nat.div_mul_cancel hbdiv
    have hsqlt : b * b < n :=
      lt_of_le_of_ne (bulk_base_sq_le hb) hsq
    have hbc : b < c := by
      nlinarith [hmul]
    have hc2 : 2 ≤ c := by omega
    have hcn : c ≤ n := Nat.div_le_self n b
    have hcdiv : c ∣ n := ⟨b, hmul.symm⟩
    have hnltcsq : n < c * c := by
      nlinarith [hmul]
    have hnotcsq : ¬ c ^ 2 ∣ n := by
      intro hdiv
      have hle : c * c ≤ n := by
        simpa only [pow_two] using Nat.le_of_dvd hn hdiv
      omega
    have hcdepth_pos : 0 < positionalDepth c n :=
      (positionalDepth_pos_iff_dvd hc2 hn).mpr hcdiv
    have hcdepth_lt : positionalDepth c n < 2 := by
      by_contra hbad
      have htwo : 2 ≤ positionalDepth c n := by omega
      apply hnotcsq
      rw [Nat.pow_dvd_iff_le_padicValNat (by omega)
        (Nat.ne_of_gt hn)]
      simpa only [positionalDepth] using htwo
    have hcdepth : positionalDepth c n = 1 := by omega
    rw [endpointCharge_of_not_square hsq]
    exact mem_depthOneBases.mpr ⟨hc2, hcn, hcdepth⟩

end GreenFrame.Concrete
