import GreenFrame.Concrete.Arithmetic.EndpointChargeLanding

/-!
# Canonical endpoint charge: logarithmic activity

Fourth checkpoint for `ABGF-AR-003`.  The maximal-power divisor gives
`k_b(n) log b ≤ log n`.  The charged endpoint is either `n` itself or lies
strictly beyond `sqrt n`, so `log n ≤ 2 log c`.
-/

namespace GreenFrame.Concrete

/-- A bulk activity term is at most the logarithm of the observed number. -/
theorem allBaseActivity_le_log_number
    {b n : ℕ} (hb : b ∈ bulkBases n) :
    allBaseActivity b n ≤ Real.log (n : ℝ) := by
  obtain ⟨hb2, hbn, _⟩ := mem_bulkBases.mp hb
  have hn : 0 < n := by omega
  have hpow : b ^ positionalDepth b n ∣ n :=
    positionalDepth_pow_dvd b n
  have hpowle : b ^ positionalDepth b n ≤ n :=
    Nat.le_of_dvd hn hpow
  have hbR : 0 < (b : ℝ) := by
    exact_mod_cast (show 0 < b by omega)
  have hpowR : 0 < (b : ℝ) ^ positionalDepth b n :=
    pow_pos hbR _
  have hleR : (b : ℝ) ^ positionalDepth b n ≤ (n : ℝ) := by
    exact_mod_cast hpowle
  calc
    allBaseActivity b n =
        Real.log ((b : ℝ) ^ positionalDepth b n) := by
      rw [Real.log_pow]
      rfl
    _ ≤ Real.log (n : ℝ) := Real.log_le_log hpowR hleR

/-- The charged depth-one endpoint carries at least half the logarithm. -/
theorem log_number_le_two_endpointActivity
    {b n : ℕ} (hb : b ∈ bulkBases n) :
    Real.log (n : ℝ) ≤
      2 * allBaseActivity (endpointCharge n b) n := by
  obtain ⟨hb2, hbn, _⟩ := mem_bulkBases.mp hb
  have hn : 0 < n := by omega
  have hendpoint := endpointCharge_mem_depthOneBases hb
  have hdepth := (mem_depthOneBases.mp hendpoint).2.2
  by_cases hsq : b * b = n
  · rw [endpointCharge_of_square hsq]
    rw [allBaseActivity_self (by omega)]
    have hlognonneg : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    linarith
  · let c := n / b
    have hbdiv : b ∣ n :=
      (positionalDepth_pos_iff_dvd hb2 hn).mp (by omega)
    have hmul : c * b = n := by
      dsimp [c]
      exact Nat.div_mul_cancel hbdiv
    have hsqlt : b * b < n :=
      lt_of_le_of_ne (bulk_base_sq_le hb) hsq
    have hbc : b < c := by
      nlinarith [hmul]
    have hnltcsq : n < c * c := by
      nlinarith [hmul]
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hltR : (n : ℝ) < (c : ℝ) ^ 2 := by
      norm_num [pow_two]
      exact_mod_cast hnltcsq
    have hloglt : Real.log (n : ℝ) < Real.log ((c : ℝ) ^ 2) :=
      Real.log_lt_log hnR hltR
    rw [endpointCharge_of_not_square hsq] at hdepth ⊢
    rw [allBaseActivity, hdepth, Nat.cast_one, one_mul]
    rw [Real.log_pow] at hloglt
    dsimp [c] at hloglt
    norm_num at hloglt ⊢
    exact hloglt.le

/-- The canonical endpoint satisfies the certificate's termwise bound. -/
theorem allBaseActivity_le_two_chargedActivity
    {b n : ℕ} (hb : b ∈ bulkBases n) :
    allBaseActivity b n ≤
      2 * allBaseActivity (endpointCharge n b) n :=
  (allBaseActivity_le_log_number hb).trans
    (log_number_le_two_endpointActivity hb)

end GreenFrame.Concrete
