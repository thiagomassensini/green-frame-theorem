import GreenFrame.Concrete.Arithmetic.EndpointChargeLanding

/-!
# Canonical endpoint charge: injectivity

Third checkpoint for `ABGF-AR-003`.  The quotient branch is injective because
every bulk base divides `n`.  The exceptional square-root branch has value
`n`, while every quotient branch has value strictly below `n`, so the two
branches cannot collide.
-/

namespace GreenFrame.Concrete

/-- The endpoint charge is injective on the finite set of bulk bases. -/
theorem endpointCharge_injectiveOn_bulkBases (n : ℕ) :
    Set.InjOn (endpointCharge n) (bulkBases n : Set ℕ) := by
  intro b₁ hb₁ b₂ hb₂ heq
  have hn : 0 < n := by
    obtain ⟨_, hbn, _⟩ := mem_bulkBases.mp hb₁
    omega
  have hb₁div : b₁ ∣ n := by
    obtain ⟨hb2, _, _⟩ := mem_bulkBases.mp hb₁
    exact (positionalDepth_pos_iff_dvd hb2 hn).mp (by omega)
  have hb₂div : b₂ ∣ n := by
    obtain ⟨hb2, _, _⟩ := mem_bulkBases.mp hb₂
    exact (positionalDepth_pos_iff_dvd hb2 hn).mp (by omega)
  by_cases hs₁ : b₁ * b₁ = n
  · by_cases hs₂ : b₂ * b₂ = n
    · have hsq : b₁ * b₁ = b₂ * b₂ := hs₁.trans hs₂.symm
      nlinarith
    · have hlt : n / b₂ < n :=
        Nat.div_lt_self hn (by
          obtain ⟨hb2, _, _⟩ := mem_bulkBases.mp hb₂
          omega)
      rw [endpointCharge_of_square hs₁,
        endpointCharge_of_not_square hs₂] at heq
      omega
  · by_cases hs₂ : b₂ * b₂ = n
    · have hlt : n / b₁ < n :=
        Nat.div_lt_self hn (by
          obtain ⟨hb2, _, _⟩ := mem_bulkBases.mp hb₁
          omega)
      rw [endpointCharge_of_not_square hs₁,
        endpointCharge_of_square hs₂] at heq
      omega
    · rw [endpointCharge_of_not_square hs₁,
        endpointCharge_of_not_square hs₂] at heq
      have hm₁ : (n / b₁) * b₁ = n := Nat.div_mul_cancel hb₁div
      have hm₂ : (n / b₂) * b₂ = n := Nat.div_mul_cancel hb₂div
      have hcpos : 0 < n / b₁ := by
        have hmem := endpointCharge_mem_depthOneBases hb₁
        rw [endpointCharge_of_not_square hs₁] at hmem
        exact lt_of_lt_of_le (by omega) (mem_depthOneBases.mp hmem).1
      apply Nat.eq_of_mul_eq_mul_left hcpos
      calc
        (n / b₁) * b₁ = n := hm₁
        _ = (n / b₂) * b₂ := hm₂.symm
        _ = (n / b₁) * b₂ := by rw [heq]

end GreenFrame.Concrete
