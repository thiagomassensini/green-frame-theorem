import GreenFrame.Concrete.Analysis.InfinitePartition

/-!
# Depth-one activity and finite charge framework

First checkpoint for `ABGF-AR-003`: the exact finite sums, endpoint map, and
the deduction from a termwise injective charge certificate.
-/

open scoped BigOperators

namespace GreenFrame.Concrete

/-- Bases whose positional depth at `n` is exactly one. -/
def depthOneBases (n : ℕ) : Finset ℕ :=
  (Finset.Icc 2 n).filter fun b => positionalDepth b n = 1

/-- Bases whose positional depth at `n` is at least two. -/
def bulkBases (n : ℕ) : Finset ℕ :=
  (Finset.Icc 2 n).filter fun b => 2 ≤ positionalDepth b n

/-- Membership criterion for the finite depth-one base set. -/
@[simp]
theorem mem_depthOneBases {b n : ℕ} :
    b ∈ depthOneBases n ↔ 2 ≤ b ∧ b ≤ n ∧ positionalDepth b n = 1 := by
  simp [depthOneBases, and_assoc]

/-- Membership criterion for the finite bulk base set. -/
@[simp]
theorem mem_bulkBases {b n : ℕ} :
    b ∈ bulkBases n ↔ 2 ≤ b ∧ b ≤ n ∧ 2 ≤ positionalDepth b n := by
  simp [bulkBases, and_assoc]

/-- Total log-depth activity carried by the depth-one bases at `n`. -/
noncomputable def depthOneActivity (n : ℕ) : ℝ :=
  ∑ b ∈ depthOneBases n, allBaseActivity b n

/-- Total log-depth activity carried by bases of depth at least two at `n`. -/
noncomputable def bulkActivity (n : ℕ) : ℝ :=
  ∑ b ∈ bulkBases n, allBaseActivity b n

/-- Depth-one activity is nonnegative. -/
theorem depthOneActivity_nonneg (n : ℕ) :
    0 ≤ depthOneActivity n := by
  apply Finset.sum_nonneg
  intro b hb
  exact allBaseActivity_nonneg (mem_depthOneBases.mp hb).1

/-- Bulk activity is nonnegative. -/
theorem bulkActivity_nonneg (n : ℕ) :
    0 ≤ bulkActivity n := by
  apply Finset.sum_nonneg
  intro b hb
  exact allBaseActivity_nonneg (mem_bulkBases.mp hb).1

/-- Canonical endpoint to which the bulk base `b` is charged at `n`. -/
def endpointCharge (n b : ℕ) : ℕ :=
  if b * b = n then n else n / b

/-- On the square-root branch, the endpoint charge is `n` itself. -/
@[simp]
theorem endpointCharge_of_square {n b : ℕ} (h : b * b = n) :
    endpointCharge n b = n := by
  simp [endpointCharge, h]

/-- Off the square-root branch, the endpoint charge is the quotient `n / b`. -/
@[simp]
theorem endpointCharge_of_not_square {n b : ℕ} (h : b * b ≠ n) :
    endpointCharge n b = n / b := by
  simp [endpointCharge, h]

/-- A finite injective charge from bulk bases into depth-one bases at `n`. -/
structure DepthOneChargeCertificate (n : ℕ) where
  charge : ℕ → ℕ
  mapsToDepthOne : ∀ {b}, b ∈ bulkBases n → charge b ∈ depthOneBases n
  injectiveOn : Set.InjOn charge (bulkBases n : Set ℕ)
  activityBound : ∀ {b}, b ∈ bulkBases n →
    allBaseActivity b n ≤ 2 * allBaseActivity (charge b) n

/-- Any finite charge certificate yields the bulk-to-depth-one activity bound. -/
theorem bulkActivity_le_two_mul_depthOneActivity_of_certificate
    {n : ℕ} (h : DepthOneChargeCertificate n) :
    bulkActivity n ≤ 2 * depthOneActivity n := by
  classical
  have hterm :
      bulkActivity n ≤
        ∑ b ∈ bulkBases n, 2 * allBaseActivity (h.charge b) n := by
    exact Finset.sum_le_sum fun b hb => h.activityBound hb
  have himage : (bulkBases n).image h.charge ⊆ depthOneBases n := by
    intro c hc
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hc
    exact h.mapsToDepthOne hb
  have hinj : ∀ b₁ ∈ bulkBases n, ∀ b₂ ∈ bulkBases n,
      h.charge b₁ = h.charge b₂ → b₁ = b₂ := by
    intro b₁ hb₁ b₂ hb₂ heq
    exact h.injectiveOn hb₁ hb₂ heq
  have hcharged :
      (∑ b ∈ bulkBases n, allBaseActivity (h.charge b) n) ≤
        depthOneActivity n := by
    rw [depthOneActivity, ← Finset.sum_image hinj]
    exact Finset.sum_le_sum_of_subset_of_nonneg himage fun b hb _ =>
      allBaseActivity_nonneg (mem_depthOneBases.mp hb).1
  calc
    bulkActivity n ≤
        ∑ b ∈ bulkBases n, 2 * allBaseActivity (h.charge b) n := hterm
    _ = 2 * ∑ b ∈ bulkBases n, allBaseActivity (h.charge b) n := by
      simp [Finset.mul_sum]
    _ ≤ 2 * depthOneActivity n :=
      mul_le_mul_of_nonneg_left hcharged (by norm_num)

/-- Every non-seed coordinate admits the canonical endpoint charge certificate. -/
def CanonicalDepthOneChargeExists : Prop :=
  ∀ n : ℕ, 1 < n →
    ∃ h : DepthOneChargeCertificate n, h.charge = endpointCharge n

/-- A canonical endpoint charge certificate yields the activity bound. -/
theorem bulkActivity_le_two_mul_depthOneActivity_of_charge_exists
    (hcharge : CanonicalDepthOneChargeExists) {n : ℕ} (hn : 1 < n) :
    bulkActivity n ≤ 2 * depthOneActivity n := by
  obtain ⟨h, _⟩ := hcharge n hn
  exact bulkActivity_le_two_mul_depthOneActivity_of_certificate h

end GreenFrame.Concrete
