import GreenFrame.Concrete.Arithmetic.EndpointChargeInjection
import GreenFrame.Concrete.Arithmetic.EndpointChargeActivity

/-!
# Canonical endpoint charge certificate

Final checkpoint for `ABGF-AR-003`.  The geometric landing theorem, branchwise
injectivity, and logarithmic term bound are assembled into the concrete finite
charge certificate.  The public head theorem has no certificate hypothesis.
-/

namespace GreenFrame.Concrete

/-- The paper endpoint map supplies the complete finite charge certificate. -/
noncomputable def canonicalDepthOneChargeCertificate (n : ℕ) :
    DepthOneChargeCertificate n where
  charge := endpointCharge n
  mapsToDepthOne := endpointCharge_mem_depthOneBases
  injectiveOn := endpointCharge_injectiveOn_bulkBases n
  activityBound := allBaseActivity_le_two_chargedActivity

/-- The canonical charge construction exists at every non-seed coordinate. -/
theorem canonicalDepthOneChargeExists : CanonicalDepthOneChargeExists := by
  intro n _
  exact ⟨canonicalDepthOneChargeCertificate n, rfl⟩

/-- `ABGF-AR-003`, with the canonical endpoint charge constructed internally. -/
theorem canonical_bulkActivity_le_two_mul_depthOneActivity
    {n : ℕ} (hn : 1 < n) :
    bulkActivity n ≤ 2 * depthOneActivity n :=
  bulkActivity_le_two_mul_depthOneActivity_of_charge_exists
    canonicalDepthOneChargeExists hn

end GreenFrame.Concrete
