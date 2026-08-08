import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Complex split frame bounds

Draft interface between the concrete Green/residual operators and the
operator-theoretic Parseval/Poisson layer.

The important point is that the external lower ledger is retained separately
from the lower bound for the full analysis.  The latter alone cannot imply
that the normalized external component has closed range.
-/

noncomputable section

open scoped InnerProductSpace

namespace GreenFrame.Concrete

/-- Hilbert direct sum, rather than the sup-normed ordinary product. -/
abbrev HilbertSum (E B : Type*) := WithLp 2 (E × B)

variable {H K E B : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]

/-- Quantitative two-sided frame bounds proved by the concrete kernel layer. -/
structure ComplexFrameBounds (T : H →L[ℂ] K) where
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  upper_pos : 0 < upper
  lower_norm_sq : ∀ x, lower * ‖x‖ ^ 2 ≤ ‖T x‖ ^ 2
  upper_norm_sq : ∀ x, ‖T x‖ ^ 2 ≤ upper * ‖x‖ ^ 2

/-- Raw external component of a split analysis operator. -/
def rawExternal (T : H →L[ℂ] HilbertSum E B) : H →L[ℂ] E :=
  (WithLp.fstL 2 ℂ E B).comp T

/-- Raw bulk component of a split analysis operator. -/
def rawBulk (T : H →L[ℂ] HilbertSum E B) : H →L[ℂ] B :=
  (WithLp.sndL 2 ℂ E B).comp T

@[simp]
theorem rawExternal_apply (T : H →L[ℂ] HilbertSum E B) (x : H) :
    rawExternal T x = (T x).fst :=
  rfl

@[simp]
theorem rawBulk_apply (T : H →L[ℂ] HilbertSum E B) (x : H) :
    rawBulk T x = (T x).snd :=
  rfl

/-- Full frame bounds together with the independent lower ledger for the
external sector (seed, residual, and depth-one Green in the canonical split). -/
structure SplitComplexFrameBounds (T : H →L[ℂ] HilbertSum E B)
    extends ComplexFrameBounds T where
  externalLower : ℝ
  externalLower_pos : 0 < externalLower
  external_lower_norm_sq :
    ∀ x, externalLower * ‖x‖ ^ 2 ≤ ‖rawExternal T x‖ ^ 2

/-- Build the split certificate directly from the three component estimates
delivered by the concrete layer.  The external estimate supplies the full
lower frame bound; the two component upper estimates add by the Hilbert-sum
Pythagorean identity.  Thus this constructor needs no independently assumed
full-analysis lower inequality. -/
def SplitComplexFrameBounds.ofComponentBounds
    (T : H →L[ℂ] HilbertSum E B)
    {externalLower externalUpper bulkUpper : ℝ}
    (externalLower_pos : 0 < externalLower)
    (externalUpper_pos : 0 < externalUpper)
    (bulkUpper_nonneg : 0 ≤ bulkUpper)
    (external_lower_norm_sq :
      ∀ x, externalLower * ‖x‖ ^ 2 ≤ ‖rawExternal T x‖ ^ 2)
    (external_upper_norm_sq :
      ∀ x, ‖rawExternal T x‖ ^ 2 ≤ externalUpper * ‖x‖ ^ 2)
    (bulk_upper_norm_sq :
      ∀ x, ‖rawBulk T x‖ ^ 2 ≤ bulkUpper * ‖x‖ ^ 2) :
    SplitComplexFrameBounds T where
  lower := externalLower
  upper := externalUpper + bulkUpper
  lower_pos := externalLower_pos
  upper_pos := add_pos_of_pos_of_nonneg externalUpper_pos bulkUpper_nonneg
  lower_norm_sq x := by
    calc
      externalLower * ‖x‖ ^ 2 ≤ ‖rawExternal T x‖ ^ 2 :=
        external_lower_norm_sq x
      _ ≤ ‖rawExternal T x‖ ^ 2 + ‖rawBulk T x‖ ^ 2 :=
        le_add_of_nonneg_right (sq_nonneg ‖rawBulk T x‖)
      _ = ‖T x‖ ^ 2 := by
        rw [rawExternal_apply, rawBulk_apply]
        exact (WithLp.prod_norm_sq_eq_of_L2 (T x)).symm
  upper_norm_sq x := by
    calc
      ‖T x‖ ^ 2 =
          ‖rawExternal T x‖ ^ 2 + ‖rawBulk T x‖ ^ 2 := by
        rw [rawExternal_apply, rawBulk_apply]
        exact WithLp.prod_norm_sq_eq_of_L2 (T x)
      _ ≤ externalUpper * ‖x‖ ^ 2 + bulkUpper * ‖x‖ ^ 2 :=
        add_le_add (external_upper_norm_sq x) (bulk_upper_norm_sq x)
      _ = (externalUpper + bulkUpper) * ‖x‖ ^ 2 := by ring
  externalLower := externalLower
  externalLower_pos := externalLower_pos
  external_lower_norm_sq := external_lower_norm_sq

end GreenFrame.Concrete
