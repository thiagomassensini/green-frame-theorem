import GreenFrame.Concrete.Analysis.CanonicalParseval

/-!
# Normalized external/bulk split
-/

noncomputable section

open scoped InnerProductSpace

namespace GreenFrame.Concrete

variable {H E B : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]

/-- External component after canonical Parseval normalization. -/
def normalizedExternal (T : H →L[ℂ] HilbertSum E B) : H →L[ℂ] E :=
  (rawExternal T).comp (inverseSqrtFrame T)

/-- Bulk component after canonical Parseval normalization. -/
def normalizedBulk (T : H →L[ℂ] HilbertSum E B) : H →L[ℂ] B :=
  (rawBulk T).comp (inverseSqrtFrame T)

@[simp]
theorem normalizedExternal_apply (T : H →L[ℂ] HilbertSum E B) (x : H) :
    normalizedExternal T x = (canonicalAnalysis T x).fst :=
  rfl

@[simp]
theorem normalizedBulk_apply (T : H →L[ℂ] HilbertSum E B) (x : H) :
    normalizedBulk T x = (canonicalAnalysis T x).snd :=
  rfl

/-- Pythagorean Parseval identity for the normalized split. -/
theorem normalized_split_energy {T : H →L[ℂ] HilbertSum E B}
    (bounds : ComplexFrameBounds T) (x : H) :
    ‖normalizedExternal T x‖ ^ 2 + ‖normalizedBulk T x‖ ^ 2 = ‖x‖ ^ 2 := by
  calc
    ‖normalizedExternal T x‖ ^ 2 + ‖normalizedBulk T x‖ ^ 2
        = ‖canonicalAnalysis T x‖ ^ 2 := by
            symm
            simpa using WithLp.prod_norm_sq_eq_of_L2 (canonicalAnalysis T x)
    _ = ‖x‖ ^ 2 := by rw [canonicalParseval_norm bounds]

/-- The external lower constant after normalization. -/
def normalizedExternalLower {T : H →L[ℂ] HilbertSum E B}
    (bounds : SplitComplexFrameBounds T) : ℝ :=
  bounds.externalLower / bounds.upper

theorem normalizedExternalLower_pos {T : H →L[ℂ] HilbertSum E B}
    (bounds : SplitComplexFrameBounds T) :
    0 < normalizedExternalLower bounds :=
  div_pos bounds.externalLower_pos bounds.upper_pos

/-- The raw external ledger and the global upper frame bound give the exact
normalized external lower bound `externalLower / upper`. -/
theorem normalizedExternal_lower_norm_sq
    {T : H →L[ℂ] HilbertSum E B}
    (bounds : SplitComplexFrameBounds T) (x : H) :
    normalizedExternalLower bounds * ‖x‖ ^ 2 ≤
      ‖normalizedExternal T x‖ ^ 2 := by
  let Q : H →L[ℂ] H := inverseSqrtFrame T
  have hVnorm : ‖canonicalAnalysis T x‖ = ‖x‖ :=
    canonicalParseval_norm bounds.toComplexFrameBounds x
  have hx : ‖x‖ ^ 2 ≤ bounds.upper * ‖Q x‖ ^ 2 := by
    calc
      ‖x‖ ^ 2 = ‖canonicalAnalysis T x‖ ^ 2 := by rw [hVnorm]
      _ = ‖T (Q x)‖ ^ 2 := rfl
      _ ≤ bounds.upper * ‖Q x‖ ^ 2 := bounds.upper_norm_sq (Q x)
  calc
    normalizedExternalLower bounds * ‖x‖ ^ 2
        ≤ normalizedExternalLower bounds *
            (bounds.upper * ‖Q x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hx (normalizedExternalLower_pos bounds).le
    _ = bounds.externalLower * ‖Q x‖ ^ 2 := by
          dsimp [normalizedExternalLower]
          rw [← mul_assoc, div_mul_cancel₀ _ bounds.upper_pos.ne']
    _ ≤ ‖rawExternal T (Q x)‖ ^ 2 :=
          bounds.external_lower_norm_sq (Q x)
    _ = ‖normalizedExternal T x‖ ^ 2 := rfl

end GreenFrame.Concrete
