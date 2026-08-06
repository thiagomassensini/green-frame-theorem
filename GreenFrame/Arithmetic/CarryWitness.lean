import GreenFrame.Arithmetic.NormalizedWeights

/-!
# Canonical `(2,4)` carry witness

At the integer `4`, the active all-base log-depth activities of bases `2` and
`4` are equal. This finite chart is the exact arithmetic witness used to show
that the Green bulk is nontrivial.
-/

namespace GreenFrame

/-- The two active activities at `n = 4`, indexed by bases `2` and `4`. -/
def carryFourActivity : Fin 2 → ℝ := fun _ => 1

/-- The normalized two-camera weight at `n = 4`. -/
def carryFourWeight (i : Fin 2) : ℝ :=
  normalizedWeight Finset.univ carryFourActivity i

/-- The two equal activities have total mass two. -/
theorem carryActivity_four_normalizer :
    activityNormalizer (Finset.univ : Finset (Fin 2)) carryFourActivity = 2 := by
  norm_num [activityNormalizer, carryFourActivity, Fin.sum_univ_two]

/-- The base-2 camera receives exactly half of the mass at `n = 4`. -/
theorem carryWeight_two_four : carryFourWeight (0 : Fin 2) = 1 / 2 := by
  norm_num [carryFourWeight, normalizedWeight, carryActivity_four_normalizer,
    carryFourActivity]

/-- The base-4 camera receives the complementary half. -/
theorem carryWeight_four_four : carryFourWeight (1 : Fin 2) = 1 / 2 := by
  norm_num [carryFourWeight, normalizedWeight, carryActivity_four_normalizer,
    carryFourActivity]

end GreenFrame
