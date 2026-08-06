import GreenFrame.Analysis.PythagoreanSplit

/-!
# Elementary Green-stencil estimates
-/

namespace GreenFrame

/-- The unweighted second-difference stencil. -/
def greenStencil (x parent grandparent : ℝ) : ℝ :=
  x - 2 * parent + grandparent

/-- Three-term Cauchy inequality in squared form. -/
theorem sum_three_sq_le (x y z : ℝ) :
    (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]

/-- A Green stencil is controlled by twelve times the local three-node energy. -/
theorem greenStencil_sq_le (x parent grandparent : ℝ) :
    greenStencil x parent grandparent ^ 2
      ≤ 12 * (x ^ 2 + parent ^ 2 + grandparent ^ 2) := by
  have h := sum_three_sq_le x (-2 * parent) grandparent
  dsimp [greenStencil]
  nlinarith [sq_nonneg x, sq_nonneg parent, sq_nonneg grandparent]

/-- The square of every Green coordinate is nonnegative. -/
theorem greenStencil_sq_nonneg (x parent grandparent : ℝ) :
    0 ≤ greenStencil x parent grandparent ^ 2 := by
  exact sq_nonneg _

/-- Summing the local estimate gives the finite Green Bessel estimate. -/
theorem greenAnalysis_norm_sq_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x parent grandparent : ι → ℝ) :
    (∑ i in s, greenStencil (x i) (parent i) (grandparent i) ^ 2)
      ≤ 12 * ∑ i in s, (x i ^ 2 + parent i ^ 2 + grandparent i ^ 2) := by
  calc
    (∑ i in s, greenStencil (x i) (parent i) (grandparent i) ^ 2)
        ≤ ∑ i in s, 12 * (x i ^ 2 + parent i ^ 2 + grandparent i ^ 2) := by
          exact Finset.sum_le_sum fun i _ => greenStencil_sq_le (x i) (parent i) (grandparent i)
    _ = 12 * ∑ i in s, (x i ^ 2 + parent i ^ 2 + grandparent i ^ 2) := by
          rw [Finset.mul_sum]

end GreenFrame
