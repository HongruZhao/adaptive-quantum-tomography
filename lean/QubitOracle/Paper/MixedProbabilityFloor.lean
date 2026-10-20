import Mathlib
/-!
# Mixed-qubit binary probability floor

This is the scalar core of the mixed-state regularity estimate.  In the
paper one substitutes `z = u^T theta` and obtains `|z| <= ||theta||` from
Cauchy--Schwarz for a unit measurement axis.
-/

namespace QubitOracle
namespace Paper

/-- The two outcomes of a projective qubit measurement. -/
inductive BinaryOutcome
  | plus
  | minus
  deriving DecidableEq

instance : Fintype BinaryOutcome where
  elems := {.plus, .minus}
  complete := by
    intro y
    cases y <;> simp

/-- Numerical sign attached to a binary outcome. -/
def BinaryOutcome.sign : BinaryOutcome → ℝ
  | .plus => 1
  | .minus => -1

/-- Born probability written in terms of the scalar Bloch projection. -/
noncomputable def binaryBornProbability (z : ℝ) (y : BinaryOutcome) : ℝ :=
  (1 + y.sign * z) / 2

/-- Both binary outcomes stay above half of the radial gap. -/
theorem binaryBornProbability_lower_bound (z s : ℝ)
    (hz : |z| ≤ s) (y : BinaryOutcome) :
    (1 - s) / 2 ≤ binaryBornProbability z y := by
  rcases y with _ | _
  · simp only [binaryBornProbability, BinaryOutcome.sign, one_mul]
    have hneg : -s ≤ z := by
      exact (abs_le.mp hz).1
    linarith
  · simp only [binaryBornProbability, BinaryOutcome.sign, neg_mul]
    have hpos : z ≤ s := by
      exact (abs_le.mp hz).2
    linarith

/-- An interior radial gap makes every binary Born probability positive. -/
theorem binaryBornProbability_pos (z s : ℝ)
    (hz : |z| ≤ s) (hs : s < 1) (y : BinaryOutcome) :
    0 < binaryBornProbability z y := by
  have hgap : 0 < (1 - s) / 2 := by linarith
  exact lt_of_lt_of_le hgap (binaryBornProbability_lower_bound z s hz y)

/-- The likelihood denominator has the corresponding unscaled lower bound. -/
theorem signed_denominator_lower_bound (z s : ℝ)
    (hz : |z| ≤ s) (y : BinaryOutcome) :
    1 - s ≤ 1 + y.sign * z := by
  have h := binaryBornProbability_lower_bound z s hz y
  unfold binaryBornProbability at h
  linarith

end Paper
end QubitOracle
