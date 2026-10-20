import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.OneQubitPureCoordinateCore
/-! Supporting definitions and proved lemmas used by the manuscript. -/

namespace QubitOracle.Paper

open Finset
open scoped BigOperators

noncomputable section

/-! ## Elementary finite-three-dimensional dot algebra -/

theorem blochDot_directional_comm
    (x z : Fin 3 → Real) :
    blochDot x z = blochDot z x := by
  simp [blochDot, Fin.sum_univ_succ]
  ring

theorem blochDot_directional_self
    (x : Fin 3 → Real) :
    blochDot x x = blochNormSq x := by
  simp [blochDot, blochNormSq, Fin.sum_univ_succ]
  ring

theorem blochDot_sub_scaled
    (x z v : Fin 3 → Real) (a b : Real) :
    blochDot (fun j => x j - a * v j)
        (fun j => z j - b * v j) =
      blochDot x z - b * blochDot x v -
        a * blochDot v z + a * b * blochNormSq v := by
  simp [blochDot, blochNormSq, Fin.sum_univ_succ]
  ring

theorem blochDot_right_sub_scaled
    (v x : Fin 3 → Real) (a : Real) :
    blochDot v (fun j => x j - a * v j) =
      blochDot v x - a * blochNormSq v := by
  simp [blochDot, blochNormSq, Fin.sum_univ_succ]
  ring

/-! ## The concrete Householder map -/

def qubitHouseholderVector
    (r : Fin 3 → Real) : Fin 3 → Real :=
  fun j => r j - directionalNorthPole j

theorem qubitHouseholderVector_normSq_nonnegative
    (r : Fin 3 → Real) :
    0 ≤ blochNormSq (qubitHouseholderVector r) := by
  unfold blochNormSq
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem qubitHouseholderVector_normSq_pos
    (r : Fin 3 → Real)
    (hDifferent : r ≠ directionalNorthPole) :
    0 < blochNormSq (qubitHouseholderVector r) := by
  have hNonnegative := qubitHouseholderVector_normSq_nonnegative r
  have hNonzero : blochNormSq (qubitHouseholderVector r) ≠ 0 := by
    intro hZero
    have hExpanded :
        r 0 ^ 2 + r 1 ^ 2 + (r 2 - 1) ^ 2 = 0 := by
      convert hZero using 1 <;>
        simp [blochNormSq, qubitHouseholderVector,
          directionalNorthPole, Fin.sum_univ_succ] <;> ring
    have h0 : r 0 = 0 := by
      nlinarith [sq_nonneg (r 0), sq_nonneg (r 1),
        sq_nonneg (r 2 - 1)]
    have h1 : r 1 = 0 := by
      nlinarith [sq_nonneg (r 0), sq_nonneg (r 1),
        sq_nonneg (r 2 - 1)]
    have h2 : r 2 = 1 := by
      nlinarith [sq_nonneg (r 0), sq_nonneg (r 1),
        sq_nonneg (r 2 - 1)]
    apply hDifferent
    funext j
    fin_cases j <;>
      simp [directionalNorthPole, h0, h1, h2]
  exact lt_of_le_of_ne hNonnegative (Ne.symm hNonzero)

theorem qubitHouseholderVector_normSq_ne
    (r : Fin 3 → Real)
    (hDifferent : r ≠ directionalNorthPole) :
    blochNormSq (qubitHouseholderVector r) ≠ 0 :=
  (qubitHouseholderVector_normSq_pos r hDifferent).ne'

/-- Identity at the north pole, and otherwise the reflection across the
hyperplane orthogonal to `r - e₃`. -/
def qubitHouseholderToNorth
    (r x : Fin 3 → Real) : Fin 3 → Real :=
  if hNorth : r = directionalNorthPole then x
  else
    fun j =>
      x j -
        2 * (blochDot (qubitHouseholderVector r) x /
          blochNormSq (qubitHouseholderVector r)) *
          qubitHouseholderVector r j

@[simp]
theorem qubitHouseholderToNorth_at_northPole
    (x : Fin 3 → Real) :
    qubitHouseholderToNorth directionalNorthPole x = x := by
  simp [qubitHouseholderToNorth]

/-- The Householder map preserves every Bloch inner product. -/
theorem qubitHouseholderToNorth_dot_preserved
    (r x z : Fin 3 → Real) :
    blochDot (qubitHouseholderToNorth r x)
        (qubitHouseholderToNorth r z) = blochDot x z := by
  classical
  by_cases hNorth : r = directionalNorthPole
  · simp [qubitHouseholderToNorth, hNorth]
  · have hDenominator :=
      qubitHouseholderVector_normSq_ne r hNorth
    simp only [qubitHouseholderToNorth, dif_neg hNorth]
    rw [blochDot_sub_scaled]
    rw [blochDot_directional_comm x (qubitHouseholderVector r)]
    field_simp [hDenominator]
    ring

/-- Consequently the squared Bloch norm is preserved. -/
theorem qubitHouseholderToNorth_normSq_preserved
    (r x : Fin 3 → Real) :
    blochNormSq (qubitHouseholderToNorth r x) = blochNormSq x := by
  rw [← blochDot_directional_self,
    qubitHouseholderToNorth_dot_preserved,
    blochDot_directional_self]

/-- Dotting the reflection normal with a reflected vector changes sign. -/
theorem qubitHouseholderVector_dot_image
    (r x : Fin 3 → Real) :
    blochDot (qubitHouseholderVector r)
        (qubitHouseholderToNorth r x) =
      -blochDot (qubitHouseholderVector r) x := by
  classical
  by_cases hNorth : r = directionalNorthPole
  · subst r
    simp [qubitHouseholderToNorth, qubitHouseholderVector,
      directionalNorthPole, blochDot, Fin.sum_univ_succ]
  · have hDenominator :=
      qubitHouseholderVector_normSq_ne r hNorth
    simp only [qubitHouseholderToNorth, dif_neg hNorth]
    rw [blochDot_right_sub_scaled]
    field_simp [hDenominator]
    ring

/-- The concrete reflection is its own inverse. -/
theorem qubitHouseholderToNorth_involutive
    (r x : Fin 3 → Real) :
    qubitHouseholderToNorth r (qubitHouseholderToNorth r x) = x := by
  classical
  by_cases hNorth : r = directionalNorthPole
  · simp [qubitHouseholderToNorth, hNorth]
  · funext j
    have hDot := qubitHouseholderVector_dot_image r x
    simp only [qubitHouseholderToNorth, dif_neg hNorth] at hDot ⊢
    rw [hDot]
    ring

/-! ## Sending a unit truth to the north pole -/

theorem qubitHouseholderVector_dot_truth
    (r : Fin 3 → Real)
    (hUnit : blochNormSq r = 1) :
    blochDot (qubitHouseholderVector r) r = 1 - r 2 := by
  have hExpanded := hUnit
  simp [blochNormSq, Fin.sum_univ_succ] at hExpanded
  simp [blochDot, qubitHouseholderVector,
    directionalNorthPole, Fin.sum_univ_succ]
  nlinarith

theorem qubitHouseholderVector_normSq_eq
    (r : Fin 3 → Real)
    (hUnit : blochNormSq r = 1) :
    blochNormSq (qubitHouseholderVector r) = 2 * (1 - r 2) := by
  have hExpanded := hUnit
  simp [blochNormSq, Fin.sum_univ_succ] at hExpanded
  simp [blochNormSq, qubitHouseholderVector,
    directionalNorthPole, Fin.sum_univ_succ]
  nlinarith

theorem qubitHouseholder_truth_coefficient_eq_one
    (r : Fin 3 → Real)
    (hUnit : blochNormSq r = 1)
    (hDifferent : r ≠ directionalNorthPole) :
    2 * (blochDot (qubitHouseholderVector r) r /
      blochNormSq (qubitHouseholderVector r)) = 1 := by
  have hDenominator := qubitHouseholderVector_normSq_ne r hDifferent
  rw [qubitHouseholderVector_dot_truth r hUnit,
    qubitHouseholderVector_normSq_eq r hUnit]
  have hGap : 1 - r 2 ≠ 0 := by
    intro hZero
    apply hDenominator
    rw [qubitHouseholderVector_normSq_eq r hUnit, hZero]
    norm_num
  field_simp [hGap]

/-- Every unit Bloch truth is sent exactly to the north pole. -/
theorem qubitHouseholderToNorth_maps_truth
    (r : Fin 3 → Real)
    (hUnit : blochNormSq r = 1) :
    qubitHouseholderToNorth r r = directionalNorthPole := by
  classical
  by_cases hNorth : r = directionalNorthPole
  · simpa [hNorth, qubitHouseholderToNorth]
  · have hCoefficient :=
      qubitHouseholder_truth_coefficient_eq_one r hUnit hNorth
    funext j
    simp only [qubitHouseholderToNorth, dif_neg hNorth]
    rw [hCoefficient]
    simp [qubitHouseholderVector]

/-- By involutivity, the same map sends the north pole back to the truth. -/
theorem qubitHouseholderToNorth_maps_northPole
    (r : Fin 3 → Real)
    (hUnit : blochNormSq r = 1) :
    qubitHouseholderToNorth r directionalNorthPole = r := by
  calc
    qubitHouseholderToNorth r directionalNorthPole =
        qubitHouseholderToNorth r (qubitHouseholderToNorth r r) := by
      rw [qubitHouseholderToNorth_maps_truth r hUnit]
    _ = r := qubitHouseholderToNorth_involutive r r

/-! ## Transport of tangent measurement axes and Born probabilities -/

theorem qubitHouseholder_transportedAxis_unit
    (r axis : Fin 3 → Real)
    (hAxis : blochNormSq axis = 1) :
    blochNormSq (qubitHouseholderToNorth r axis) = 1 := by
  rw [qubitHouseholderToNorth_normSq_preserved, hAxis]

theorem qubitHouseholder_transportedAxis_tangent
    (r axis : Fin 3 → Real)
    (hTruthUnit : blochNormSq r = 1)
    (hTangent : blochDot axis r = 0) :
    blochDot (qubitHouseholderToNorth r axis)
        directionalNorthPole = 0 := by
  calc
    blochDot (qubitHouseholderToNorth r axis)
        directionalNorthPole =
      blochDot (qubitHouseholderToNorth r axis)
        (qubitHouseholderToNorth r r) := by
      rw [qubitHouseholderToNorth_maps_truth r hTruthUnit]
    _ = blochDot axis r :=
      qubitHouseholderToNorth_dot_preserved r axis r
    _ = 0 := hTangent




/-! ## The reflected arbitrary-truth chart -/





/-! ## Transported log likelihood and regularity certificate -/







namespace Label


end Label

end

end QubitOracle.Paper
