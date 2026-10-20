import Mathlib

/-! Literal finite-outcome identities used in Section 2.4.
Scores have the same positive-support convention as the manuscript.
The sampling probabilities here are held fixed under differentiation.
-/
namespace QubitOracle.Paper.InformationDefinitions
open scoped BigOperators
noncomputable section
variable {O : Type*} [Fintype O]

def directionalScore (p dp : O → ℝ) (y : O) : ℝ :=
  if 0 < p y then dp y / p y else 0

def directionalFisher (p dp dq : O → ℝ) : ℝ :=
  ∑ y, if 0 < p y then dp y * dq y / p y else 0

/-- On positive support the score is the derivative of log probability,
with the action and its selection probability held fixed. -/
theorem directionalScore_eq_log_derivative (p : O → ℝ → ℝ) (dp : O → ℝ)
    (y : O) (hp : 0 < p y 0) (hd : HasDerivAt (p y) (dp y) 0) :
    directionalScore (fun z => p z 0) dp y =
      deriv (fun s => Real.log (p y s)) 0 := by
  rw [directionalScore,if_pos hp]
  exact (hd.log (ne_of_gt hp)).deriv.symm

theorem fisher_eq_expected_scores (p dp dq : O → ℝ) :
    directionalFisher p dp dq =
      ∑ y, p y * directionalScore p dp y * directionalScore p dq y := by
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : 0 < p y
  · simp only [directionalScore, h, ↓reduceIte]
    field_simp
  · simp [directionalScore, h]

theorem fisher_eq_positive_support (p dp dq : O → ℝ) [DecidablePred fun y => 0 < p y] :
    directionalFisher p dp dq =
      ∑ y ∈ Finset.univ.filter (fun y => 0 < p y), dp y * dq y / p y := by
  simp only [directionalFisher, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> rfl

theorem fisher_eq_total_division (p dp dq : O → ℝ) (hp : ∀ y, 0 ≤ p y) :
    directionalFisher p dp dq = ∑ y, dp y * dq y / p y := by
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : 0 < p y
  · simp [h]
  · have hz : p y = 0 := le_antisymm (le_of_not_gt h) (hp y)
    simp [h, hz]

theorem fisher_nonnegative (p dp : O → ℝ) : 0 ≤ directionalFisher p dp dp := by
  apply Finset.sum_nonneg
  intro y _
  by_cases h : 0 < p y
  · simp only [h, ↓reduceIte]
    exact div_nonneg (mul_self_nonneg _) h.le
  · simp [h]

theorem fisher_zero_iff (p dp : O → ℝ) :
    directionalFisher p dp dp = 0 ↔ ∀ y, 0 < p y → dp y = 0 := by
  constructor
  · intro hf y hy
    have hn (z : O) : 0 ≤ if 0 < p z then dp z * dp z / p z else 0 := by
      split_ifs with h
      · exact div_nonneg (mul_self_nonneg _) h.le
      · exact le_rfl
    have hbound := Finset.single_le_sum (fun z _ => hn z) (Finset.mem_univ y)
    change (if 0 < p y then dp y * dp y / p y else 0) ≤ directionalFisher p dp dp at hbound
    rw [if_pos hy, hf] at hbound
    have he : dp y * dp y / p y = 0 := le_antisymm hbound (div_nonneg (mul_self_nonneg _) hy.le)
    exact mul_self_eq_zero.mp ((div_eq_zero_iff).mp he |>.resolve_right (ne_of_gt hy))
  · intro h
    apply Finset.sum_eq_zero
    intro y _
    by_cases hy : 0 < p y
    · simp [hy, h y hy]
    · simp [hy]

/-- Positive information is precisely first-order identifiability on
positive-probability outcomes. This says nothing about global injectivity. -/
theorem fisher_positive_iff (p dp : O → ℝ) :
    0 < directionalFisher p dp dp ↔ ∃ y, 0 < p y ∧ dp y ≠ 0 := by
  rw [lt_iff_le_and_ne, and_iff_right (fisher_nonnegative p dp), ne_comm]
  simp only [ne_eq, fisher_zero_iff]
  push Not
  rfl

/-- Recording a finite randomized setting preserves its weighted
information. The weights are part of the design, not an observed score. -/
theorem randomized_information {A : Type*} [Fintype A]
    (weight : A → ℝ) (p dp dq : A → O → ℝ)
    (hw : ∀ a, 0 ≤ weight a) (hp : ∀ a y, 0 ≤ p a y) :
    directionalFisher (fun ay : A × O => weight ay.1 * p ay.1 ay.2)
      (fun ay => weight ay.1 * dp ay.1 ay.2)
      (fun ay => weight ay.1 * dq ay.1 ay.2) =
      ∑ a, weight a * directionalFisher (p a) (dp a) (dq a) := by
  rw [fisher_eq_total_division _ _ _ (fun ay => mul_nonneg (hw _) (hp _ _))]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [fisher_eq_total_division _ _ _ (hp a), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  by_cases ha : weight a = 0
  · simp [ha]
  · by_cases hy : p a y = 0
    · simp [hy]
    · field_simp

end
end QubitOracle.Paper.InformationDefinitions
