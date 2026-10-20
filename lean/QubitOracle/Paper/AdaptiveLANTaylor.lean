import QubitOracle.Paper.SequentialHessian
import QubitOracle.Paper.AdaptiveConditions

/-!
# Deterministic algebra for adaptive LAN

This module proves the finite Taylor-sum identity, the total cubic remainder
bound, and bounded-score Lindeberg arithmetic.  It intentionally does not
assert stochastic convergence or a martingale central limit theorem.
-/

namespace QubitOracle.Paper

open scoped BigOperators

noncomputable section

/-- Conditional tail second moment used in the martingale Lindeberg
condition. -/
def finiteTailScoreMoment
    {Y E : Type*} [Fintype Y] [Norm E]
    (mass : Y -> ℝ) (score : Y -> E) (epsilon : ℝ) (n : ℕ) : ℝ :=
  ∑ y, mass y * ‖score y‖ ^ 2 *
    lindebergIndicator (epsilon * Real.sqrt (n : ℝ)) ‖score y‖

/-- If every possible score is below the Lindeberg threshold, the conditional
tail moment is exactly zero. -/
theorem finiteTailScoreMoment_eq_zero_of_bounded
    {Y E : Type*} [Fintype Y] [Norm E]
    (mass : Y -> ℝ) (score : Y -> E) (epsilon : ℝ) (n : ℕ)
    (hbounded : ∀ y, ‖score y‖ ≤ epsilon * Real.sqrt (n : ℝ)) :
    finiteTailScoreMoment mass score epsilon n = 0 := by
  apply Finset.sum_eq_zero
  intro y _
  rw [show lindebergIndicator (epsilon * Real.sqrt (n : ℝ)) ‖score y‖ = 0 from
    lindebergIndicator_eq_zero_of_le (hbounded y)]
  ring

/-- Finite normalized Lindeberg sum over regular rounds. -/
def finiteMartingaleLindebergSum
    {ι : Type*} (rounds : Finset ι) (regularWeight tailMoment : ι -> ℝ)
    (n : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ t ∈ rounds, regularWeight t * tailMoment t

theorem finiteMartingaleLindebergSum_eq_zero
    {ι : Type*} (rounds : Finset ι) (regularWeight tailMoment : ι -> ℝ)
    (n : ℕ) (htail : ∀ t ∈ rounds, tailMoment t = 0) :
    finiteMartingaleLindebergSum rounds regularWeight tailMoment n = 0 := by
  unfold finiteMartingaleLindebergSum
  have hsum : (∑ t ∈ rounds, regularWeight t * tailMoment t) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    rw [htail t ht, mul_zero]
  rw [hsum, mul_zero]

/-- Sum a shotwise scalar Taylor identity. -/
theorem finite_LAN_Taylor_sum
    {ι : Type*} (rounds : Finset ι)
    (logRatio linear quadratic remainder : ι -> ℝ)
    (hstep : ∀ i ∈ rounds,
      logRatio i = linear i - (1 / 2 : ℝ) * quadratic i + remainder i) :
    (∑ i ∈ rounds, logRatio i) =
      (∑ i ∈ rounds, linear i) -
        (1 / 2 : ℝ) * (∑ i ∈ rounds, quadratic i) +
          ∑ i ∈ rounds, remainder i := by
  calc
    (∑ i ∈ rounds, logRatio i) =
        ∑ i ∈ rounds,
          (linear i - (1 / 2 : ℝ) * quadratic i + remainder i) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hstep i hi
    _ = (∑ i ∈ rounds, linear i) -
          (1 / 2 : ℝ) * (∑ i ∈ rounds, quadratic i) +
            ∑ i ∈ rounds, remainder i := by
              simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
              rw [Finset.mul_sum]

/-- A per-round `B / n` absolute bound over at most `n` rounds gives a total
absolute remainder at most `B`. -/
theorem finite_sum_remainder_abs_le
    {ι : Type*} (rounds : Finset ι) (remainder : ι -> ℝ)
    (n : ℕ) (B : ℝ) (hn : 0 < n) (hB : 0 ≤ B)
    (hcard : rounds.card ≤ n)
    (hrem : ∀ i ∈ rounds, |remainder i| ≤ B / (n : ℝ)) :
    |∑ i ∈ rounds, remainder i| ≤ B := by
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcardReal : (rounds.card : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hcard
  calc
    |∑ i ∈ rounds, remainder i| ≤
        ∑ i ∈ rounds, |remainder i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ rounds, B / (n : ℝ) :=
      Finset.sum_le_sum fun i hi => hrem i hi
    _ = (rounds.card : ℝ) * (B / (n : ℝ)) := by simp
    _ ≤ (n : ℝ) * (B / (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hcardReal (div_nonneg hB hnReal.le)
    _ = B := by field_simp [hnReal.ne']

/-- Cubic Taylor remainders of size
`(C * radius^3 / sqrt n) / n` sum to the paper's
`C * radius^3 / sqrt n` bound. -/
theorem finite_LAN_cubic_remainder_bound
    {ι : Type*} (rounds : Finset ι) (remainder : ι -> ℝ)
    (n : ℕ) (C radius : ℝ) (hn : 0 < n)
    (hC : 0 ≤ C) (hradius : 0 ≤ radius)
    (hcard : rounds.card ≤ n)
    (hrem : ∀ i ∈ rounds,
      |remainder i| ≤
        (C * radius ^ 3 / Real.sqrt (n : ℝ)) / (n : ℝ)) :
    |∑ i ∈ rounds, remainder i| ≤
      C * radius ^ 3 / Real.sqrt (n : ℝ) := by
  apply finite_sum_remainder_abs_le rounds remainder n
    (C * radius ^ 3 / Real.sqrt (n : ℝ)) hn
  · positivity
  · exact hcard
  · exact hrem

end

end QubitOracle.Paper
