import QubitOracle.Paper.ExplorationDeletionRate

noncomputable section

namespace QubitOracle.Paper

open scoped BigOperators
open Filter

/-- The deterministic cumulative exploration mass `E_n`. -/
def explorationCumulativeMass
    (epsilon : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, epsilon (k + 1)

/-- The three asymptotic assumptions displayed in `eq:SI_explore`. -/
structure ExplorationScheduleHypotheses
    (epsilon : ℕ → ℝ) : Prop where
  cumulative_tendsto_atTop :
    Tendsto (explorationCumulativeMass epsilon) atTop atTop
  cumulative_div_log_tendsto_atTop :
    Tendsto
      (fun n : ℕ =>
        explorationCumulativeMass epsilon n / Real.log n)
      atTop atTop
  cumulative_average_tendsto_zero :
    Tendsto (explorationScheduleAverage epsilon) atTop (nhds 0)

/-- The schedule average is exactly `E_n / n`. -/
theorem explorationScheduleAverage_eq
    (epsilon : ℕ → ℝ) (n : ℕ) :
    explorationScheduleAverage epsilon n =
      (n : ℝ)⁻¹ * explorationCumulativeMass epsilon n := by
  rfl

namespace Label

/-- `eq:SI_explore`: exact Lean encoding of the cumulative exploration mass
and the three schedule assumptions.  The theorem does not assert that an
arbitrary schedule satisfies these hypotheses. -/
theorem eq_SI_explore
    (epsilon : ℕ → ℝ)
    (h : ExplorationScheduleHypotheses epsilon) :
    (∀ n,
      explorationCumulativeMass epsilon n =
        ∑ k ∈ Finset.range n, epsilon (k + 1)) ∧
      Tendsto (explorationCumulativeMass epsilon) atTop atTop ∧
      Tendsto
        (fun n : ℕ =>
          explorationCumulativeMass epsilon n / Real.log n)
        atTop atTop ∧
      Tendsto
        (fun n : ℕ =>
          (n : ℝ)⁻¹ * explorationCumulativeMass epsilon n)
        atTop (nhds 0) := by
  refine ⟨fun n => rfl, h.cumulative_tendsto_atTop,
    h.cumulative_div_log_tendsto_atTop, ?_⟩
  have haverage : explorationScheduleAverage epsilon =
      fun n : ℕ =>
        (n : ℝ)⁻¹ * explorationCumulativeMass epsilon n := by
    funext n
    exact explorationScheduleAverage_eq epsilon n
  rw [← haverage]
  exact h.cumulative_average_tendsto_zero

end Label

end QubitOracle.Paper
