import QubitOracle.Paper.SourceFaithfulMinimax

/-!
# Capped quadratic losses for local asymptotic minimax bounds

The local minimax argument first uses bounded bowl-shaped losses and then
lets the cap increase.  This module verifies both properties for the capped
squared norm and proves the required monotone convergence of its lintegrals.
-/

namespace QubitOracle.Paper

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Squared norm capped at the finite or infinite level `C`. -/
def cappedSquaredNormLoss {A : Type*} [Norm A]
    (C : ℝ≥0∞) (x : A) : ℝ≥0∞ :=
  min (ENNReal.ofReal (‖x‖ ^ 2)) C

/-- Every capped squared norm is a bowl-shaped loss: its sublevel sets are
closed balls (below the cap) or the entire space (at or above the cap). -/
theorem cappedSquaredNormLoss_bowlShaped
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (C : ℝ≥0∞) : IsBowlShapedLoss (@cappedSquaredNormLoss A _ C) := by
  constructor
  · intro c
    by_cases hC : C ≤ c
    · have hset : {x : A | cappedSquaredNormLoss C x ≤ c} = Set.univ := by
        ext x
        simp [cappedSquaredNormLoss, hC]
      rw [hset]
      exact convex_univ
    · have hcTop : c ≠ ∞ := by
        intro hc
        subst c
        exact hC le_top
      have hc0 : 0 ≤ c.toReal := ENNReal.toReal_nonneg
      have hset : {x : A | cappedSquaredNormLoss C x ≤ c} =
          Metric.closedBall 0 (Real.sqrt c.toReal) := by
        ext x
        simp only [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right]
        rw [cappedSquaredNormLoss, min_le_iff]
        simp only [hC, or_false, ENNReal.ofReal_le_iff_le_toReal hcTop]
        constructor
        · intro hx
          apply (sq_le_sq₀ (norm_nonneg x) (Real.sqrt_nonneg _)).1
          rwa [Real.sq_sqrt hc0]
        · intro hx
          have hx' := (sq_le_sq₀ (norm_nonneg x) (Real.sqrt_nonneg _)).2 hx
          rwa [Real.sq_sqrt hc0] at hx'
      rw [hset]
      exact convex_closedBall 0 (Real.sqrt c.toReal)
  · intro x
    simp [cappedSquaredNormLoss]

theorem cappedSquaredNormLoss_measurable
    {A : Type*} [NormedAddCommGroup A] [MeasurableSpace A] [BorelSpace A]
    (C : ℝ≥0∞) : Measurable (@cappedSquaredNormLoss A _ C) := by
  unfold cappedSquaredNormLoss
  fun_prop

theorem cappedSquaredNormLoss_le
    {A : Type*} [Norm A] (C : ℝ≥0∞) (x : A) :
    cappedSquaredNormLoss C x ≤ C :=
  min_le_right _ _

/-- Pointwise removal of the cap along natural levels. -/
theorem cappedSquaredNormLoss_tendsto
    {A : Type*} [Norm A] (x : A) :
    Filter.Tendsto (fun n : ℕ => cappedSquaredNormLoss (n : ℝ≥0∞) x)
      Filter.atTop (nhds (ENNReal.ofReal (‖x‖ ^ 2))) := by
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt
    (ENNReal.ofReal_ne_top : ENNReal.ofReal (‖x‖ ^ 2) ≠ ∞)
  apply tendsto_const_nhds.congr'
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hcast : (N : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by exact_mod_cast hn
  simp only [cappedSquaredNormLoss]
  rw [min_eq_left (le_of_lt hN |>.trans hcast)]

/-- Monotone convergence removes the cap inside every lintegral. -/
theorem lintegral_cappedSquaredNormLoss_tendsto
    {A : Type*} [NormedAddCommGroup A] [MeasurableSpace A] [BorelSpace A]
    (mu : Measure A) :
    Filter.Tendsto
      (fun n : ℕ => ∫⁻ x, cappedSquaredNormLoss (n : ℝ≥0∞) x ∂mu)
      Filter.atTop
      (nhds (∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂mu)) := by
  apply lintegral_tendsto_of_tendsto_of_monotone
  · intro n
    exact (cappedSquaredNormLoss_measurable (n : ℝ≥0∞)).aemeasurable
  · filter_upwards [] with x
    intro i j hij
    exact min_le_min_left _ (by exact_mod_cast hij)
  · filter_upwards [] with x
    exact cappedSquaredNormLoss_tendsto x

end

end QubitOracle.Paper
