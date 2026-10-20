import QubitOracle.Paper.ExplorationScheduleLabels

namespace QubitOracle.Paper

noncomputable section

/-- The clipped power exploration schedule displayed in the main paper. -/
def powerExplorationSchedule (c : ℝ) (n₀ : ℕ) (α : ℝ) (i : ℕ) : ℝ :=
  min 1 (c * Real.rpow (i + n₀ : ℝ) (-α))

namespace Label

/-- Main-text equation `eq:power_exploration`, including the stated parameter
domain `c > 0`, `n₀ ≥ 1`, and `0 < α < 1`. -/
theorem eq_power_exploration
    (c : ℝ) (n₀ : ℕ) (α : ℝ)
    (_hc : 0 < c) (_hn₀ : 1 ≤ n₀) (_hα₀ : 0 < α) (_hα₁ : α < 1) :
    ∀ i, powerExplorationSchedule c n₀ α i =
      min 1 (c * Real.rpow (i + n₀ : ℝ) (-α)) :=
  fun _ => rfl

end Label

/-- Every term of the admissible clipped power schedule is strictly positive. -/
theorem powerExplorationSchedule_pos
    (c : ℝ) (n₀ : ℕ) (α : ℝ)
    (hc : 0 < c) (hn₀ : 1 ≤ n₀) (i : ℕ) :
    0 < powerExplorationSchedule c n₀ α i := by
  have hn₀Real : (0 : ℝ) < (n₀ : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn₀)
  have hbase : (0 : ℝ) < (i : ℝ) + (n₀ : ℝ) :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg i) hn₀Real
  apply lt_min (by norm_num)
  exact mul_pos hc (Real.rpow_pos_of_pos hbase _)

/-- Clipping enforces the protocol requirement `epsilon_i ≤ 1`. -/
theorem powerExplorationSchedule_le_one
    (c : ℝ) (n₀ : ℕ) (α : ℝ) (i : ℕ) :
    powerExplorationSchedule c n₀ α i ≤ 1 :=
  min_le_left _ _

/-- In particular, every clipped power probability is nonnegative. -/
theorem powerExplorationSchedule_nonneg
    (c : ℝ) (n₀ : ℕ) (α : ℝ)
    (hc : 0 < c) (hn₀ : 1 ≤ n₀) (i : ℕ) :
    0 ≤ powerExplorationSchedule c n₀ α i :=
  (powerExplorationSchedule_pos c n₀ α hc hn₀ i).le

end

end QubitOracle.Paper
