import QubitOracle.Paper.PowerExplorationSchedule
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Partial-sum bounds for the clipped power exploration schedule

This module supplies the analytic core of supplement equation
`eq:SI_power_orders`.  Clipping changes the un-clipped power law only by
fixed positive multiplicative constants.  The shifted negative-power sum is
then bounded below by its final term times the number of terms and above by
the exact integral of the corresponding antitone function.
-/

noncomputable section

namespace QubitOracle.Paper

open scoped BigOperators
open Set

/-- Shifted negative-power sum underlying the cumulative exploration mass. -/
def shiftedNegativeRpowSum (n₀ : ℕ) (α : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    Real.rpow ((n₀ : ℝ) + (k + 1 : ℕ)) (-α)

/-- The clipped term is bounded above by the un-clipped power term. -/
theorem powerExplorationSchedule_le_mul_rpow
    (c : ℝ) (n₀ : ℕ) (α : ℝ) (i : ℕ) :
    powerExplorationSchedule c n₀ α i ≤
      c * Real.rpow (i + n₀ : ℝ) (-α) :=
  min_le_right _ _

/-- For positive `c` and `α`, clipping loses at most the fixed factor
`min 1 c`. -/
theorem min_mul_rpow_le_powerExplorationSchedule
    (c : ℝ) (n₀ : ℕ) (α : ℝ)
    (hc : 0 < c) (hn₀ : 1 ≤ n₀) (hα : 0 < α) (i : ℕ) :
    min 1 c * Real.rpow (i + n₀ : ℝ) (-α) ≤
      powerExplorationSchedule c n₀ α i := by
  have hbase : (1 : ℝ) ≤ (i + n₀ : ℕ) := by
    exact_mod_cast hn₀.trans (Nat.le_add_left n₀ i)
  let x : ℝ := Real.rpow (i + n₀ : ℝ) (-α)
  have hx0 : 0 ≤ x := Real.rpow_nonneg (by positivity) _
  have hx1 : x ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos
      (by simpa only [Nat.cast_add] using hbase) (neg_nonpos.mpr hα.le)
  by_cases hc1 : c ≤ 1
  · have hminc : min 1 c = c := min_eq_right hc1
    have hcx1 : c * x ≤ 1 := by
      calc
        c * x ≤ c * 1 := mul_le_mul_of_nonneg_left hx1 hc.le
        _ = c := by ring
        _ ≤ 1 := hc1
    rw [powerExplorationSchedule, hminc]
    change c * x ≤ min 1 (c * x)
    rw [min_eq_right hcx1]
  · have hcge : 1 ≤ c := (lt_of_not_ge hc1).le
    have hminc : min 1 c = 1 := min_eq_left hcge
    rw [powerExplorationSchedule, hminc, one_mul]
    change x ≤ min 1 (c * x)
    apply le_min hx1
    nlinarith

/-- The cumulative clipped schedule is sandwiched between fixed multiples of
the shifted power sum. -/
theorem powerExplorationCumulativeMass_sandwich
    (c : ℝ) (n₀ : ℕ) (α : ℝ)
    (hc : 0 < c) (hn₀ : 1 ≤ n₀) (hα : 0 < α) (n : ℕ) :
    min 1 c * shiftedNegativeRpowSum n₀ α n ≤
        explorationCumulativeMass
          (powerExplorationSchedule c n₀ α) n ∧
      explorationCumulativeMass
          (powerExplorationSchedule c n₀ α) n ≤
        c * shiftedNegativeRpowSum n₀ α n := by
  constructor
  · unfold shiftedNegativeRpowSum explorationCumulativeMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    simpa [Nat.cast_add, add_comm, add_left_comm, add_assoc] using
      min_mul_rpow_le_powerExplorationSchedule
        c n₀ α hc hn₀ hα (k + 1)
  · unfold shiftedNegativeRpowSum explorationCumulativeMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    simpa [Nat.cast_add, add_comm, add_left_comm, add_assoc] using
      powerExplorationSchedule_le_mul_rpow c n₀ α (k + 1)

/-- Elementary lower bound: every term is at least the final shifted power. -/
theorem shiftedNegativeRpowSum_lower
    (n₀ : ℕ) (α : ℝ) (hn₀ : 1 ≤ n₀) (hα : 0 < α) (n : ℕ) :
    (n : ℝ) * Real.rpow ((n₀ : ℝ) + n) (-α) ≤
      shiftedNegativeRpowSum n₀ α n := by
  have hn₀pos : (0 : ℝ) < n₀ := by
    exact_mod_cast (Nat.zero_lt_of_lt hn₀)
  calc
    (n : ℝ) * Real.rpow ((n₀ : ℝ) + n) (-α) =
        ∑ _k ∈ Finset.range n,
          Real.rpow ((n₀ : ℝ) + n) (-α) := by simp
    _ ≤ shiftedNegativeRpowSum n₀ α n := by
      unfold shiftedNegativeRpowSum
      apply Finset.sum_le_sum
      intro k hk
      have hkNat : k + 1 ≤ n := Nat.succ_le_iff.mpr (Finset.mem_range.mp hk)
      have hkReal : (n₀ : ℝ) + (k + 1 : ℕ) ≤ (n₀ : ℝ) + n := by
        exact_mod_cast Nat.add_le_add_left hkNat n₀
      exact Real.rpow_le_rpow_of_nonpos
        (add_pos_of_pos_of_nonneg hn₀pos (Nat.cast_nonneg (k + 1)))
        hkReal (neg_nonpos.mpr hα.le)

/-- Integral upper bound for the shifted negative-power sum. -/
theorem shiftedNegativeRpowSum_le_integral
    (n₀ : ℕ) (α : ℝ) (hn₀ : 1 ≤ n₀) (hα : 0 < α) (n : ℕ) :
    shiftedNegativeRpowSum n₀ α n ≤
      ∫ x : ℝ in (n₀ : ℝ)..(n₀ : ℝ) + n, Real.rpow x (-α) := by
  have hn₀pos : (0 : ℝ) < n₀ := by
    exact_mod_cast (Nat.zero_lt_of_lt hn₀)
  have hanti : AntitoneOn (fun x : ℝ => Real.rpow x (-α))
      (Icc (n₀ : ℝ) ((n₀ : ℝ) + n)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
      (neg_nonpos.mpr hα.le)).mono (by
        intro x hx
        exact lt_of_lt_of_le hn₀pos hx.1)
  simpa [shiftedNegativeRpowSum, Nat.cast_add, add_comm,
    add_left_comm, add_assoc] using hanti.sum_le_integral

/-- Closed-form upper bound obtained by evaluating the power integral. -/
theorem shiftedNegativeRpowSum_upper
    (n₀ : ℕ) (α : ℝ)
    (hn₀ : 1 ≤ n₀) (hα0 : 0 < α) (hα1 : α < 1) (n : ℕ) :
    shiftedNegativeRpowSum n₀ α n ≤
      Real.rpow ((n₀ : ℝ) + n) (1 - α) / (1 - α) := by
  have hsum := shiftedNegativeRpowSum_le_integral n₀ α hn₀ hα0 n
  have hexponent : -1 < -α := by linarith
  have hden : 0 ≤ 1 - α := by linarith
  have hbaseNonneg : 0 ≤ Real.rpow (n₀ : ℝ) (1 - α) :=
    Real.rpow_nonneg (Nat.cast_nonneg n₀) _
  calc
    shiftedNegativeRpowSum n₀ α n ≤
        ∫ x : ℝ in (n₀ : ℝ)..(n₀ : ℝ) + n,
          Real.rpow x (-α) := hsum
    _ = (Real.rpow ((n₀ : ℝ) + n) (1 - α) -
          Real.rpow (n₀ : ℝ) (1 - α)) / (1 - α) := by
      change (∫ x : ℝ in (n₀ : ℝ)..(n₀ : ℝ) + n, x ^ (-α)) =
        (((n₀ : ℝ) + n) ^ (1 - α) - (n₀ : ℝ) ^ (1 - α)) / (1 - α)
      rw [integral_rpow (Or.inl hexponent)]
      ring_nf
    _ ≤ Real.rpow ((n₀ : ℝ) + n) (1 - α) / (1 - α) :=
      div_le_div_of_nonneg_right
        (sub_le_self _ hbaseNonneg) hden

end QubitOracle.Paper
