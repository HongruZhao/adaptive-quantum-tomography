import QubitOracle.RankOneLosses

/-!
# Pure-state Bures control under local rescaling

This module kernel-checks the deterministic Bures estimate used in the
rank-one part of the adaptive-LAN argument.  It does not invoke probability
or asymptotic notation: the statistical substitution `a = 1 / sqrt n` can be
made after supplying the corresponding arithmetic bounds.
-/

namespace QubitOracle
namespace Paper

open scoped BigOperators

noncomputable section

/-- Squared tangent radius scales quadratically. -/
theorem tangentRadiusSq_smul {n : ℕ} (a : ℝ)
    (h : TangentIndex n → ℝ) :
    tangentRadiusSq (a • h) = a ^ 2 * tangentRadiusSq h := by
  simp only [tangentRadiusSq, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The exact pure-state Bures remainder after an arbitrary local scaling. -/
theorem buresChartLoss_smul_remainder_bounds {n : ℕ} (a : ℝ)
    (h : TangentIndex n → ℝ)
    (hchart : a ^ 2 * tangentRadiusSq h ≤ 4) :
    0 ≤ buresChartLoss (a • h) -
        (a ^ 2 * tangentRadiusSq h) / 4 ∧
    buresChartLoss (a • h) -
        (a ^ 2 * tangentRadiusSq h) / 4 ≤
      a ^ 4 * (tangentRadiusSq h) ^ 2 / 16 := by
  have hscaled : tangentRadiusSq (a • h) ≤ 4 := by
    rw [tangentRadiusSq_smul]
    exact hchart
  have hb := buresChartLoss_remainder_bounds (a • h) hscaled
  rw [tangentRadiusSq_smul] at hb
  constructor
  · exact hb.1
  · calc
      buresChartLoss (a • h) - (a ^ 2 * tangentRadiusSq h) / 4
          ≤ (a ^ 2 * tangentRadiusSq h) ^ 2 / 16 := hb.2
      _ = a ^ 4 * (tangentRadiusSq h) ^ 2 / 16 := by ring

/-- A direct upper bound with the quadratic term and fourth-order remainder. -/
theorem buresChartLoss_smul_upper {n : ℕ} (a : ℝ)
    (h : TangentIndex n → ℝ)
    (hchart : a ^ 2 * tangentRadiusSq h ≤ 4) :
    buresChartLoss (a • h) ≤
      (a ^ 2 * tangentRadiusSq h) / 4 +
      a ^ 4 * (tangentRadiusSq h) ^ 2 / 16 := by
  have hb := buresChartLoss_smul_remainder_bounds a h hchart
  linarith [hb.2]

end

end Paper
end QubitOracle
