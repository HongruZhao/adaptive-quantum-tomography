import QubitOracle.TwoBasis

/-!
# Uniform outcome probabilities of the pure-state two-basis oracle

The two adapted bases have uniform probability at the chart center.  This is
the finite-dimensional positivity input used in the regular-round likelihood
analysis.
-/

namespace QubitOracle
namespace Paper

noncomputable section

/-- Every outcome of either oracle basis has probability `1 / (n + 1)` at
the reference ray. -/
theorem baseProbability_eq_inv_dimension {n : ℕ} (F : OracleFrame n)
    (k : Fin (n + 1)) :
    baseProbability F k = 1 / (n + 1 : ℝ) := by
  rw [baseProbability, F.uniformFirstRow]
  have hd : 0 < (n + 1 : ℝ) := by positivity
  have hs : Real.sqrt (n + 1 : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hd)
  have hsquare : Real.sqrt (n + 1 : ℝ) ^ 2 = (n + 1 : ℝ) :=
    Real.sq_sqrt hd.le
  field_simp [hs]
  nlinarith

/-- The paper's eventual regularity margin `1 / (2d)` is strictly below the
oracle probability `1 / d`. -/
theorem halfDimensionInv_le_baseProbability {n : ℕ} (F : OracleFrame n)
    (k : Fin (n + 1)) :
    1 / (2 * (n + 1 : ℝ)) ≤ baseProbability F k := by
  rw [baseProbability_eq_inv_dimension]
  have hd : 0 < (n + 1 : ℝ) := by positivity
  have htwo : 0 < (2 : ℝ) * (n + 1 : ℝ) := mul_pos (by norm_num) hd
  rw [div_le_div_iff₀ htwo hd]
  nlinarith

/-- In particular, every oracle outcome probability is positive. -/
theorem baseProbability_pos {n : ℕ} (F : OracleFrame n)
    (k : Fin (n + 1)) :
    0 < baseProbability F k := by
  rw [baseProbability_eq_inv_dimension]
  positivity

end

end Paper
end QubitOracle
