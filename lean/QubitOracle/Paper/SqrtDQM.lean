import QubitOracle.Paper.ProtocolRegularity

/-!
# A kernel-checked square-root DQM remainder

This file proves the scalar analytic estimate needed to discharge the DQM
condition for binary qubit projective measurements.  It is deliberately
independent of the adaptive controller: once the two Born probabilities have
a common positive floor, the square-root likelihood remainder is quadratic in
the probability increment.
-/

namespace QubitOracle.Paper

noncomputable section

/-- Exact algebraic remainder after linearizing `sqrt` at a positive point. -/
theorem sqrt_sub_linearization_identity
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    Real.sqrt a - Real.sqrt b - (a - b) / (2 * Real.sqrt b) =
      -((a - b) ^ 2) /
        (2 * Real.sqrt b * (Real.sqrt a + Real.sqrt b) ^ 2) := by
  have hsa : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hsqrtb : Real.sqrt b ≠ 0 := ne_of_gt hsb
  have hsum : Real.sqrt a + Real.sqrt b ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos hsa hsb)
  have hsa_sq : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha
  have hsb_sq : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt (le_of_lt hb)
  field_simp [hsqrtb, hsum]
  nlinarith

/-- A common positive floor controls the absolute square-root DQM remainder. -/
theorem abs_sqrt_sub_linearization_le
    {a b m : ℝ} (hm : 0 < m) (ha : m ≤ a) (hb : m ≤ b) :
    |Real.sqrt a - Real.sqrt b - (a - b) / (2 * Real.sqrt b)| ≤
      (a - b) ^ 2 / (2 * m * Real.sqrt m) := by
  have ha0 : 0 ≤ a := le_trans (le_of_lt hm) ha
  have hb0 : 0 ≤ b := le_trans (le_of_lt hm) hb
  have hbpos : 0 < b := lt_of_lt_of_le hm hb
  have hsma : Real.sqrt m ≤ Real.sqrt a := Real.sqrt_le_sqrt ha
  have hsmb : Real.sqrt m ≤ Real.sqrt b := Real.sqrt_le_sqrt hb
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hsa : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have hsb : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
  have hsum : Real.sqrt m ≤ Real.sqrt a + Real.sqrt b := by
    exact hsma.trans (le_add_of_nonneg_right hsb)
  have hsq : (Real.sqrt m) ^ 2 ≤
      (Real.sqrt a + Real.sqrt b) ^ 2 := by
    nlinarith [sq_nonneg (Real.sqrt a + Real.sqrt b - Real.sqrt m)]
  have hfirst :
      Real.sqrt m * (Real.sqrt m) ^ 2 ≤
        Real.sqrt m * (Real.sqrt a + Real.sqrt b) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq (le_of_lt hsm)
  have hsecond :
      Real.sqrt m * (Real.sqrt a + Real.sqrt b) ^ 2 ≤
        Real.sqrt b * (Real.sqrt a + Real.sqrt b) ^ 2 :=
    mul_le_mul_of_nonneg_right hsmb (sq_nonneg _)
  have hsm_sq : (Real.sqrt m) ^ 2 = m :=
    Real.sq_sqrt (le_of_lt hm)
  have hden_le :
      2 * m * Real.sqrt m ≤
        2 * Real.sqrt b * (Real.sqrt a + Real.sqrt b) ^ 2 := by
    nlinarith
  have hden0 : 0 < 2 * m * Real.sqrt m := by positivity
  have hden :
      0 < 2 * Real.sqrt b * (Real.sqrt a + Real.sqrt b) ^ 2 := by
    have hab : 0 < Real.sqrt a + Real.sqrt b := by
      exact lt_of_lt_of_le hsm hsum
    positivity
  rw [sqrt_sub_linearization_identity ha0 hbpos]
  rw [abs_div, abs_neg, abs_of_nonneg (sq_nonneg (a - b)), abs_of_pos hden]
  exact (div_le_div_iff₀ hden hden0).2
    (mul_le_mul_of_nonneg_left hden_le (sq_nonneg (a - b)))

end

end QubitOracle.Paper
