import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import QubitOracle.Paper.LogThirdOrderRemainderCore

/-!
# Scalar logarithm Taylor bound

Mathlib's complex logarithm estimate
`Complex.norm_log_sub_logTaylor_le` is specialized to real inputs.  On
`|x| <= 1/2` it gives a `2/3 * |x|^3` remainder, which is stronger than the
`8/3 * |x|^3` envelope used by the adaptive Bernoulli LAN module.
-/

namespace QubitOracle.Paper

noncomputable section

theorem logThirdOrderRemainder_le_twoThirds
    (x : ℝ) (hx : |x| ≤ 1 / 2) :
    |logThirdOrderRemainder x| ≤ (2 / 3 : ℝ) * |x| ^ 3 := by
  have hxlt : ‖(x : ℂ)‖ < 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using
      hx.trans_lt (by norm_num : (1 / 2 : ℝ) < 1)
  have hxpos : 0 ≤ 1 + x := by
    have hneg : -x ≤ |x| := neg_le_abs x
    linarith
  have hcomplex :=
    Complex.norm_log_sub_logTaylor_le 2 (z := (x : ℂ)) hxlt
  have hremainder :
      ((logThirdOrderRemainder x : ℝ) : ℂ) =
        Complex.log (1 + (x : ℂ)) -
          Complex.logTaylor 3 (x : ℂ) := by
    rw [show (1 + (x : ℂ)) = ((1 + x : ℝ) : ℂ) by norm_num]
    rw [← Complex.ofReal_log hxpos]
    simp [logThirdOrderRemainder, Complex.logTaylor,
      Finset.sum_range_succ]
    ring
  rw [← hremainder] at hcomplex
  simp only [Complex.norm_real, Real.norm_eq_abs] at hcomplex
  norm_num at hcomplex
  have hinverse : (1 - |x|)⁻¹ ≤ (2 : ℝ) := by
    rw [inv_le_comm₀ (by linarith : 0 < 1 - |x|) (by norm_num : 0 < (2 : ℝ))]
    linarith
  calc
    |logThirdOrderRemainder x| ≤
        |x| ^ 3 * (1 - |x|)⁻¹ / 3 := by
      simpa [Complex.norm_real, Real.norm_eq_abs] using hcomplex
    _ ≤ |x| ^ 3 * 2 / 3 := by
      gcongr
    _ = (2 / 3 : ℝ) * |x| ^ 3 := by ring

theorem logThirdOrderRemainder_contract :
    LogThirdOrderRemainderContract := by
  intro x hx
  calc
    |logThirdOrderRemainder x| ≤ (2 / 3 : ℝ) * |x| ^ 3 :=
      logThirdOrderRemainder_le_twoThirds x hx
    _ ≤ (8 / 3 : ℝ) * |x| ^ 3 := by
      have hpow : 0 ≤ |x| ^ 3 := pow_nonneg (abs_nonneg x) 3
      nlinarith

namespace Label

theorem lem_SI_log_third_order_remainder :
    LogThirdOrderRemainderContract :=
  logThirdOrderRemainder_contract

end Label
end

end QubitOracle.Paper
