import Mathlib

/-! Supporting definitions and proved lemmas used by the manuscript. -/

namespace QubitOracle.Paper

open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory

noncomputable section






/-- Every fixed deterministic score envelope becomes negligible after the
root-sample-size normalization. -/
theorem constant_div_sqrt_nat_tendsto_zero (B : Real) :
    Tendsto (fun n : Nat => B / Real.sqrt (n : Real)) atTop (nhds 0) := by
  have hsqrt : Tendsto (fun n : Nat => Real.sqrt (n : Real)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv :
      Tendsto (fun n : Nat => (Real.sqrt (n : Real))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  simpa [div_eq_mul_inv] using
    (tendsto_const_nhds.mul hinv :
      Tendsto (fun n : Nat => B * (Real.sqrt (n : Real))⁻¹)
        atTop (nhds (B * 0)))


end

end QubitOracle.Paper
