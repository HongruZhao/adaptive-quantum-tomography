import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace QubitOracle.Paper

noncomputable section

/-- Third-order remainder after the quadratic expansion of `log (1+x)`. -/
def logThirdOrderRemainder (x : ℝ) : ℝ :=
  Real.log (1 + x) - x + x ^ 2 / 2

/-- The scalar Taylor envelope used by the finite LAN algebra. -/
def LogThirdOrderRemainderContract : Prop :=
  ∀ x : ℝ, |x| ≤ 1 / 2 →
    |logThirdOrderRemainder x| ≤ (8 / 3 : ℝ) * |x| ^ 3

end
end QubitOracle.Paper
