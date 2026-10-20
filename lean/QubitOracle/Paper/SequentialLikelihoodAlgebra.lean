import Mathlib

/-!
# Algebraic core of adaptive likelihood factorization

The measure-theoretic Radon--Nikodym chain rule remains in the external
probability layer.  Once a realized adaptive history is fixed, however, the
parameter-independent policy factor cancels and the remaining finite product
identity is ordinary field algebra, checked here.
-/

namespace QubitOracle
namespace Paper

open scoped BigOperators

/-- A common nonzero policy mass cancels from the realized-path likelihood
ratio. -/
theorem commonPolicyMass_cancels (q numerator denominator : ℝ)
    (hq : q ≠ 0) :
    (q * numerator) / (q * denominator) = numerator / denominator := by
  field_simp [hq]

/-- The ratio of finite products is the product of the shotwise ratios. -/
theorem finiteLikelihoodRatio_eq_productRatios
    {ι : Type} (rounds : Finset ι) (p p' : ι → ℝ) :
    rounds.prod p' / rounds.prod p =
      rounds.prod (fun i => p' i / p i) := by
  exact (Finset.prod_div_distrib (s := rounds) p' p).symm

/-- Combining the preceding identities gives the finite realized-history
factorization used by the adaptive likelihood proof. -/
theorem adaptivePathLikelihoodRatio_factorization
    {ι : Type} (rounds : Finset ι) (q : ℝ) (p p' : ι → ℝ)
    (hq : q ≠ 0) :
    (q * rounds.prod p') / (q * rounds.prod p) =
      rounds.prod (fun i => p' i / p i) := by
  rw [commonPolicyMass_cancels q _ _ hq]
  exact finiteLikelihoodRatio_eq_productRatios rounds p p'

end Paper
end QubitOracle
