import Mathlib

/-!
# Algebraic Gaussian quadratic-risk identity

For a centered random vector with covariance `Sigma`, expansion of
`E[Z^T G Z]` reduces the expectation to the finite contraction defined here.
The probability-theoretic fact that a Gaussian vector has its declared
covariance belongs to the external probability layer; the trace reduction is
kernel-checked in this module.
-/

namespace QubitOracle
namespace Paper

open scoped BigOperators

/-- Finite contraction of a quadratic-loss matrix with a covariance matrix. -/
def covarianceQuadraticRisk {ι : Type} [Fintype ι]
    (G Sigma : Matrix ι ι ℝ) : ℝ :=
  ∑ i, ∑ j, G i j * Sigma j i

/-- The covariance contraction is the trace of `G * Sigma`. -/
theorem covarianceQuadraticRisk_eq_trace {ι : Type} [Fintype ι]
    [DecidableEq ι] (G Sigma : Matrix ι ι ℝ) :
    covarianceQuadraticRisk G Sigma = Matrix.trace (G * Sigma) := by
  simp [covarianceQuadraticRisk, Matrix.trace, Matrix.mul_apply]

/-- In particular, covariance `M^{-1}` gives the LAN quadratic-risk constant
`trace (G M^{-1})`. -/
theorem gaussianShiftQuadraticRisk_eq_trace_inv {ι : Type} [Fintype ι]
    [DecidableEq ι] (G M : Matrix ι ι ℝ) :
    covarianceQuadraticRisk G M⁻¹ = Matrix.trace (G * M⁻¹) :=
  covarianceQuadraticRisk_eq_trace G M⁻¹

end Paper
end QubitOracle
