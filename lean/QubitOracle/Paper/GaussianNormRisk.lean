import QubitOracle.Paper.CappedQuadraticLoss
import QubitOracle.Paper.SourceFaithfulMinimax

/-!
# Gaussian squared-norm risk

This file evaluates the quadratic risk of the finite-dimensional centered
Gaussian limit experiment.  It is proved from Mathlib's Gaussian moment
identities; no paper-specific axiom is used.
-/

namespace QubitOracle.Paper

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace BigOperators

noncomputable section

/-- Every coordinate second moment of a centered multivariate Gaussian is the
corresponding diagonal covariance entry. -/
theorem integral_sq_eval_multivariateGaussian
    {D : Type*} [Fintype D] [DecidableEq D]
    (S : Matrix D D ℝ) (hS : S.PosSemidef) (i : D) :
    ∫ x, (x i) ^ 2 ∂multivariateGaussian (0 : LANParameter D) S = S i i := by
  have hmean : ∫ x, x i ∂multivariateGaussian (0 : LANParameter D) S = 0 := by
    rw [← EuclideanSpace.coe_proj, ContinuousLinearMap.integral_comp_id_comm]
    · simp
    · exact IsGaussian.integrable_id
  rw [← variance_eval_multivariateGaussian hS,
    variance_of_integral_eq_zero (by fun_prop) hmean]

/-- The Gaussian squared Euclidean risk is the trace of its covariance. -/
theorem integral_norm_sq_multivariateGaussian
    {D : Type*} [Fintype D] [DecidableEq D]
    (S : Matrix D D ℝ) (hS : S.PosSemidef) :
    ∫ x, ‖x‖ ^ 2 ∂multivariateGaussian (0 : LANParameter D) S = Matrix.trace S := by
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum]
  · simp_rw [integral_sq_eval_multivariateGaussian S hS]
    rfl
  · intro i hi
    exact (IsGaussian.memLp_two_id.continuousLinearMap_comp
      (EuclideanSpace.proj i : LANParameter D →L[ℝ] ℝ)).integrable_sq

/-- `lintegral` form of the Gaussian quadratic-risk identity, matching the
loss convention used by the minimax interface. -/
theorem lintegral_ofReal_norm_sq_multivariateGaussian
    {D : Type*} [Fintype D] [DecidableEq D]
    (S : Matrix D D ℝ) (hS : S.PosSemidef) :
    (∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2)
        ∂multivariateGaussian (0 : LANParameter D) S) =
      ENNReal.ofReal (Matrix.trace S) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_norm_sq_multivariateGaussian S hS]
  · exact (IsGaussian.memLp_two_id
      (μ := multivariateGaussian (0 : LANParameter D) S)).integrable_norm_pow'
  · exact ae_of_all _ fun x => sq_nonneg ‖x‖

/-- The bounded capped risks increase to the exact Gaussian quadratic risk.
This is the cap-removal step used after applying a bounded-loss minimax theorem. -/
theorem lintegral_cappedSquaredNormLoss_multivariateGaussian_tendsto
    {D : Type*} [Fintype D] [DecidableEq D]
    (S : Matrix D D ℝ) (hS : S.PosSemidef) :
    Filter.Tendsto
      (fun n : ℕ => ∫⁻ x, cappedSquaredNormLoss (n : ENNReal) x
        ∂multivariateGaussian (0 : LANParameter D) S)
      Filter.atTop (nhds (ENNReal.ofReal (Matrix.trace S))) := by
  have hRisk :
      (∫⁻ x, ‖x‖ₑ ^ 2 ∂multivariateGaussian (0 : LANParameter D) S) =
        ENNReal.ofReal (Matrix.trace S) := by
    rw [← lintegral_ofReal_norm_sq_multivariateGaussian S hS]
    congr 1
    funext x
    rw [← ofReal_norm]
    exact (ENNReal.ofReal_pow (norm_nonneg x) 2).symm
  simpa [hRisk] using
    (lintegral_cappedSquaredNormLoss_tendsto
      (multivariateGaussian (0 : LANParameter D) S))

end

end QubitOracle.Paper
