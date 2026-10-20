import Mathlib
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
/-! Exact matrix identities in the paper's information-invariance display.
The same invertible Jacobian changes the classical and quantum metrics;
the loss weight must be transformed as well. -/
namespace QubitOracle.AdaptiveDesign.InformationCoordinateInvariance
open Matrix
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem inverse_congruence (H J : Matrix ι ι ℝ) :
    (J.transpose * H * J)⁻¹ = J⁻¹ * H⁻¹ * (J⁻¹).transpose := by
  simp only [Matrix.mul_inv_rev, ← Matrix.transpose_nonsing_inv, Matrix.mul_assoc]

theorem information_ratio_congruence (H I J : Matrix ι ι ℝ)
    (hJ : IsUnit J.det) :
    (J.transpose * H * J)⁻¹ * (J.transpose * I * J) = J⁻¹ * H⁻¹ * I * J := by
  rw [inverse_congruence]
  have ht : (J⁻¹).transpose * J.transpose = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hJ, Matrix.transpose_one]
  calc
    _ = J⁻¹ * H⁻¹ * ((J⁻¹).transpose * J.transpose) * I * J := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [ht, Matrix.mul_one]

theorem trace_information_invariant (H I J : Matrix ι ι ℝ)
    (hJ : IsUnit J.det) :
    Matrix.trace ((J.transpose * H * J)⁻¹ * (J.transpose * I * J)) =
      Matrix.trace (H⁻¹ * I) := by
  rw [information_ratio_congruence H I J hJ, Matrix.trace_mul_comm]
  simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv J hJ, Matrix.one_mul]

theorem weighted_covariance_trace_invariant (W I J : Matrix ι ι ℝ)
    (hJ : IsUnit J.det) :
    Matrix.trace ((J.transpose * W * J) * (J.transpose * I * J)⁻¹) =
      Matrix.trace (W * I⁻¹) := by
  rw [Matrix.trace_mul_comm, trace_information_invariant I W J hJ, Matrix.trace_mul_comm]

end
end QubitOracle.AdaptiveDesign.InformationCoordinateInvariance
