import QubitOracle.AdaptiveDesign.TangentGLSGeometry
import QubitOracle.AdaptiveDesign.GlobalPFSICTransport

/-!
# Exact matrix form of the implemented vector update

The normalized vector and intrinsic projector formula are the same estimator.
The remainder after its tangent linear term is displayed exactly.
-/

namespace QubitOracle.AdaptiveDesign.TangentGLS

open QubitOracle.Paper GlobalPFSICHermitian PureMatrixController
open scoped BigOperators InnerProductSpace ComplexOrder
noncomputable section

theorem projector_real_smul {d : ℕ} (a : ℝ) (v : Fin (d+1) → ℂ) :
    rankOneDensity (a • v) = (a^2) • rankOneDensity v := by
  ext i j
  simp [rankOneDensity, Complex.real_smul, star_mul]
  push_cast
  ring

theorem unnormalizedVector_eq_mulVec {d : ℕ} (h : PureVector d) (A : tangentSpace h) :
    (unnormalizedVector h A).ofLp = (1 + toMatrix A.val).mulVec h.val := by
  ext i
  simp [unnormalizedVector, pureVector, tangentVector, Matrix.add_mulVec]

theorem tangent_numerator {d : ℕ} (h : PureVector d) (A : tangentSpace h) :
    (1 + toMatrix A.val) * rankOneDensity h.val * (1 + toMatrix A.val) =
      rankOneDensity h.val + toMatrix A.val +
        toMatrix A.val * rankOneDensity h.val * toMatrix A.val := by
  have ht := (tangentSpace_mem h A.val).mp A.property
  calc
    _ = rankOneDensity h.val +
        (rankOneDensity h.val * toMatrix A.val + toMatrix A.val * rankOneDensity h.val) +
        toMatrix A.val * rankOneDensity h.val * toMatrix A.val := by noncomm_ring
    _ = _ := by rw [ht]

theorem unnormalized_projector {d : ℕ} (h : PureVector d) (A : tangentSpace h) :
    rankOneDensity (unnormalizedVector h A).ofLp =
      rankOneDensity h.val + toMatrix A.val +
        toMatrix A.val * rankOneDensity h.val * toMatrix A.val := by
  rw [unnormalizedVector_eq_mulVec]
  change GlobalPFSIC.projector ((1 + toMatrix A.val).mulVec h.val) = _
  rw [GlobalPFSIC.projector_mulVec]
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, (toMatrix_isHermitian A.val).eq]
  exact tangent_numerator h A

theorem updatedState_matrix_formula {d : ℕ} (h : PureVector d) (A : tangentSpace h) :
    updatedState h A = (1 + ‖tangentVector h A‖ ^ 2)⁻¹ •
      (rankOneDensity h.val + toMatrix A.val +
        toMatrix A.val * rankOneDensity h.val * toMatrix A.val) := by
  have hv : (updatedPureVector h A).val =
      (‖unnormalizedVector h A‖⁻¹ : ℝ) • (unnormalizedVector h A).ofLp := rfl
  unfold updatedState
  rw [hv, projector_real_smul, inv_pow, unnormalizedVector_norm_sq, unnormalized_projector]

/-- Normalization changes the linear tangent step only by the explicit
quadratic numerator divided by `1 + ||Delta h||^2`. -/
theorem updatedState_exact_remainder {d : ℕ} (h : PureVector d) (A : tangentSpace h) :
    updatedState h A - (rankOneDensity h.val + toMatrix A.val) =
      (1 + ‖tangentVector h A‖ ^ 2)⁻¹ •
        (toMatrix A.val * rankOneDensity h.val * toMatrix A.val -
          (‖tangentVector h A‖ ^ 2) • (rankOneDensity h.val + toMatrix A.val)) := by
  rw [updatedState_matrix_formula]
  have hden : 1 + ‖tangentVector h A‖ ^ 2 ≠ 0 := by positivity
  have hid : (1 + ‖tangentVector h A‖ ^ 2)⁻¹ * (1 + ‖tangentVector h A‖ ^ 2) = 1 :=
    inv_mul_cancel₀ hden
  have hscale : rankOneDensity h.val + toMatrix A.val =
      (1 + ‖tangentVector h A‖ ^ 2)⁻¹ •
        ((1 + ‖tangentVector h A‖ ^ 2) • (rankOneDensity h.val + toMatrix A.val)) := by
    rw [smul_smul, hid, one_smul]
  conv_lhs => rhs; rw [hscale]
  rw [← smul_sub]
  congr 1
  rw [add_smul, one_smul]
  abel

end
end QubitOracle.AdaptiveDesign.TangentGLS
