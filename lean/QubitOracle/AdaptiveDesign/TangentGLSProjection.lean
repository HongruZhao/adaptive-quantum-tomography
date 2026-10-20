import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel
import QubitOracle.AdaptiveDesign.GlobalPFSICLibrary
import QubitOracle.AdaptiveDesign.P2AdaptiveTheorem
import QubitOracle.AdaptiveDesign.PureMatrixController
import QubitOracle.AdaptiveDesign.TangentGLSGeometry
import QubitOracle.AdaptiveDesign.TangentGLSWeightExpansion
import QubitOracle.Paper.PureStateFoundations
/-!
# Intrinsic tangent projection and the quadratic normal error

These polynomial identities show why a new coordinate chart is unnecessary.
The normal part of the difference of two pure projectors is quadratic in
their difference.
-/

namespace QubitOracle.AdaptiveDesign.TangentGLS

open QubitOracle.Paper GlobalPFSICHermitian PureMatrixController
open scoped BigOperators InnerProductSpace ComplexOrder
noncomputable section

def tangentProjectionMatrix {d : ℕ} (h : PureVector d) (A : HermitianSpace (d+1)) :
    Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  rankOneDensity h.val * toMatrix A + toMatrix A * rankOneDensity h.val -
    (rankOneDensity h.val * toMatrix A * rankOneDensity h.val +
      rankOneDensity h.val * toMatrix A * rankOneDensity h.val)

theorem tangentProjectionMatrix_hermitian {d : ℕ} (h : PureVector d)
    (A : HermitianSpace (d+1)) : (tangentProjectionMatrix h A).IsHermitian := by
  have hp : (rankOneDensity h.val).IsHermitian := (GlobalPFSIC.projector_posSemidef h.val).isHermitian
  change (tangentProjectionMatrix h A).conjTranspose = tangentProjectionMatrix h A
  simp only [tangentProjectionMatrix, Matrix.conjTranspose_sub, Matrix.conjTranspose_add,
    Matrix.conjTranspose_mul, hp.eq, (toMatrix_isHermitian A).eq, Matrix.mul_assoc]
  abel

def tangentProjectionVector {d : ℕ} (h : PureVector d) (A : HermitianSpace (d+1)) :
    HermitianSpace (d+1) :=
  ofMatrix (tangentProjectionMatrix h A) (tangentProjectionMatrix_hermitian h A)

theorem tangentProjectionVector_mem {d : ℕ} (h : PureVector d) (A : HermitianSpace (d+1)) :
    tangentProjectionVector h A ∈ tangentSpace h := by
  rw [tangentSpace_mem]
  change rankOneDensity h.val * tangentProjectionMatrix h A +
    tangentProjectionMatrix h A * rankOneDensity h.val = tangentProjectionMatrix h A
  have hp := pureProjector_idempotent h
  simp only [tangentProjectionMatrix, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (rankOneDensity h.val) (rankOneDensity h.val), hp]
  abel

theorem tangentProjectionVector_inner {d : ℕ} (h : PureVector d)
    (A : HermitianSpace (d+1)) (D : tangentSpace h) :
    ⟪tangentProjectionVector h A, D.val⟫_ℝ = ⟪A, D.val⟫_ℝ := by
  let P := rankOneDensity h.val
  let B := toMatrix A
  let V := toMatrix D.val
  have hD : P * V + V * P = V := (tangentSpace_mem h D.val).mp D.property
  have hzero : P * V * P = 0 := tangent_sandwich_zero h D
  have hcross : Matrix.trace (V * P * B * P) = 0 := by
    rw [Matrix.trace_mul_comm]
    have heq : P * (V * P * B) = (P * V * P) * B := by noncomm_ring
    rw [heq, hzero, Matrix.zero_mul, Matrix.trace_zero]
  have hswap : Matrix.trace (V * B * P) = Matrix.trace (P * V * B) := by
    rw [Matrix.trace_mul_comm]
    congr 1
    noncomm_ring
  have heq : V * tangentProjectionMatrix h A =
      V * P * B + V * B * P - (V * P * B * P + V * P * B * P) := by
    unfold tangentProjectionMatrix
    dsimp [P, B, V]
    noncomm_ring
  have ht : Matrix.trace (V * tangentProjectionMatrix h A) = Matrix.trace (V * B) := by
    rw [heq, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_add, hcross, hswap]
    simp only [add_zero, sub_zero]
    rw [add_comm, ← Matrix.trace_add, ← Matrix.add_mul, hD]
  simpa only [inner_eq_trace, tangentProjectionVector, toMatrix_ofMatrix] using congrArg Complex.re ht

/-- The polynomial expression is the orthogonal projection used by the
implemented least-squares system. -/
theorem tangentProjectionVector_eq_projection {d : ℕ} (h : PureVector d)
    (A : HermitianSpace (d+1)) :
    ((tangentSpace h).orthogonalProjectionOnto A).val = tangentProjectionVector h A := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (tangentProjectionVector_mem h A)
  intro D hD
  rw [inner_sub_left, tangentProjectionVector_inner h A ⟨D, hD⟩, sub_self]

/-- The normal part of `P - P0` equals `2 P (P-P0)^2 P - (P-P0)^2`.
In particular its Taylor expansion has no linear term. -/
theorem preliminaryError_normal_quadratic {d : ℕ} (h truth : PureVector d) :
    (rankOneDensity h.val - rankOneDensity truth.val) -
        toMatrix (preliminaryTangentError h truth).val =
      (rankOneDensity h.val *
        ((rankOneDensity h.val - rankOneDensity truth.val) *
          (rankOneDensity h.val - rankOneDensity truth.val)) * rankOneDensity h.val +
       rankOneDensity h.val *
        ((rankOneDensity h.val - rankOneDensity truth.val) *
          (rankOneDensity h.val - rankOneDensity truth.val)) * rankOneDensity h.val) -
      (rankOneDensity h.val - rankOneDensity truth.val) *
        (rankOneDensity h.val - rankOneDensity truth.val) := by
  have hp := pureProjector_idempotent h
  have ht := pureProjector_idempotent truth
  unfold preliminaryTangentError
  rw [tangentProjectionVector_eq_projection]
  change _ - tangentProjectionMatrix h
    ((P2Adaptive.pureParameter d h).val - (P2Adaptive.pureParameter d truth).val) = _
  unfold tangentProjectionMatrix
  change _ - (rankOneDensity h.val * (rankOneDensity h.val - rankOneDensity truth.val) +
      (rankOneDensity h.val - rankOneDensity truth.val) * rankOneDensity h.val -
      (rankOneDensity h.val * (rankOneDensity h.val - rankOneDensity truth.val) * rankOneDensity h.val +
       rankOneDensity h.val * (rankOneDensity h.val - rankOneDensity truth.val) * rankOneDensity h.val)) = _
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_assoc, ← Matrix.mul_assoc (rankOneDensity h.val) (rankOneDensity h.val), hp, ht]
  abel

end
end QubitOracle.AdaptiveDesign.TangentGLS
