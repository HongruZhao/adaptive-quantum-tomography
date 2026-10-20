import QubitOracle.AdaptiveDesign.NearestPureVariational
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.Hermitian

/-! The nearest-projector selection used in the algorithm is a leading
algebraic-eigenvalue eigenvector, including eigenvalue ties. -/
namespace QubitOracle.AdaptiveDesign.PureMatrixController
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian P2Adaptive TangentGLS
open scoped BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

def hermitianOperator {d : ℕ} (A : HermitianSpace (d+1)) :
    EuclideanSpace ℂ (Fin (d+1)) →L[ℂ] EuclideanSpace ℂ (Fin (d+1)) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (d+1)) (toMatrix A)

theorem hermitianOperator_selfAdjoint {d : ℕ} (A : HermitianSpace (d+1)) :
    IsSelfAdjoint (hermitianOperator A) :=
  (toMatrix_isHermitian A).isSelfAdjoint.map (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (d+1)))

theorem hermitianOperator_quadratic {d : ℕ} (A : HermitianSpace (d+1))
    (v : EuclideanSpace ℂ (Fin (d+1))) :
    (hermitianOperator A).reApplyInnerSelf v = (GlobalPFSIC.quadratic (toMatrix A) v.ofLp).re := by
  simp only [ContinuousLinearMap.reApplyInnerSelf_apply, hermitianOperator]
  rw [inner_re_symm]
  simp [PiLp.inner_apply, GlobalPFSIC.quadratic,
    Matrix.mulVec, dotProduct, Finset.mul_sum, Complex.re_sum,
    mul_comm, mul_left_comm, mul_assoc]

/-- Largest algebraic eigenvalue, expressed as the supremum of the
Rayleigh quotient over nonzero vectors. No positive-definiteness or
simple-eigenvalue assumption is imposed. -/
theorem nearestVector_leadingEigenvector {d : ℕ} (A : HermitianSpace (d+1)) :
    Module.End.HasEigenvector (hermitianOperator A).toLinearMap
      ((⨆ v : {v : EuclideanSpace ℂ (Fin (d+1)) // v ≠ 0},
        (hermitianOperator A).rayleighQuotient v.val : ℝ) : ℂ)
      (pureVector (nearestVector d (toMatrix A))) := by
  apply (hermitianOperator_selfAdjoint A).hasEigenvector_of_isMaxOn
  · apply norm_ne_zero_iff.mp
    rw [pureVector_norm]
    norm_num
  · intro v hv
    have hn : ‖v‖ = 1 := by simpa [pureVector_norm] using hv
    let g : PureVector d := ⟨v.ofLp, by
      change (∑ i, Complex.normSq (v.ofLp i)) = 1
      have he := congrArg (fun r : ℝ => r^2) hn
      rw [EuclideanSpace.norm_sq_eq] at he
      simpa [Complex.sq_norm] using he⟩
    change (hermitianOperator A).reApplyInnerSelf v ≤
      (hermitianOperator A).reApplyInnerSelf (pureVector (nearestVector d (toMatrix A)))
    rw [hermitianOperator_quadratic, hermitianOperator_quadratic]
    exact nearestVector_maximizes_rayleigh A g

end
end QubitOracle.AdaptiveDesign.PureMatrixController
