-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMSharpMoments
import QubitOracle.AdaptiveDesign.PVMRealizedGram

/-! Each complete-basis measurement frame is an orthogonal projection,
and therefore has operator norm at most one. -/
namespace QubitOracle.AdaptiveDesign.PVMFrameProjection
open QubitOracle.Paper GlobalPFSICHermitian GlobalPFSICBorn PVMGeometry
open PVMPilotGLS TangentGLS
open scoped BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem basisEffect_orthonormal {d : ℕ} (U : Action d) :
    Orthonormal ℝ (basisEffect U) := by
  rw [orthonormal_iff_ite]
  intro i j
  by_cases hij : i=j
  · subst j
    simp [real_inner_self_eq_norm_sq,PVMSharpMoments.basisEffect_norm]
  · rw [if_neg hij,inner_eq_trace,basisEffect_orthogonal,if_neg (Ne.symm hij)]
    simp

theorem frame_norm_le {d : ℕ} (U : Action d) (A : HermitianSpace (d+1)) :
    ‖basisGramOperator U A‖≤‖A‖ := by
  have ho := basisEffect_orthonormal U
  have hb := ho.sum_inner_products_le (s:=Finset.univ) A
  have hs : ‖basisGramOperator U A‖^2=∑ k, ⟪basisEffect U k,A⟫_ℝ^2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [basisGramOperator,gramCLM_apply,one_mul]
    rw [ho.inner_sum]
    simp [pow_two]
  have hh : ‖basisGramOperator U A‖^2≤‖A‖^2 := by
    rw [hs]
    simpa only [Real.norm_eq_abs,sq_abs] using hb
  nlinarith [norm_nonneg A,norm_nonneg (basisGramOperator U A)]

theorem frame_operator_norm_le_one {d : ℕ} (U : Action d) : ‖basisGramOperator U‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  simpa only [one_mul] using frame_norm_le U A

end
end QubitOracle.AdaptiveDesign.PVMFrameProjection

-/
