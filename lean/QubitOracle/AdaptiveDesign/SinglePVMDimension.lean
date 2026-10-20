import QubitOracle.AdaptiveDesign.GlobalPFSICBornModel
import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel
import QubitOracle.AdaptiveDesign.GlobalPFSICLibrary
import QubitOracle.AdaptiveDesign.PVMGeometry
/-! A single orthonormal PVM spans exactly D real Hermitian directions,
as asserted in the reference-construction appendix. -/
namespace QubitOracle.AdaptiveDesign.PVMGeometry
open QubitOracle QubitOracle.Paper GlobalPFSIC GlobalPFSICHermitian GlobalPFSICBorn
open scoped BigOperators InnerProductSpace
noncomputable section
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency.types false

theorem coordinateEffects_orthonormal (d : ℕ) :
    Orthonormal ℝ (@coordinateEffect d) := by
  rw [orthonormal_iff_ite]
  intro j k
  rw [inner_eq_trace]
  change (Matrix.trace (projector (coordinate k)*projector (coordinate j))).re = _
  by_cases hjk : j=k
  · subst k
    simp [projector,coordinate,Matrix.trace,Matrix.diag,Matrix.mul_apply,
      Matrix.vecMulVec_apply,Pi.single_apply]
  · simp [projector,coordinate,Matrix.trace,Matrix.diag,Matrix.mul_apply,
      Matrix.vecMulVec_apply,Pi.single_apply,hjk,Ne.symm hjk]

theorem basisEffects_orthonormal {d : ℕ} (U : Action d) :
    Orthonormal ℝ (basisEffect U) := by
  rw [orthonormal_iff_ite]
  intro j k
  change ⟪conjugationIsometry U.matrix U.unitary (coordinateEffect j),
    conjugationIsometry U.matrix U.unitary (coordinateEffect k)⟫_ℝ = _
  rw [(conjugationIsometry U.matrix U.unitary).inner_map_map]
  exact orthonormal_iff_ite.mp (coordinateEffects_orthonormal d) j k

theorem single_pvm_span_dimension {d : ℕ} (U : Action d) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range (basisEffect U))) = d+1 := by
  simpa using finrank_span_eq_card (basisEffects_orthonormal U).linearIndependent

end
end QubitOracle.AdaptiveDesign.PVMGeometry
