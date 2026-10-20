import QubitOracle.AdaptiveDesign.PhasePairFrameBound

namespace QubitOracle.AdaptiveDesign.PhasePair
open QubitOracle QubitOracle.Paper GeneralPOVM GlobalPFSICHermitian FiniteFrameCoercivity
open scoped BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

theorem frameOperator_transport {E F O : Type*} [Fintype O]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (U : E ≃ₗᵢ[ℝ] F) (v : O → E) (A : F) :
    frameOperator (fun o => U (v o)) A = U (frameOperator v (U.symm A)) := by
  simp only [frameOperator_apply,transported_measurement,map_sum,map_smul]

theorem paired_frame_identity {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (A : HermitianSpace (d+1)) :
    frameOperator (effectVector (paired P)) A =
      (1/4:ℝ) • ∑ b : Bool,
        conjugationIsometry (branch d b) (branch_unitary d b)
          (frameOperator (effectVector P)
            ((conjugationIsometry (branch d b) (branch_unitary d b)).symm A)) := by
  simp only [frameOperator_apply,Fintype.sum_prod_type,paired_effectVector,
    real_inner_smul_left,transported_measurement,map_sum,map_smul,smul_smul,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro o _
  congr 1
  ring

end
end QubitOracle.AdaptiveDesign.PhasePair
