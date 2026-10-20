-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMRealizedGram
import QubitOracle.AdaptiveDesign.PureAmplitudeLoss
import QubitOracle.Paper.CompactIdentifiedFiberInMeasure

/-! Uniform local excitation for the balanced projective pair. The
unidentified complement frame is handled by compactness; it need not
converge and is not an extra hypothesis on the controller. -/
namespace QubitOracle.AdaptiveDesign.PVMPilotGLS
open QubitOracle QubitOracle.Paper GlobalPFSIC GlobalPFSICHermitian GlobalPFSICBorn
open PureMatrixController P2Adaptive TangentGLS PVMGeometry PVMPilotBorn
open PVMUniformMoments Filter MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace Topology ComplexOrder Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
variable [PVMPilotSchedule.Schedule]
variable {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d]

def exploitationGram (U : Action d) : Operator d :=
  (1/2:ℝ) • basisGramOperator (PVMGeneralGeometry.exploitationChiAction U)+
  (1/2:ℝ) • basisGramOperator (PVMGeneralGeometry.exploitationTauAction U)

theorem basisGramOperator_quadratic (U : Action d) (A : HermitianSpace (d+1)) :
    ⟪A,basisGramOperator U A⟫_ℝ = ∑ k, ⟪basisEffect U k,A⟫_ℝ^2 := by
  simp only [basisGramOperator,gramCLM_apply,inner_sum,inner_smul_right,one_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [real_inner_comm A]
  ring

theorem meanGram_nonnegative (a : ℕ × Action d) (A : HermitianSpace (d+1)) :
    0 ≤ ⟪A,meanGram a A⟫_ℝ := by
  simp only [meanGram,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    inner_sum,inner_smul_right,basisGramOperator_quadratic]
  exact Finset.sum_nonneg (fun b _ => mul_nonneg (settingWeight_nonnegative _ _ _)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

theorem meanGram_exploitation_lower (a : ℕ × Action d) (A : HermitianSpace (d+1)) :
    (1-PVMPilotSchedule.epsilon a.1)*⟪A,exploitationGram a.2 A⟫_ℝ ≤ ⟪A,meanGram a A⟫_ℝ := by
  have he : 0 ≤ ∑ l : PVMGeneralGeometry.ExplorationIndex d,
      (PVMPilotSchedule.epsilon a.1/(Fintype.card (PVMGeneralGeometry.ExplorationIndex d):ℝ))*
        ⟪A,basisGramOperator (PVMGeneralGeometry.explorationBasis l) A⟫_ℝ := by
    apply Finset.sum_nonneg
    intro l _
    rw [basisGramOperator_quadratic]
    exact mul_nonneg (div_nonneg (PVMPilotSchedule.epsilon_nonnegative _) (Nat.cast_nonneg _))
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  simp only [meanGram,Fintype.sum_sum_type,Fintype.sum_bool,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,inner_add_right,inner_smul_right,
    inner_sum,settingWeight,settingBasis,exploitationGram] at *
  simp only [div_eq_mul_inv] at he
  nlinarith

theorem compress_exploitationGram (truth : PureVector d) (U : Action d) :
    compress truth (exploitationGram U) = informationLift truth
      (stageGram (PVMGeneralGeometry.exploitationFrame d) ((trueFrame d truth).conjTranspose*U.matrix)) := by
  rw [exploitationGram,map_add,map_smul,map_smul]
  change (1/2:ℝ) • compress truth (basisGramOperator (PVMGeneralGeometry.exploitationChiAction U))+
    (1/2:ℝ) • compress truth (basisGramOperator (PVMGeneralGeometry.exploitationTauAction U)) = _
  rw [show compress truth (basisGramOperator (PVMGeneralGeometry.exploitationChiAction U)) = _ from
    basis_projectedGram truth (PVMGeneralGeometry.exploitationChiAction U),
    show compress truth (basisGramOperator (PVMGeneralGeometry.exploitationTauAction U)) = _ from
    basis_projectedGram truth (PVMGeneralGeometry.exploitationTauAction U)]
  ext A
  simp only [stageGram,informationLift,map_add,map_smul,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_add,
    PVMGeneralGeometry.exploitationChiAction,PVMGeneralGeometry.exploitationTauAction,
    controllerChiBasis,controllerTauBasis,transportedChiBasis,transportedTauBasis,Matrix.mul_assoc]
  simp only [smul_smul,mul_comm (1/2:ℝ) (2:ℝ)]

def frameParameter (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) : HermitianSpace (d+1) :=
  ofMatrix (frameProjector U) (projector_posSemidef (fun i => U i 0)).isHermitian

theorem frameParameter_overlap (truth : PureVector d)
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    ⟪(pureParameter d truth).val,frameParameter U⟫_ℝ =
      controllerTrueOverlapSq ((trueFrame d truth).conjTranspose*U) := by
  let V := conjugationIsometry (trueFrame d truth) (trueFrame_unitary d truth)
  have he : (pureParameter d truth).val = V (pureParameter d (knownReference d)).val :=
    (trueFrame_referenceParameter truth).symm
  calc
    _ = ⟪V (pureParameter d (knownReference d)).val,V (V.symm (frameParameter U))⟫_ℝ := by
      rw [V.apply_symm_apply,← he]
    _ = (toMatrix (V.symm (frameParameter U)) 0 0).re := by rw [V.inner_map_map,reference_overlap]
    _ = _ := by
      change (((trueFrame d truth).conjTranspose*frameProjector U*
        (trueFrame d truth).conjTranspose.conjTranspose) 0 0).re = _
      rw [← frameProjector_mul,frameProjector_zero_entry]

theorem frameParameter_overlap_error (truth : PureVector d)
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    |controllerTrueOverlapSq ((trueFrame d truth).conjTranspose*U)-1| ≤
      ‖frameParameter U-(pureParameter d truth).val‖ := by
  have hh := norm_inner_le_norm (𝕜:=ℝ) (pureParameter d truth).val
    (frameParameter U-(pureParameter d truth).val)
  simpa only [inner_sub_right,frameParameter_overlap,real_inner_self_eq_norm_sq,
    pureParameter_norm,one_pow,one_mul,Real.norm_eq_abs] using hh

theorem local_exploitationGram (truth : PureVector d) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ U : Action d,
      ‖frameParameter U.matrix-(pureParameter d truth).val‖ < δ →
      ‖compress truth (exploitationGram U)-(1/(d+1:ℝ)) • tangentProjector truth‖ < 1/(2*(d+1:ℝ)) := by
  obtain ⟨δ,hδ,hlocal⟩ := compact_identified_fiber_uniform
    {U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ | U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ}
    isCompact_unitaryMatrices controllerTrueOverlapSq continuous_controllerTrueOverlapSq 1
    (fun U => informationLift truth (stageGram (PVMGeneralGeometry.exploitationFrame d) U))
    ((1/(d+1:ℝ)) • tangentProjector truth)
    (fun U hU he => ⟨((informationLift_continuous truth).comp
      (stageGram_continuous _)).continuousAt, by rw [stageGram_aligned _ U hU he,informationLift_gram_target]⟩)
    (1/(2*(d+1:ℝ))) (by positivity)
  refine ⟨δ,hδ,fun U hclose => ?_⟩
  rw [compress_exploitationGram]
  have hh := hlocal ((trueFrame d truth).conjTranspose*U.matrix)
    (relative_unitary _ _ (trueFrame_unitary d truth) U.unitary)
    ((show dist (controllerTrueOverlapSq ((trueFrame d truth).conjTranspose*U.matrix)) 1 ≤
      ‖frameParameter U.matrix-(pureParameter d truth).val‖ from by
        simpa only [Real.dist_eq] using frameParameter_overlap_error truth U.matrix).trans_lt hclose)
  simpa only [dist_eq_norm] using hh

end
end QubitOracle.AdaptiveDesign.PVMPilotGLS

-/
