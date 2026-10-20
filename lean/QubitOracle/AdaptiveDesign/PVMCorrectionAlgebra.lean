-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMRealizedGram

/-! Deterministic perturbation bounds for the literal tangent LS correction. -/
namespace QubitOracle.AdaptiveDesign.PVMPilotGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive TangentGLS
open Filter MeasureTheory ProbabilityCalculus
open scoped BigOperators InnerProductSpace Topology
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
variable [PVMPilotSchedule.Schedule]
variable {d n : ℕ} [PVMGeneralGeometry.ExplorationLibrary d]

lemma perturbation_norm_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E) (hB : ‖B‖ ≤ 1/2) (x : E) : ‖x‖ ≤ 2*‖x+B x‖ := by
  have h := norm_sub_le (x+B x) (B x)
  rw [add_sub_cancel_right] at h
  have hb := B.le_opNorm x
  have hc := mul_le_mul_of_nonneg_right hB (norm_nonneg x)
  linarith

def recordOperator {O : Type} [Fintype O] (h : PureVector d)
    (data : Fin n → Record d O) (ridge : ℝ) : Operator d :=
  ridge • tangentProjector h + recordInformation h data (floor d)

def recordOperatorError {O : Type} [Fintype O] (h : PureVector d)
    (data : Fin n → Record d O) (ridge : ℝ) : Operator d :=
  ((d+1:ℝ)/(n:ℝ)) • recordOperator h data ridge - tangentProjector h

lemma recordOperator_tangent {O : Type} [Fintype O] (h : PureVector d)
    (data : Fin n → Record d O) (ridge : ℝ) (x : tangentSpace h) :
    recordOperator h data ridge x.val =
      (normalMap (tangentFeature h data) (fun _ => 1) ridge x).val := by
  have hh := record_normalMap_val h data (floor d) ridge x
  simp only [unit_weight] at hh
  rw [hh]
  simp only [recordOperator,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    tangentProjector_self]

lemma recordOperator_projection {O : Type} [Fintype O] (h : PureVector d)
    (data : Fin n → Record d O) (ridge : ℝ) (x : HermitianSpace (d+1)) :
    recordOperator h data ridge (tangentProjector h x) = recordOperator h data ridge x := by
  simp only [recordOperator,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    tangentProjector_idem,recordInformation_projection]

def tangentError (h truth : PureVector d) : HermitianSpace (d+1) :=
  (preliminaryTangentError h truth).val

def normalRemainder {O : Type} [Fintype O] (h truth : PureVector d)
    (data : Fin n → Record d O) (ridge : ℝ) : HermitianSpace (d+1) :=
  -(score (tangentFeature h data) (fun _ => 1) (curvature h truth data)).val +
    ridge • tangentError h truth

lemma normalRemainder_bound {O : Type} [Fintype O] (h truth : PureVector d)
    (data : Fin n → Record d O) (ridge C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ r, ‖recordFeature data r‖ ≤ C) :
    ‖normalRemainder h truth data ridge‖ ≤
      3*(n:ℝ)*(Fintype.card O:ℝ)*C^2*
        ‖(pureParameter d h).val-(pureParameter d truth).val‖^2 + 2*|ridge| := by
  apply (norm_add_le _ _).trans
  rw [norm_neg,norm_smul,Real.norm_eq_abs]
  have hh := curvature_score_bound h truth data C hC hb
  have ha : ‖tangentError h truth‖ ≤ 2 :=
    (preliminaryTangentError_norm_le h truth).trans (preliminaryError_norm_le_two h truth)
  have hr := mul_le_mul_of_nonneg_left ha (abs_nonneg ridge)
  change ‖(score (tangentFeature h data) (fun _ => 1) (curvature h truth data)).val‖ ≤ _ at hh
  linarith

lemma scoreSum_records (truth : PureVector d) (batchSize : ℕ → ℕ)
    (path : AdaptiveInfinitePath (PVMPilotAdaptive.PVMOutcome d)) (n : ℕ) :
    scoreSum truth batchSize n path =
      score (recordFeature (actualRecords batchSize path n)) (fun _ => 1)
        (fun r => observedIndicator (actualRecords batchSize path n) r-
          fittedProbability truth (actualRecords batchSize path n) r) := by
  symm
  simpa only [unit_weight] using score_eq_sum truth batchSize path n

lemma actual_normal_equation (truth : PureVector d) (ridge : ℝ) (hr : 0 < ridge)
    (batchSize : ℕ → ℕ) (n : ℕ) (path : AdaptiveInfinitePath (PVMPilotAdaptive.PVMOutcome d)) :
    recordOperator (actualPreliminary batchSize path n) (actualRecords batchSize path n) ridge
      ((actualDelta ridge hr batchSize path n).val + tangentError (actualPreliminary batchSize path n) truth) =
    tangentProjector (actualPreliminary batchSize path n) (scoreSum truth batchSize n path) +
      normalRemainder (actualPreliminary batchSize path n) truth (actualRecords batchSize path n) ridge := by
  let h := actualPreliminary batchSize path n
  let data := actualRecords batchSize path n
  have hh := congrArg Subtype.val (one_step_error_equation h truth data ridge hr)
  rw [← recordOperator_tangent] at hh
  rw [scoreSum_records]
  simpa only [h,data,actualDelta,Submodule.coe_add,Submodule.coe_sub,Submodule.coe_neg,
    Submodule.coe_smul,score_tangent_val,normalRemainder,tangentError,sub_eq_add_neg,add_assoc] using hh

/-- Purely algebraic root-n cancellation in the ambient Hermitian space. -/
lemma scaled_ambient_equation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B Q : E →L[ℝ] E) (u s r : E) (N c : ℝ) (hN : 0 < N)
    (hu : Q u=u) (hs : Q s=s) (he : B u=s+r) :
    let A := (c/N) • B-Q
    let x := Real.sqrt N • u-(c/Real.sqrt N) • s
    x+A x = (c/Real.sqrt N) • r-A ((c/Real.sqrt N) • s) := by
  have hh := scaled_error_equation (c • B.toLinearMap) u (c • s) (c • r) N hN
    (by change c • B u = c • s+c • r; rw [he,smul_add])
  dsimp only
  have hxs : Q (Real.sqrt N • u-(c/Real.sqrt N) • s) =
      Real.sqrt N • u-(c/Real.sqrt N) • s := by rw [map_sub,map_smul,map_smul,hu,hs]
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,hxs]
  simp only [LinearMap.smul_apply,ContinuousLinearMap.coe_coe,smul_smul] at hh
  have hc : N⁻¹*c=c/N := by ring
  have hc' : (Real.sqrt N)⁻¹*c=c/Real.sqrt N := by ring
  rw [hc,hc'] at hh
  simp only [map_smul,hs] at hh ⊢
  convert hh using 1 <;> module

end
end QubitOracle.AdaptiveDesign.PVMPilotGLS

-/
