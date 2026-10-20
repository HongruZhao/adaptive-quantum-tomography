-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMCorrectionLimits

namespace QubitOracle.AdaptiveDesign.PVMPilotGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive TangentGLS
open Filter MeasureTheory
open scoped BigOperators InnerProductSpace Topology
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
variable [PVMPilotSchedule.Schedule]
variable {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d]

lemma scoreSum_average_zero (truth : PureVector d) (batchSize : ℕ → ℕ) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth),
      Tendsto (fun n : ℕ => (n:ℝ)⁻¹ • scoreSum truth batchSize n path) atTop (𝓝 0) := by
  apply AdaptiveRidgeConsistency.actualVectorResponse_average_ae_tendsto_zero
    _ _ _ (scoreResponse_mean truth) (2*((floor d)⁻¹*PVMGeometry.basisBound d)) _ (scoreResponse_bound truth)
  have hb := PVMGeometry.basisBound_nonnegative d
  have hf := floor_pos d
  positivity

lemma normalRemainder_average_zero (truth : PureVector d) (ridge : ℝ) (batchSize : ℕ → ℕ)
    (path : AdaptiveInfinitePath (PVMPilotAdaptive.PVMOutcome d))
    (he : Tendsto (fun n => actualPreliminaryError batchSize truth n path) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n:ℝ)⁻¹ • normalRemainder (actualPreliminary batchSize path n) truth
      (actualRecords batchSize path n) ridge) atTop (𝓝 0) := by
  let C := 3*(d+1:ℝ)*(PVMGeometry.basisBound d)^2
  have hupper : Tendsto (fun n : ℕ => C*‖actualPreliminaryError batchSize truth n path‖^2+
      (2*|ridge|)/(n:ℝ)) atTop (𝓝 0) := by
    have hh := (he.norm.pow 2).const_mul C
    simpa using hh.add (show Tendsto (fun n : ℕ => (2*|ridge|)/(n:ℝ)) atTop (𝓝 0) from
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
  apply squeeze_zero_norm' _ hupper
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn')]
  have hb := mul_le_mul_of_nonneg_left (normalRemainder_bound (actualPreliminary batchSize path n) truth
    (actualRecords batchSize path n) ridge (PVMGeometry.basisBound d) (PVMGeometry.basisBound_nonnegative d)
    (fun r => by rw [recordFeature_eq]; exact PVMGeometry.basisEffect_bound _ _)) (inv_pos.mpr hn').le
  apply hb.trans_eq
  simp only [Fintype.card_fin,actualPreliminaryError]
  dsimp [C]
  simp only [Nat.cast_add,Nat.cast_one]
  field_simp
  <;> ring

lemma correctedDelta_consistent (truth : PureVector d) (ridge : ℝ) (hr : 0 < ridge)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth),
      Tendsto (fun n => (actualDelta ridge hr batchSize path n).val) atTop (𝓝 0) := by
  filter_upwards [actualPreliminaryError_consistent batchSize truth,operatorError_limit truth ridge batchSize hpositive,
    scoreSum_average_zero truth batchSize] with path he hB hs
  let u := fun n => (actualDelta ridge hr batchSize path n).val+tangentError (actualPreliminary batchSize path n) truth
  have hrm := normalRemainder_average_zero truth ridge batchSize path he
  have hp : Tendsto (fun n : ℕ => (n:ℝ)⁻¹ • tangentProjector (actualPreliminary batchSize path n)
      (scoreSum truth batchSize n path)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) (by simpa only [norm_zero] using hs.norm)
    rw [← map_smul]
    exact ((tangentProjector _).le_opNorm _).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (tangentProjector_norm_le _) (norm_nonneg _))
  have hright : Tendsto (fun n : ℕ => ((d+1:ℝ)/(n:ℝ)) •
      (tangentProjector (actualPreliminary batchSize path n) (scoreSum truth batchSize n path)+
        normalRemainder (actualPreliminary batchSize path n) truth (actualRecords batchSize path n) ridge))
      atTop (𝓝 0) := by
    simpa only [smul_add,smul_smul,div_eq_mul_inv,smul_zero,zero_add] using (hp.add hrm).const_smul (d+1:ℝ)
  have hu : Tendsto u atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (by simpa using hright.norm.const_mul 2)
    have hev := hB.norm.eventually (gt_mem_nhds (show ‖(0:Operator d)‖<1/2 by norm_num))
    filter_upwards [hev] with n hn
    have hb := perturbation_norm_bound _ hn.le (u n)
    have hqu : tangentProjector (actualPreliminary batchSize path n) (u n)=u n :=
      tangentProjector_self _ (actualDelta ridge hr batchSize path n+
        preliminaryTangentError (actualPreliminary batchSize path n) truth)
    have heq : u n+recordOperatorError (actualPreliminary batchSize path n) (actualRecords batchSize path n) ridge (u n) =
        ((d+1:ℝ)/(n:ℝ)) • (tangentProjector (actualPreliminary batchSize path n) (scoreSum truth batchSize n path)+
          normalRemainder (actualPreliminary batchSize path n) truth (actualRecords batchSize path n) ridge) := by
      simp only [recordOperatorError,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,hqu]
      rw [show recordOperator (actualPreliminary batchSize path n) (actualRecords batchSize path n) ridge (u n) = _ from
        actual_normal_equation truth ridge hr batchSize n path]
      abel
    rw [heq] at hb
    simpa only [smul_add] using hb
  have ha : Tendsto (fun n => tangentError (actualPreliminary batchSize path n) truth) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => preliminaryTangentError_norm_le _ truth) (by simpa only [actualPreliminaryError,norm_zero] using he.norm)
  simpa only [u,add_sub_cancel_right,sub_zero] using hu.sub ha

/-- Strong consistency of the actual normalized correction needs only
infinite exploration, not the stronger efficiency budget. -/
theorem corrected_consistent (truth : PureVector d) (ridge : ℝ) (hr : 0 < ridge)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth),
      Tendsto (fun n => (pureParameter d (actualEstimate ridge hr batchSize path n)).val)
        atTop (𝓝 (pureParameter d truth).val) := by
  filter_upwards [actualPreliminaryError_consistent batchSize truth,
    correctedDelta_consistent truth ridge hr batchSize hpositive] with path he hd
  have hrem : Tendsto (fun n => (pureParameter d (actualEstimate ridge hr batchSize path n)).val-
      (pureParameter d truth).val-(actualPreliminaryError batchSize truth n path+(actualDelta ridge hr batchSize path n).val))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => updated_error_bound (actualPreliminary batchSize path n) truth
      (actualRecords batchSize path n) ridge hr)
    have hnorm n : ‖(actualDelta ridge hr batchSize path n).val‖ =
        ‖recordCorrection (actualPreliminary batchSize path n) (actualRecords batchSize path n) (floor d) ridge (floor_pos d) hr‖ := rfl
    simpa only [hnorm,norm_zero,zero_pow (by omega : 2 ≠ 0),mul_zero] using (hd.norm.pow 2).const_mul 3
  apply tendsto_sub_nhds_zero_iff.mp
  simpa only [sub_add_cancel,zero_add] using hrem.add (he.add hd)

end
end QubitOracle.AdaptiveDesign.PVMPilotGLS

-/
