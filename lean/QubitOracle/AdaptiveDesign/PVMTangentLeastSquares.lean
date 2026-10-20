-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMPilotResponse
import QubitOracle.AdaptiveDesign.PVMPilotMeasurability
import QubitOracle.AdaptiveDesign.TangentGLSLinearization

/-! For the balanced PVM pair the efficient correction can use ordinary
least squares on the pure-state tangent space. All weights are exactly one.
The normal equation cancels the first-order preliminary error algebraically. -/
namespace QubitOracle.AdaptiveDesign.PVMPilotGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive TangentGLS
open Filter MeasureTheory ProbabilityCalculus
open scoped BigOperators InnerProductSpace Topology Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
variable [PVMPilotSchedule.Schedule]
variable {d n : ℕ} [PVMGeneralGeometry.ExplorationLibrary d]

lemma unit_weight {O : Type} [Fintype O] (h : PureVector d) (data : Fin n → Record d O)
    (r : Fin n × O) : (denominator (floor d) (fittedProbability h data r))⁻¹=1 := by
  rw [floor, denominator, max_eq_right (fittedProbability_le_one h data r), inv_one]

/-- Literal equality with the ordinary (unweighted) tangent LS solve. -/
lemma correction_is_unweighted {O : Type} [Fintype O] (h : PureVector d)
    (data : Fin n → Record d O) (ridge : ℝ) (hr : 0 < ridge) :
    recordCorrection h data (floor d) ridge (floor_pos d) hr =
      correction (tangentFeature h data) (fun _ => 1) (fittedResidual h data)
        (fun _ => zero_le_one) ridge hr := by
  unfold recordCorrection fittedCorrection
  simp only [unit_weight]

lemma unweighted_normalEquation {O : Type} [Fintype O] (h : PureVector d)
    (data : Fin n → Record d O) (ridge : ℝ) (hr : 0 < ridge) :
    normalMap (tangentFeature h data) (fun _ => 1) ridge
      (recordCorrection h data (floor d) ridge (floor_pos d) hr) =
      score (tangentFeature h data) (fun _ => 1) (fittedResidual h data) := by
  rw [correction_is_unweighted]
  exact correction_normalEquation _ _ _ _ _ hr

def curvature {O : Type} [Fintype O] (h truth : PureVector d)
    (data : Fin n → Record d O) (r : Fin n × O) : ℝ :=
  fittedProbability h data r-fittedProbability truth data r-
    ⟪tangentFeature h data r,preliminaryTangentError h truth⟫_ℝ

/-- Exact cancellation; the remainder is quadratic pure-state curvature.
There are no estimated inverse weights and no fitted-weight martingales. -/
theorem one_step_error_equation {O : Type} [Fintype O] (h truth : PureVector d)
    (data : Fin n → Record d O) (ridge : ℝ) (hr : 0 < ridge) :
    normalMap (tangentFeature h data) (fun _ => 1) ridge
      (recordCorrection h data (floor d) ridge (floor_pos d) hr + preliminaryTangentError h truth) =
      score (tangentFeature h data) (fun _ => 1)
        (fun r => observedIndicator data r-fittedProbability truth data r) -
      score (tangentFeature h data) (fun _ => 1) (curvature h truth data) +
      ridge • preliminaryTangentError h truth := by
  rw [map_add, unweighted_normalEquation, normalMap_apply]
  simp only [score, gram_apply, one_mul, ← Finset.sum_sub_distrib, ← sub_smul]
  rw [add_comm (ridge • preliminaryTangentError h truth), ← add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  simp only [← add_smul, fittedResidual, curvature]
  congr 1
  ring

lemma curvature_score_bound {O : Type} [Fintype O] (h truth : PureVector d)
    (data : Fin n → Record d O) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ r, ‖recordFeature data r‖ ≤ C) :
    ‖score (tangentFeature h data) (fun _ => 1) (curvature h truth data)‖ ≤
      3*(n:ℝ)*(Fintype.card O:ℝ)*C^2*
        ‖(pureParameter d h).val-(pureParameter d truth).val‖^2 := by
  have hh (r : Fin n × O) : ‖(curvature h truth data r) • tangentFeature h data r‖ ≤
      3*C^2*‖(pureParameter d h).val-(pureParameter d truth).val‖^2 := by
    rw [norm_smul, Real.norm_eq_abs]
    have ha := record_curvature_bound h truth data r C (hb r)
    have hf := (tangentFeature_norm_le h data r).trans (hb r)
    calc
      _ ≤ (3*C*‖(pureParameter d h).val-(pureParameter d truth).val‖^2)*C :=
        mul_le_mul ha hf (norm_nonneg _) (by positivity)
      _ = _ := by ring
  unfold score
  simp only [one_mul]
  apply (norm_sum_le _ _).trans
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun r _ => hh r)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hs

/-- Retraction into the pure-state manifold introduces only a quadratic error. -/
theorem updated_error_bound {O : Type} [Fintype O] (h truth : PureVector d)
    (data : Fin n → Record d O) (ridge : ℝ) (hr : 0 < ridge) :
    ‖(pureParameter d (updatedPureVector h (recordCorrection h data (floor d) ridge (floor_pos d) hr))).val-
      (pureParameter d truth).val-
      ((pureParameter d h).val-(pureParameter d truth).val+
        (recordCorrection h data (floor d) ridge (floor_pos d) hr).val)‖ ≤
      3*‖recordCorrection h data (floor d) ridge (floor_pos d) hr‖^2 := by
  let A := recordCorrection h data (floor d) ridge (floor_pos d) hr
  rw [← toMatrix_norm]
  change ‖(updatedState h A-rankOneDensity truth.val)-
    ((rankOneDensity h.val-rankOneDensity truth.val)+toMatrix A.val)‖ ≤ 3*‖A‖^2
  have he : (updatedState h A-rankOneDensity truth.val)-
      ((rankOneDensity h.val-rankOneDensity truth.val)+toMatrix A.val) =
      updatedState h A-(rankOneDensity h.val+toMatrix A.val) := by abel
  rw [he]
  exact updatedState_remainder_bound_global h A

end
end QubitOracle.AdaptiveDesign.PVMPilotGLS

-/
