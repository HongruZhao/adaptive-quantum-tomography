import QubitOracle.AdaptiveDesign.AdaptiveRidgeConsistency
import QubitOracle.AdaptiveDesign.CoerciveLeastSquares
import QubitOracle.AdaptiveDesign.GeneralPOVMAdaptive
import QubitOracle.AdaptiveDesign.GeneralPOVMModel
import QubitOracle.AdaptiveDesign.GeneralPOVMProbabilityLimits
import QubitOracle.AdaptiveDesign.GeneralPOVMTransport
import QubitOracle.AdaptiveDesign.GlobalPFSICBornModel
import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel
import QubitOracle.AdaptiveDesign.P2AdaptiveTheorem
import QubitOracle.AdaptiveDesign.ProtectedGLSWeightBounds
import QubitOracle.AdaptiveDesign.PureMatrixController
import QubitOracle.AdaptiveDesign.SequentialRidgeController
import QubitOracle.AdaptiveDesign.TangentGLSActualRates
import QubitOracle.AdaptiveDesign.TangentGLSAlgebra
import QubitOracle.AdaptiveDesign.TangentGLSAmbient
import QubitOracle.AdaptiveDesign.TangentGLSBounds
import QubitOracle.AdaptiveDesign.TangentGLSEstimator
import QubitOracle.AdaptiveDesign.TangentGLSGeometry
import QubitOracle.AdaptiveDesign.TangentGLSLinearization
import QubitOracle.AdaptiveDesign.TangentGLSNormalizedError
import QubitOracle.AdaptiveDesign.TangentGLSRecordBounds
import QubitOracle.AdaptiveDesign.TangentGLSRecordIdentities
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.AdaptiveTrajectoryExperiment
/-! Strong consistency of the actual all-record normalized GLS output.
The proof uses only identification and a positive denominator floor. It
does not infer almost-sure convergence from a central limit theorem and
does not treat data-fitted weights as predictable. -/
namespace QubitOracle.AdaptiveDesign.TangentGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive
open GeneralPOVM Filter MeasureTheory
open scoped BigOperators Topology InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

theorem protected_residual_lipschitz (τ p q z : ℝ) (hτ : 0 < τ)
    (hz : |z-p| ≤ 1) :
    |(denominator τ q)⁻¹*(z-q) - (denominator τ p)⁻¹*(z-p)| ≤
      (τ⁻¹+τ⁻¹^2)*|q-p| := by
  have he : (denominator τ q)⁻¹*(z-q) - (denominator τ p)⁻¹*(z-p) =
      ((denominator τ q)⁻¹-(denominator τ p)⁻¹)*(z-p) -
        (denominator τ q)⁻¹*(q-p) := by ring
  rw [he]
  have hw := protected_inverse_lipschitz τ p q hτ
  have hq : |(denominator τ q)⁻¹| ≤ τ⁻¹ := by
    rw [abs_of_pos (inv_pos.mpr (denominator_pos hτ q))]
    exact inv_anti₀ hτ (le_max_right _ _)
  calc
    _ ≤ |(denominator τ q)⁻¹-(denominator τ p)⁻¹| *|z-p| +
        |(denominator τ q)⁻¹| *|q-p| := by
      simpa only [Real.norm_eq_abs, abs_mul] using norm_sub_le
        (((denominator τ q)⁻¹-(denominator τ p)⁻¹)*(z-p))
        ((denominator τ q)⁻¹*(q-p))
    _ ≤ (|q-p|/τ^2)*1 + τ⁻¹*|q-p| :=
      add_le_add (mul_le_mul hw hz (abs_nonneg _) (by positivity))
        (mul_le_mul_of_nonneg_right hq (abs_nonneg _))
    _ = _ := by simp only [div_eq_mul_inv, inv_pow]; ring

variable {d n : ℕ} {O : Type} [Fintype O]

theorem record_fitted_score_difference_bound
    (h truth : PureVector d) (data : Fin n → Record d O) (τ C : ℝ)
    (hτ : 0 < τ) (hC : 0 ≤ C) (hb : ∀ r, ‖recordFeature data r‖ ≤ C) :
    ‖score (recordFeature data) (fun r => (denominator τ (fittedProbability h data r))⁻¹)
        (fittedResidual h data) -
      score (recordFeature data) (fun r => (denominator τ (fittedProbability truth data r))⁻¹)
        (fittedResidual truth data)‖ ≤
      (n : ℝ)*(Fintype.card O : ℝ)*(τ⁻¹+τ⁻¹^2)*C^2*
        ‖(pureParameter d h).val-(pureParameter d truth).val‖ := by
  rw [score, score, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ r : Fin n × O, (τ⁻¹+τ⁻¹^2)*C^2*
        ‖(pureParameter d h).val-(pureParameter d truth).val‖ := by
      apply Finset.sum_le_sum
      intro r _
      rw [← sub_smul, norm_smul, Real.norm_eq_abs]
      have h1 := protected_residual_lipschitz τ (fittedProbability truth data r)
        (fittedProbability h data r) (observedIndicator data r) hτ
        (record_noise_abs_le truth data r)
      have h2 := record_increment_bound h truth data r C (hb r)
      have h3 := mul_le_mul_of_nonneg_left h2
        (show 0 ≤ τ⁻¹+τ⁻¹^2 by positivity)
      have hh := mul_le_mul (h1.trans h3) (hb r) (norm_nonneg _) (by positivity)
      exact hh.trans_eq (by ring)
    _ = _ := by simp [Fintype.card_prod, Fintype.card_fin]; ring

variable [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]

theorem actual_ambientScore_average_zero
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P)
    (truth : PureVector d) (τ : ℝ) (hτ : 0 < τ)
    (regularization : ℝ) (hr : 0 < regularization) (batchSize : ℕ → ℕ) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth,
      Tendsto (fun n : ℕ => (n:ℝ)⁻¹ • actualScoreSum P hI truth τ regularization hr batchSize n path)
        atTop (𝓝 0) := by
  apply AdaptiveRidgeConsistency.actualVectorResponse_average_ae_tendsto_zero
    _ _ _ (ambientScoreResponse_mean P truth τ) (2*(τ⁻¹*responseBound P))
    (by have hb := responseBound_nonnegative P; positivity)
    (ambientScoreResponse_bound P truth τ hτ)

/-- A deterministic bound for the actual finite-record correction. -/
theorem actualDelta_norm_bound
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) (n : ℕ) (hn : 0 < n) (path : AdaptiveInfinitePath O) :
    ‖actualDelta P hI hp regularization ridge hr hη batchSize n path‖ ≤
      (‖(n:ℝ)⁻¹ • actualScoreSum P hI truth (referenceFloor P) regularization hr batchSize n path‖ +
        (Fintype.card O : ℝ)*((referenceFloor P)⁻¹+(referenceFloor P)⁻¹^2)*(responseBound P)^2*
          ‖actualPreliminaryError P hI regularization hr batchSize truth n path‖) /
        coercivityConstant P hI := by
  let h := actualPreliminary P hI regularization hr batchSize path n
  let data := actualRecords P hI regularization hr batchSize path n
  let τ := referenceFloor P
  let w := fun r => (denominator τ (fittedProbability h data r))⁻¹
  let s := score (recordFeature data) w (fittedResidual h data)
  let δ := recordCorrection h data τ ridge (referenceFloor_pos P hp) hη
  have hN : (0:ℝ)<n := by exact_mod_cast hn
  have hκ := coercivityConstant_pos P hI
  have he : normalMap (tangentFeature h data) w ridge δ =
      score (tangentFeature h data) w (fittedResidual h data) :=
    correction_normalEquation _ _ _ _ _ hη
  have hb := CoerciveLeastSquares.norm_le_residual_div _ _
    (show 0 < ridge+(n:ℝ)*coercivityConstant P hI by positivity)
    (actual_record_normalMap_coercive P hI hp regularization ridge hr batchSize path n h) δ _ he
  have hs : ‖score (tangentFeature h data) w (fittedResidual h data)‖ ≤ ‖s‖ := by
    change ‖(score (tangentFeature h data) w (fittedResidual h data)).val‖ ≤ _
    rw [score_tangent_val]
    exact ((tangentProjector h).le_opNorm s).trans
      (by simpa using mul_le_mul_of_nonneg_right (tangentProjector_norm_le h) (norm_nonneg s))
  have hfeature (r : Fin n × O) : ‖recordFeature data r‖ ≤ responseBound P := by
    dsimp [data]
    rw [actual_recordFeature_eq]
    exact responseVector_norm_le P _ _
  have hd := record_fitted_score_difference_bound h truth data τ (responseBound P)
    (referenceFloor_pos P hp) (responseBound_nonnegative P) hfeature
  have ht : score (recordFeature data)
      (fun r => (denominator τ (fittedProbability truth data r))⁻¹) (fittedResidual truth data) =
      actualScoreSum P hI truth τ regularization hr batchSize n path :=
    actual_score_eq_sum P hI truth τ regularization hr batchSize path n
  simp only [ht] at hd
  have hs' : ‖s‖ ≤
      (n:ℝ)*(Fintype.card O : ℝ)*(τ⁻¹+τ⁻¹^2)*(responseBound P)^2*
        ‖(pureParameter d h).val-(pureParameter d truth).val‖ +
      ‖actualScoreSum P hI truth τ regularization hr batchSize n path‖ := by
    calc
      _ ≤ ‖s-actualScoreSum P hI truth τ regularization hr batchSize n path‖ +
          ‖actualScoreSum P hI truth τ regularization hr batchSize n path‖ := norm_le_norm_sub_add _ _
      _ ≤ _ := by
        dsimp only [s, w]
        exact add_le_add hd le_rfl
  have hbound : ‖δ‖ ≤ (‖actualScoreSum P hI truth τ regularization hr batchSize n path‖ +
      (n:ℝ)*(Fintype.card O : ℝ)*(τ⁻¹+τ⁻¹^2)*(responseBound P)^2*
        ‖actualPreliminaryError P hI regularization hr batchSize truth n path‖) /
      ((n:ℝ)*coercivityConstant P hI) := by
    have hden : (n:ℝ)*coercivityConstant P hI ≤ ridge+(n:ℝ)*coercivityConstant P hI := by linarith
    have hb' := hb.trans (div_le_div_of_nonneg_left
      (norm_nonneg _) (mul_pos hN hκ) hden)
    apply hb'.trans
    apply div_le_div_of_nonneg_right (hs.trans ?_) (mul_pos hN hκ).le
    simpa only [add_comm, actualPreliminaryError, h] using hs'

  change ‖δ‖ ≤ _
  apply hbound.trans_eq
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hN)]
  dsimp only [τ]
  field_simp [ne_of_gt hN, ne_of_gt hκ]
  <;> ring

theorem actualDelta_stronglyConsistent
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth,
      Tendsto (fun n => actualDelta P hI hp regularization ridge hr hη batchSize n path)
        atTop (𝓝 0) := by
  filter_upwards [actualPreliminaryError_consistent P hI regularization hr batchSize truth,
    actual_ambientScore_average_zero P hI truth (referenceFloor P) (referenceFloor_pos P hp)
      regularization hr batchSize] with path he hs
  have hu := (hs.norm.add (he.norm.const_mul ((Fintype.card O : ℝ)*
    ((referenceFloor P)⁻¹+(referenceFloor P)⁻¹^2)*(responseBound P)^2))).div_const
      (coercivityConstant P hI)
  simp only [norm_zero, mul_zero, add_zero, zero_div] at hu
  apply squeeze_zero_norm' _ hu
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact actualDelta_norm_bound P hI hp truth regularization ridge hr hη batchSize n hn path

/-- The actual physical output is strongly consistent. Fisher symmetry
and a batch-growth condition are not needed for this assertion. -/
theorem corrected_stronglyConsistent
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth,
      Tendsto (fun n => (pureParameter d
        (actualEstimate P hI hp regularization ridge hr hη batchSize path n)).val)
        atTop (𝓝 (pureParameter d truth).val) := by
  filter_upwards [actualPreliminaryError_consistent P hI regularization hr batchSize truth,
    actualDelta_stronglyConsistent P hI hp truth regularization ridge hr hη batchSize] with path he hd
  have hrem : Tendsto (fun n => actualProjectorError P hI hp truth regularization ridge hr hη batchSize n path -
      (actualPreliminaryError P hI regularization hr batchSize truth n path +
        actualDelta P hI hp regularization ridge hr hη batchSize n path)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => actual_retraction_error_bound P hI hp truth
      regularization ridge hr hη batchSize n path)
    simpa using (hd.norm.pow 2).const_mul 3
  apply tendsto_sub_nhds_zero_iff.mp
  simpa only [sub_add_cancel, zero_add, actualProjectorError] using hrem.add (he.add hd)

end
end QubitOracle.AdaptiveDesign.TangentGLS
