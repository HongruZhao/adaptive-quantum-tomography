import QubitOracle.AdaptiveDesign.TangentGLSFittedInformation
import QubitOracle.AdaptiveDesign.TangentGLSStochasticRemainder

/-! Exact bridges from the literal finite-record solve to predictable
fixed-truth responses. No sample split or predictable fitted weights. -/
namespace QubitOracle.AdaptiveDesign.TangentGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive
open GeneralPOVM Filter MeasureTheory
open scoped BigOperators Topology InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {d n : ℕ} {O : Type} [Fintype O]

theorem recordCorrection_error_equation (h truth : PureVector d) (data : Fin n → Record d O)
    (floor ridge : ℝ) (hf : 0 < floor) (hr : 0 < ridge) :
    normalMap (tangentFeature h data) (fun r => (denominator floor (fittedProbability h data r))⁻¹) ridge
      (recordCorrection h data floor ridge hf hr + preliminaryTangentError h truth) =
    score (tangentFeature h data) (fun r => (denominator floor (fittedProbability truth data r))⁻¹)
      (fun r => observedIndicator data r - fittedProbability truth data r) +
    (noiseDerivative (tangentFeature h data) (fittedProbability truth data) (observedIndicator data) floor
      (preliminaryTangentError h truth) +
    fittedWeightRemainder (tangentFeature h data) (fittedProbability truth data)
      (fittedProbability h data) (observedIndicator data) floor (preliminaryTangentError h truth) +
    ridge • preliminaryTangentError h truth) := by
  rw [map_add]
  change normalMap _ _ ridge (fittedCorrection _ _ _ floor ridge hf hr) + _ = _
  rw [fittedCorrection, correction_normalEquation]
  rw [show fittedResidual h data = fun r => observedIndicator data r - fittedProbability h data r by rfl,
    fittedScore_exact_expansion _ _ _ _ floor hf, normalMap_apply]
  abel

theorem tangentProjector_self (h : PureVector d) (x : tangentSpace h) : tangentProjector h x.val = x.val :=
  Submodule.starProjection_eq_self_iff.mpr x.property

theorem record_normalMap_val (h : PureVector d) (data : Fin n → Record d O)
    (floor ridge : ℝ) (x : tangentSpace h) :
    (normalMap (tangentFeature h data)
      (fun r => (denominator floor (fittedProbability h data r))⁻¹) ridge x).val =
      ridge • x.val + recordInformation h data floor x.val := by
  simp only [normalMap_apply, Submodule.coe_add, Submodule.coe_smul, gram_tangent_val,
    recordInformation, ContinuousLinearMap.comp_apply, tangentProjector_self]

variable [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]

def actualScoreSum (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P)
    (truth : PureVector d) (floor regularization : ℝ) (hr : 0 < regularization)
    (batchSize : ℕ → ℕ) (n : ℕ) (path : AdaptiveInfinitePath O) : HermitianSpace (d+1) :=
  ∑ k ∈ Finset.range n, AdaptiveRidgeConsistency.actualVectorResponse
    (adaptiveProtocol P hI regularization hr batchSize) (ambientScoreResponse P truth floor) k path

def actualDerivativeSum (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P)
    (truth : PureVector d) (floor regularization : ℝ) (hr : 0 < regularization)
    (batchSize : ℕ → ℕ) (n : ℕ) (path : AdaptiveInfinitePath O) :
    HermitianSpace (d+1) →L[ℝ] HermitianSpace (d+1) :=
  ∑ k ∈ Finset.range n, AdaptiveRidgeConsistency.actualVectorResponse
    (adaptiveProtocol P hI regularization hr batchSize) (ambientDerivativeResponse P truth floor) k path

theorem actual_score_eq_sum
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P)
    (truth : PureVector d) (floor regularization : ℝ) (hr : 0 < regularization)
    (batchSize : ℕ → ℕ) (path : AdaptiveInfinitePath O) (n : ℕ) :
    score (recordFeature (actualRecords P hI regularization hr batchSize path n))
      (fun r => (denominator floor (fittedProbability truth
        (actualRecords P hI regularization hr batchSize path n) r))⁻¹)
      (fun r => observedIndicator (actualRecords P hI regularization hr batchSize path n) r -
        fittedProbability truth (actualRecords P hI regularization hr batchSize path n) r) =
      actualScoreSum P hI truth floor regularization hr batchSize n path := by
  classical
  rw [actualScoreSum, ← Fin.sum_univ_eq_sum_range]
  simp only [score, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro t _
  change _ = ambientScoreResponse P truth floor (actualState P hI regularization hr batchSize path t).action (path t)
  rw [ambientScoreResponse, centeredLookup_eq_residual_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [actual_recordFeature_eq, actual_fittedProbability_eq]
  simp only [observedIndicator, actualRecords, smul_smul]
  congr 1
  ring

theorem actual_derivative_eq_sum
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P)
    (truth : PureVector d) (floor regularization : ℝ) (hr : 0 < regularization)
    (batchSize : ℕ → ℕ) (path : AdaptiveInfinitePath O) (n : ℕ) (h : PureVector d) (x : tangentSpace h) :
    (noiseDerivative (tangentFeature h (actualRecords P hI regularization hr batchSize path n))
      (fittedProbability truth (actualRecords P hI regularization hr batchSize path n))
      (observedIndicator (actualRecords P hI regularization hr batchSize path n)) floor x).val =
    tangentProjector h (actualDerivativeSum P hI truth floor regularization hr batchSize n path x.val) := by
  classical
  simp only [noiseDerivative, LinearMap.neg_apply, Submodule.coe_neg, gram_tangent_val, ← map_neg]
  congr 1
  rw [actualDerivativeSum, ← Fin.sum_univ_eq_sum_range]
  simp only [gramCLM_apply, Fintype.sum_prod_type, ← Finset.sum_neg_distrib, ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro t _
  change _ = ambientDerivativeResponse P truth floor
    (actualState P hI regularization hr batchSize path t).action (path t) x.val
  rw [ambientDerivativeResponse, centeredLookup_eq_residual_sum]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro y _
  rw [actual_recordFeature_eq, actual_fittedProbability_eq]
  simp only [observedIndicator, actualRecords, ContinuousLinearMap.smul_apply, rankOneCLM_apply,
    smul_smul, ← neg_smul, inner_neg_right]
  congr 1
  ring

theorem actual_record_normalMap_coercive
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P)
    (regularization ridge : ℝ) (hr : 0 < regularization) (batchSize : ℕ → ℕ)
    (path : AdaptiveInfinitePath O) (n : ℕ) (h : PureVector d) :
    CoerciveLeastSquares.Coercive
      (normalMap (tangentFeature h (actualRecords P hI regularization hr batchSize path n))
        (fun r => (denominator (referenceFloor P) (fittedProbability h
          (actualRecords P hI regularization hr batchSize path n) r))⁻¹) ridge)
      (ridge + (n : ℝ)*coercivityConstant P hI) := by
  apply record_normalMap_coercive h _ _ ridge _ (referenceFloor_pos P hp) (referenceFloor_le_one P hp)
  intro t x
  have hh := regressionFrame_coercive P hI (actualState P hI regularization hr batchSize path t).action x
  simpa only [regressionFrame, FiniteFrameCoercivity.frameOperator_quadratic, actual_recordFeature_eq] using hh

end
end QubitOracle.AdaptiveDesign.TangentGLS
