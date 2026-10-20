import QubitOracle.AdaptiveDesign.CoerciveLeastSquares
import QubitOracle.AdaptiveDesign.GeneralPOVMAdaptive
import QubitOracle.AdaptiveDesign.GeneralPOVMModel
import QubitOracle.AdaptiveDesign.GeneralPOVMTransport
import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel
import QubitOracle.AdaptiveDesign.PureMatrixController
import QubitOracle.AdaptiveDesign.TangentGLSActualRates
import QubitOracle.AdaptiveDesign.TangentGLSAlgebra
import QubitOracle.AdaptiveDesign.TangentGLSAmbient
import QubitOracle.AdaptiveDesign.TangentGLSBounds
import QubitOracle.AdaptiveDesign.TangentGLSEstimator
import QubitOracle.AdaptiveDesign.TangentGLSFittedInformation
import QubitOracle.AdaptiveDesign.TangentGLSGeometry
import QubitOracle.AdaptiveDesign.TangentGLSOperatorBounds
import QubitOracle.AdaptiveDesign.TangentGLSRecordIdentities
import QubitOracle.AdaptiveDesign.TangentGLSStochasticRemainder
import QubitOracle.AdaptiveDesign.TangentGLSWeightExpansion
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.AdaptiveTrajectoryExperiment
/-! Linearization of the actual all-record correction. The coercive normal
equation turns the proved score and weight remainders into an estimator
remainder, rather than assuming that the solve is asymptotically efficient. -/
namespace QubitOracle.AdaptiveDesign.TangentGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive
open GeneralPOVM Filter MeasureTheory ProbabilityCalculus
open scoped BigOperators Topology InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

theorem inv_mul_sqrt (N : ℝ) (hN : 0 < N) : N⁻¹*Real.sqrt N = (Real.sqrt N)⁻¹ := by
  have hs := Real.sq_sqrt hN.le
  have hp := (Real.sqrt_pos.mpr hN).ne'
  apply mul_right_cancel₀ hp
  rw [inv_mul_cancel₀ hp]
  calc
    _ = N⁻¹*(Real.sqrt N)^2 := by ring
    _ = 1 := by rw [hs, inv_mul_cancel₀ hN.ne']

theorem normalized_coercive {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : E →ₗ[ℝ] E) (N ridge κ : ℝ) (hN : 0 < N) (hr : 0 ≤ ridge)
    (hA : CoerciveLeastSquares.Coercive A (ridge+N*κ)) :
    CoerciveLeastSquares.Coercive (N⁻¹ • A) κ := by
  intro x
  simp only [LinearMap.smul_apply, inner_smul_right]
  have h := hA x
  have hh : N*(κ*‖x‖^2) ≤ ⟪x,A x⟫_ℝ := by nlinarith [mul_nonneg hr (sq_nonneg ‖x‖)]
  calc
    κ*‖x‖^2 = N⁻¹*(N*(κ*‖x‖^2)) := by rw [← mul_assoc, inv_mul_cancel₀ hN.ne', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (inv_pos.mpr hN).le

theorem scaled_error_equation {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : E →ₗ[ℝ] E) (u s r : E) (N : ℝ) (hN : 0 < N) (he : A u=s+r) :
    (N⁻¹ • A) (Real.sqrt N • u - (Real.sqrt N)⁻¹ • s) =
      (Real.sqrt N)⁻¹ • r - ((N⁻¹ • A) ((Real.sqrt N)⁻¹ • s) - (Real.sqrt N)⁻¹ • s) := by
  simp only [map_sub, map_smul, LinearMap.smul_apply, smul_sub, smul_smul, he,
    show Real.sqrt N * N⁻¹ = (Real.sqrt N)⁻¹ from (mul_comm _ _).trans (inv_mul_sqrt N hN), smul_add]
  abel

variable {d n : ℕ} {O : Type} [Fintype O]

theorem tangentProjector_idem (h : PureVector d) (x : HermitianSpace (d+1)) :
    tangentProjector h (tangentProjector h x) = tangentProjector h x := by
  exact tangentProjector_self h ((tangentSpace h).orthogonalProjectionOnto x)

theorem recordInformation_projection (h : PureVector d) (data : Fin n → Record d O)
    (floor : ℝ) (x : HermitianSpace (d+1)) :
    recordInformation h data floor (tangentProjector h x) = recordInformation h data floor x := by
  simp only [recordInformation, ContinuousLinearMap.comp_apply, tangentProjector_idem]

variable [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]

def actualDelta (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P)
    (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) (n : ℕ) (path : AdaptiveInfinitePath O) : HermitianSpace (d+1) :=
  (recordCorrection (actualPreliminary P hI regularization hr batchSize path n)
    (actualRecords P hI regularization hr batchSize path n)
    (referenceFloor P) ridge (referenceFloor_pos P hp) hη).val

def actualTangentError (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P)
    (truth : PureVector d) (regularization : ℝ) (hr : 0 < regularization)
    (batchSize : ℕ → ℕ) (n : ℕ) (path : AdaptiveInfinitePath O) : HermitianSpace (d+1) :=
  (preliminaryTangentError (actualPreliminary P hI regularization hr batchSize path n) truth).val

def actualLinearError (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) (n : ℕ) (path : AdaptiveInfinitePath O) : HermitianSpace (d+1) :=
  Real.sqrt (n : ℝ) • (actualDelta P hI hp regularization ridge hr hη batchSize n path +
    actualTangentError P hI truth regularization hr batchSize n path) -
    (Real.sqrt (n : ℝ))⁻¹ • tangentProjector (actualPreliminary P hI regularization hr batchSize path n)
      (actualScoreSum P hI truth (referenceFloor P) regularization hr batchSize n path)

def actualForcing (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization)
    (batchSize : ℕ → ℕ) (n : ℕ) (path : AdaptiveInfinitePath O) : HermitianSpace (d+1) :=
  tangentProjector (actualPreliminary P hI regularization hr batchSize path n)
    ((Real.sqrt (n : ℝ))⁻¹ • (actualDerivativeSum P hI truth (referenceFloor P) regularization hr batchSize n path)
      (actualTangentError P hI truth regularization hr batchSize n path)) +
    (Real.sqrt (n : ℝ))⁻¹ • actualWeightRemainder P hI regularization hr batchSize truth (referenceFloor P) n path +
    (ridge*(Real.sqrt (n : ℝ))⁻¹) • actualTangentError P hI truth regularization hr batchSize n path -
    actualInformationError P hI regularization ridge hr batchSize n path
      ((Real.sqrt (n : ℝ))⁻¹ • actualScoreSum P hI truth (referenceFloor P) regularization hr batchSize n path)

theorem actualLinearError_bound
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) (n : ℕ) (hn : 0 < n) (path : AdaptiveInfinitePath O) :
    ‖actualLinearError P hI hp truth regularization ridge hr hη batchSize n path‖ ≤
      ‖actualForcing P hI truth regularization ridge hr batchSize n path‖ / coercivityConstant P hI := by
  let h := actualPreliminary P hI regularization hr batchSize path n
  let data := actualRecords P hI regularization hr batchSize path n
  let A := normalMap (tangentFeature h data)
    (fun r => (denominator (referenceFloor P) (fittedProbability h data r))⁻¹) ridge
  let s := score (tangentFeature h data)
    (fun r => (denominator (referenceFloor P) (fittedProbability truth data r))⁻¹)
    (fun r => observedIndicator data r - fittedProbability truth data r)
  let e := preliminaryTangentError h truth
  let δ := recordCorrection h data (referenceFloor P) ridge (referenceFloor_pos P hp) hη
  let r := noiseDerivative (tangentFeature h data) (fittedProbability truth data) (observedIndicator data)
      (referenceFloor P) e + fittedWeightRemainder (tangentFeature h data) (fittedProbability truth data)
      (fittedProbability h data) (observedIndicator data) (referenceFloor P) e + ridge • e
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hA := normalized_coercive A (n : ℝ) ridge (coercivityConstant P hI) hN hη.le
    (actual_record_normalMap_coercive P hI hp regularization ridge hr batchSize path n h)
  have he : A (δ+e) = s+r := recordCorrection_error_equation h truth data (referenceFloor P) ridge
    (referenceFloor_pos P hp) hη
  let x := Real.sqrt (n : ℝ) • (δ+e) - (Real.sqrt (n : ℝ))⁻¹ • s
  have hxe : x.val = actualLinearError P hI hp truth regularization ridge hr hη batchSize n path := by
    dsimp [x, actualLinearError, actualDelta, actualTangentError, δ, e]
    rw [show s.val = tangentProjector h (actualScoreSum P hI truth (referenceFloor P) regularization hr batchSize n path) by
      dsimp [s]; rw [score_tangent_val, actual_score_eq_sum]]
  have hres : (((n : ℝ)⁻¹ • A) x).val = actualForcing P hI truth regularization ridge hr batchSize n path := by
    have hh := congrArg Subtype.val (scaled_error_equation A (δ+e) s r (n : ℝ) hN he)
    change (((n : ℝ)⁻¹ • A) x).val = _ at hh
    rw [hh]
    simp only [Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_add]
    have hs : s.val = tangentProjector h (actualScoreSum P hI truth (referenceFloor P) regularization hr batchSize n path) := by
      dsimp [s]; rw [score_tangent_val, actual_score_eq_sum]
    have hrval : r.val = tangentProjector h
        ((actualDerivativeSum P hI truth (referenceFloor P) regularization hr batchSize n path) e.val) +
        actualWeightRemainder P hI regularization hr batchSize truth (referenceFloor P) n path + ridge • e.val := by
      dsimp [r]
      rw [actual_derivative_eq_sum]
      rfl
    rw [hrval]
    change _ - (((n : ℝ)⁻¹) • (A ((Real.sqrt (n : ℝ))⁻¹ • s)).val - _) = _
    rw [show (A ((Real.sqrt (n : ℝ))⁻¹ • s)).val = ridge • ((Real.sqrt (n : ℝ))⁻¹ • s.val) +
      recordInformation h data (referenceFloor P) ((Real.sqrt (n : ℝ))⁻¹ • s.val) from record_normalMap_val h data _ ridge _]
    rw [hs]
    simp only [actualForcing, actualInformationError, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, map_smul, smul_add, smul_sub,
      smul_smul, recordInformation_projection]
    dsimp [actualTangentError, e]
    simp only [div_eq_mul_inv]
    module
  have hb := CoerciveLeastSquares.norm_le_residual_div ((n : ℝ)⁻¹ • A)
    (coercivityConstant P hI) (coercivityConstant_pos P hI) hA x _ rfl
  change ‖x.val‖ ≤ ‖(((n : ℝ)⁻¹ • A) x).val‖ / coercivityConstant P hI at hb
  rwa [hxe,hres] at hb

end
end QubitOracle.AdaptiveDesign.TangentGLS
