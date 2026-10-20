import QubitOracle.AdaptiveDesign.CoerciveLeastSquares
import QubitOracle.AdaptiveDesign.FiniteDimensionalResponseRates
import QubitOracle.AdaptiveDesign.FiniteHistoryStatistics
import QubitOracle.AdaptiveDesign.GeneralPOVMAdaptive
import QubitOracle.AdaptiveDesign.GeneralPOVMModel
import QubitOracle.AdaptiveDesign.GeneralPOVMProbabilityLimits
import QubitOracle.AdaptiveDesign.GeneralPOVMRootRate
import QubitOracle.AdaptiveDesign.GeneralPOVMTransport
import QubitOracle.AdaptiveDesign.GlobalPFSICBornModel
import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel
import QubitOracle.AdaptiveDesign.P2AdaptiveTheorem
import QubitOracle.AdaptiveDesign.ProbabilityCalculus
import QubitOracle.AdaptiveDesign.PureMatrixController
import QubitOracle.AdaptiveDesign.SequentialRidgeController
import QubitOracle.AdaptiveDesign.TangentGLSActualRates
import QubitOracle.AdaptiveDesign.TangentGLSAlgebra
import QubitOracle.AdaptiveDesign.TangentGLSAmbient
import QubitOracle.AdaptiveDesign.TangentGLSBounds
import QubitOracle.AdaptiveDesign.TangentGLSEstimator
import QubitOracle.AdaptiveDesign.TangentGLSGeometry
import QubitOracle.AdaptiveDesign.TangentGLSLinearization
import QubitOracle.AdaptiveDesign.TangentGLSRecordBounds
import QubitOracle.AdaptiveDesign.TangentGLSRecordIdentities
import QubitOracle.AdaptiveDesign.TangentGLSStochasticRemainder
import QubitOracle.AdaptiveDesign.TangentGLSWeightExpansion
import QubitOracle.AdaptiveDesign.TightRemainderBounds
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.AdaptiveTrajectoryExperiment
/-! The actual all-record POVM correction has an O_p(n^{-1}) intrinsic
cancellation remainder. The fitted tangent space and fitted denominators
are allowed to depend on every observation. -/
namespace QubitOracle.AdaptiveDesign.TangentGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive
open GeneralPOVM Filter MeasureTheory ProbabilityCalculus
open scoped BigOperators Topology InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
variable {d : ℕ} {O : Type} [Fintype O]
  [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]

theorem actualPreliminaryError_rootTight
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P)
    (truth : PureVector d) (regularization : ℝ) (hr : 0 < regularization)
    (batchSize : ℕ → ℕ) :
    TightNorm (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth)
      (fun n path => Real.sqrt ((n+1:ℕ):ℝ) •
        actualPreliminaryError P hI regularization hr batchSize truth (n+1) path) atTop := by
  apply tight_dominated (GeneralPOVMRootRate.rawEstimator_rootTight P hI regularization hr batchSize truth) 2 (by norm_num)
  intro n path
  simp only [norm_smul]
  simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left
    (actualPreliminaryError_norm_bound P hI regularization hr batchSize truth (n+1) path)
    (norm_nonneg (Real.sqrt ((n+1:ℕ):ℝ)))

theorem actualWeightRemainder_tight
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P)
    (truth : PureVector d) (regularization : ℝ) (hr : 0 < regularization)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    TightNorm (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth)
      (fun n path => actualWeightRemainder P hI regularization hr batchSize truth (referenceFloor P) (n+1) path) atTop := by
  let floor := referenceFloor P
  let C := responseBound P
  have hf : 0 < floor := referenceFloor_pos P hp
  have hC : 0 ≤ C := responseBound_nonnegative P
  let e := fun n path => actualPreliminaryError P hI regularization hr batchSize truth (n+1) path
  let g := fun n path => ‖Real.sqrt ((n+1:ℕ):ℝ) • e n path‖^2
  have hgm (n : ℕ) : Measurable (fun path => ‖g n path‖) := by
    have he := FiniteHistoryStatistics.actualStatistic_stronglyMeasurable P hI regularization hr batchSize (n+1)
      (fun raw _ => Real.sqrt ((n+1:ℕ):ℝ) •
        ((pureParameter d (nearestVector d (toMatrix raw))).val-(pureParameter d truth).val))
    exact (he.norm.measurable.pow_const 2).norm
  have hge (n : ℕ) (path : AdaptiveInfinitePath O) :
      ‖g n path‖ = ((n+1:ℕ):ℝ)*‖e n path‖^2 := by
    dsimp [g]
    rw [abs_of_nonneg (sq_nonneg _),norm_smul,mul_pow,
      Real.norm_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (by positivity)]
  apply tight_eventual_ae_bound
    (fun n => (actualWeightRemainder_measurable P hI regularization hr batchSize truth floor (n+1)).norm.measurable)
    hgm (tight_square_norm (actualPreliminaryError_rootTight P hI truth regularization hr batchSize))
    ((Fintype.card O:ℝ)*regularRemainderConstant floor C) (by dsimp [regularRemainderConstant]; positivity)
  filter_upwards [actualPreliminaryError_consistent P hI regularization hr batchSize truth,
    actual_probabilities_eventually_regular P hI hp truth regularization hr batchSize hpositive]
    with path he hreg
  obtain ⟨K,hK⟩ := hreg
  refine ⟨((K*Fintype.card O:ℕ):ℝ)*clippedRemainderConstant floor C,?_⟩
  have hclose : ∀ᶠ n in atTop, C*‖e n path‖ ≤ floor := by
    have hh : Tendsto (fun n => C*‖e n path‖) atTop (𝓝 0) := by
      simpa [e] using (he.comp (tendsto_add_atTop_nat 1)).norm.const_mul C
    exact (hh.eventually (Iio_mem_nhds hf)).mono (fun n hn => hn.le)
  filter_upwards [hclose] with n hn
  let h := actualPreliminary P hI regularization hr batchSize path (n+1)
  let data := actualRecords P hI regularization hr batchSize path (n+1)
  have hfeature (r : Fin (n+1) × O) : ‖recordFeature data r‖ ≤ C := by
    rw [show recordFeature data r = responseVector P
      (actualState P hI regularization hr batchSize path r.1).action r.2 from
        actual_recordFeature_eq P hI regularization hr batchSize path (n+1) r]
    exact responseVector_norm_le P _ _
  have hbad : badRowCount truth data floor ≤ K*Fintype.card O := by
    apply badRowCount_bound truth data floor K
    intro t ht y
    rw [show fittedProbability truth data (t,y) = bornProbability P truth
      (actualState P hI regularization hr batchSize path t).action y from
        actual_fittedProbability_eq P hI regularization hr batchSize truth path (n+1) (t,y)]
    exact hK t ht y
  have hb := record_remainder_bound_if_close h truth data floor C hf hC hfeature hn
  have hb' : ‖actualWeightRemainder P hI regularization hr batchSize truth floor (n+1) path‖ ≤
      (((n+1)*Fintype.card O:ℕ):ℝ)*regularRemainderConstant floor C*‖e n path‖^2 +
      ((K*Fintype.card O:ℕ):ℝ)*clippedRemainderConstant floor C := by
    apply hb.trans
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (by exact_mod_cast hbad)
      (by dsimp [clippedRemainderConstant]; positivity))
  apply hb'.trans_eq
  rw [hge]
  simp only [Nat.cast_mul]
  ring

/-- The intrinsic exact cancellation residual, before inversion of the
fitted normal operator. -/
def actualSecondOrderForcing
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization)
    (batchSize : ℕ → ℕ) (n : ℕ) (path : AdaptiveInfinitePath O) : HermitianSpace (d+1) :=
  tangentProjector (actualPreliminary P hI regularization hr batchSize path n)
    (actualDerivativeSum P hI truth (referenceFloor P) regularization hr batchSize n path
      (actualTangentError P hI truth regularization hr batchSize n path)) +
  actualWeightRemainder P hI regularization hr batchSize truth (referenceFloor P) n path +
  ridge • actualTangentError P hI truth regularization hr batchSize n path

theorem actualSecondOrderForcing_tight
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    TightNorm (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth)
      (fun n path => actualSecondOrderForcing P hI truth regularization ridge hr batchSize (n+1) path) atTop := by
  let M := fun n path => actualDerivativeSum P hI truth (referenceFloor P) regularization hr batchSize (n+1) path
  let e := fun n path => actualTangentError P hI truth regularization hr batchSize (n+1) path
  have hM : TightNorm (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth)
      (fun n path => (Real.sqrt ((n+1:ℕ):ℝ))⁻¹ • M n path) atTop :=
    FiniteDimensionalResponseRates.actualResponse_rootTight_normed _ _ _
      (ambientDerivativeResponse_mean P truth (referenceFloor P))
      (2*((referenceFloor P^2)⁻¹*(responseBound P)^2)) (by positivity)
      (ambientDerivativeResponse_bound P truth (referenceFloor P) (referenceFloor_pos P hp))
  have he : TightNorm (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth)
      (fun n path => Real.sqrt ((n+1:ℕ):ℝ) • e n path) atTop := by
    apply tight_dominated (actualPreliminaryError_rootTight P hI truth regularization hr batchSize) 1 (by norm_num)
    intro n path
    simp only [norm_smul,one_mul]
    exact mul_le_mul_of_nonneg_left (preliminaryTangentError_norm_le _ truth) (norm_nonneg _)
  have hprod : TightNorm (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth)
      (fun n path => tangentProjector (actualPreliminary P hI regularization hr batchSize path (n+1))
        (M n path (e n path))) atTop := by
    apply tight_product_bound hM he
    intro n path
    have hproj := (tangentSpace (actualPreliminary P hI regularization hr batchSize path (n+1))).norm_starProjection_apply_le
      (M n path (e n path))
    apply hproj.trans
    have hN : Real.sqrt ((n+1:ℕ):ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    simp only [norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    calc
      ‖M n path (e n path)‖ ≤ ‖M n path‖*‖e n path‖ := (M n path).le_opNorm _
      _ = _ := by field_simp
  have hridge : TightNorm (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth)
      (fun n path => ridge • e n path) atTop := by
    apply tight_uniform_bound (|ridge| * 2)
    intro n path
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left ((preliminaryTangentError_norm_le _ truth).trans
      (preliminaryError_norm_le_two _ truth)) (abs_nonneg _)
  exact tight_add (tight_add hprod
    (actualWeightRemainder_tight P hI hp truth regularization hr batchSize hpositive)) hridge

/-- Literal residual of the actual correction after removing the fitted
inverse-normal-operator score term. -/
def actualCancellationError
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) (n : ℕ) (path : AdaptiveInfinitePath O) : HermitianSpace (d+1) :=
  let h := actualPreliminary P hI regularization hr batchSize path n
  let data := actualRecords P hI regularization hr batchSize path n
  let floor := referenceFloor P
  let hf := referenceFloor_pos P hp
  let A := normalEquiv (tangentFeature h data)
    (fun r => (denominator floor (fittedProbability h data r))⁻¹)
    (fun r => (inv_pos.mpr (denominator_pos hf _)).le) ridge hη
  let s := score (tangentFeature h data)
    (fun r => (denominator floor (fittedProbability truth data r))⁻¹)
    (fun r => observedIndicator data r-fittedProbability truth data r)
  (recordCorrection h data floor ridge hf hη + preliminaryTangentError h truth-A.symm s).val

theorem actualCancellationError_bound
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) (n : ℕ) (hn : 0 < n) (path : AdaptiveInfinitePath O) :
    ‖(n:ℝ) • actualCancellationError P hI hp truth regularization ridge hr hη batchSize n path‖ ≤
      (coercivityConstant P hI)⁻¹ *
        ‖actualSecondOrderForcing P hI truth regularization ridge hr batchSize n path‖ := by
  let h := actualPreliminary P hI regularization hr batchSize path n
  let data := actualRecords P hI regularization hr batchSize path n
  let floor := referenceFloor P
  let hf := referenceFloor_pos P hp
  let A := normalEquiv (tangentFeature h data)
    (fun r => (denominator floor (fittedProbability h data r))⁻¹)
    (fun r => (inv_pos.mpr (denominator_pos hf _)).le) ridge hη
  let s := score (tangentFeature h data)
    (fun r => (denominator floor (fittedProbability truth data r))⁻¹)
    (fun r => observedIndicator data r-fittedProbability truth data r)
  let e := preliminaryTangentError h truth
  let r := noiseDerivative (tangentFeature h data) (fittedProbability truth data)
      (observedIndicator data) floor e +
    fittedWeightRemainder (tangentFeature h data) (fittedProbability truth data)
      (fittedProbability h data) (observedIndicator data) floor e + ridge • e
  let x := recordCorrection h data floor ridge hf hη + e-A.symm s
  have he : A x=r := by
    dsimp only [x]
    rw [map_sub,A.apply_symm_apply]
    have hh := recordCorrection_error_equation h truth data floor ridge hf hη
    change A (recordCorrection h data floor ridge hf hη+e)=s+r at hh
    rw [hh]
    abel
  have hrval : r.val=actualSecondOrderForcing P hI truth regularization ridge hr batchSize n path := by
    dsimp only [r]
    simp only [Submodule.coe_add,Submodule.coe_smul]
    rw [actual_derivative_eq_sum]
    rfl
  have hN : (0:ℝ)<n := by exact_mod_cast hn
  have hco : CoerciveLeastSquares.Coercive A.toLinearMap ((n:ℝ)*coercivityConstant P hI) := by
    intro z
    have hh := actual_record_normalMap_coercive P hI hp regularization ridge hr batchSize path n h z
    change _ ≤ ⟪z,A z⟫_ℝ at hh
    change (n:ℝ)*coercivityConstant P hI*‖z‖^2 ≤ ⟪z,A z⟫_ℝ
    nlinarith [mul_nonneg hη.le (sq_nonneg ‖z‖)]
  have hb := CoerciveLeastSquares.norm_le_residual_div A.toLinearMap
    ((n:ℝ)*coercivityConstant P hI) (mul_pos hN (coercivityConstant_pos P hI)) hco x r he
  change ‖x.val‖ ≤ ‖r.val‖/((n:ℝ)*coercivityConstant P hI) at hb
  rw [hrval] at hb
  rw [norm_smul,Real.norm_of_nonneg hN.le]
  change (n:ℝ)*‖x.val‖ ≤ _
  apply (mul_le_mul_of_nonneg_left hb hN.le).trans_eq
  field_simp

/-- Exactly the O_p(n^{-1}) remainder claimed in the intrinsic cancellation
formula, for every predetermined sequence of positive finite batches. -/
theorem actualCancellationError_secondOrder
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    TightNorm (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth)
      (fun n path => ((n+1:ℕ):ℝ) •
        actualCancellationError P hI hp truth regularization ridge hr hη batchSize (n+1) path) atTop := by
  exact tight_dominated
    (actualSecondOrderForcing_tight P hI hp truth regularization ridge hr batchSize hpositive)
    (coercivityConstant P hI)⁻¹ (inv_pos.mpr (coercivityConstant_pos P hI))
    (fun n path => actualCancellationError_bound P hI hp truth regularization ridge hr hη batchSize
      (n+1) (by omega) path)

end
end QubitOracle.AdaptiveDesign.TangentGLS
