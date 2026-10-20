import QubitOracle.AdaptiveDesign.AdaptiveRidgeConsistency
import QubitOracle.AdaptiveDesign.BoundedResponseQuarterRate
import QubitOracle.AdaptiveDesign.FiniteHistoryStatistics
import QubitOracle.AdaptiveDesign.GeneralPOVMAdaptive
import QubitOracle.AdaptiveDesign.GeneralPOVMModel
import QubitOracle.AdaptiveDesign.GeneralPOVMProbabilityLimits
import QubitOracle.AdaptiveDesign.GeneralPOVMTransport
import QubitOracle.AdaptiveDesign.GlobalPFSICBornModel
import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel
import QubitOracle.AdaptiveDesign.P2AdaptiveTheorem
import QubitOracle.AdaptiveDesign.ProbabilityCalculus
import QubitOracle.AdaptiveDesign.ProbabilityZeroAlgebra
import QubitOracle.AdaptiveDesign.PureMatrixController
import QubitOracle.AdaptiveDesign.SequentialRidgeController
import QubitOracle.AdaptiveDesign.TangentGLSActualRates
import QubitOracle.AdaptiveDesign.TangentGLSAmbient
import QubitOracle.AdaptiveDesign.TangentGLSBounds
import QubitOracle.AdaptiveDesign.TangentGLSEstimator
import QubitOracle.AdaptiveDesign.TangentGLSGeometry
import QubitOracle.AdaptiveDesign.TangentGLSRecordBounds
import QubitOracle.AdaptiveDesign.TangentGLSWeightExpansion
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.AdaptiveTrajectoryExperiment
import QubitOracle.Paper.FiniteAdaptiveBornScoreClosure
/-! The fitted-weight remainder of the actual all-record estimator vanishes
at root-n scale. Early clipped records, data reuse, and the nonlinear pure
state constraint are all included in this theorem. -/

namespace QubitOracle.AdaptiveDesign.TangentGLS

open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController
open Filter MeasureTheory ProbabilityTheory ProbabilityCalculus
open scoped BigOperators Topology InnerProductSpace ComplexOrder
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {d : ℕ} {O : Type} [Fintype O]
  [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]

def actualWeightRemainder
    (P : FinitePOVM (Fin (d+1)) O) (hI : GeneralPOVM.Identifying P)
    (regularization : ℝ) (hr : 0 < regularization) (batchSize : ℕ → ℕ)
    (truth : PureVector d) (floor : ℝ) (n : ℕ) (path : AdaptiveInfinitePath O) : HermitianSpace (d+1) :=
  let h := actualPreliminary P hI regularization hr batchSize path n
  let data := actualRecords P hI regularization hr batchSize path n
  (fittedWeightRemainder (tangentFeature h data) (fittedProbability truth data)
    (fittedProbability h data) (observedIndicator data) floor (preliminaryTangentError h truth)).val

theorem actualWeightRemainder_measurable
    (P : FinitePOVM (Fin (d+1)) O) (hI : GeneralPOVM.Identifying P)
    (regularization : ℝ) (hr : 0 < regularization) (batchSize : ℕ → ℕ)
    (truth : PureVector d) (floor : ℝ) (n : ℕ) :
    StronglyMeasurable (actualWeightRemainder P hI regularization hr batchSize truth floor n) := by
  exact FiniteHistoryStatistics.actualStatistic_stronglyMeasurable P hI regularization hr batchSize n
    (fun raw data =>
      let h := nearestVector d (toMatrix raw)
      (fittedWeightRemainder (tangentFeature h data) (fittedProbability truth data)
        (fittedProbability h data) (observedIndicator data) floor (preliminaryTangentError h truth)).val)

theorem actualWeightRemainder_rootRate
    (P : FinitePOVM (Fin (d+1)) O) (hI : GeneralPOVM.Identifying P) (hp : GeneralPOVM.Regular P)
    (truth : PureVector d) (regularization : ℝ) (hr : 0 < regularization)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure
      (GeneralPOVM.adaptiveProtocol P hI regularization hr batchSize) truth)
      (fun n path => (Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹ •
        actualWeightRemainder P hI regularization hr batchSize truth (referenceFloor P) (n+1) path)
      atTop (fun _ => 0) := by
  let floor := referenceFloor P
  let C := GeneralPOVM.responseBound P
  have hf : 0 < floor := referenceFloor_pos P hp
  have hC : 0 ≤ C := GeneralPOVM.responseBound_nonnegative P
  let α := (Fintype.card O : ℝ) * regularRemainderConstant floor C
  have ha : Tendsto (fun n : ℕ => (Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      (constant_div_sqrt_nat_tendsto_zero 1).comp (tendsto_add_atTop_nat 1)
  apply of_eventual_ae_bound α
    (fun n => ((actualWeightRemainder_measurable P hI regularization hr batchSize truth floor (n+1)).const_smul
      (Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹).aestronglyMeasurable)
    (actualPreliminaryError_square_rootRate P hI regularization hr batchSize truth) ha
  filter_upwards [actualPreliminaryError_consistent P hI regularization hr batchSize truth,
    actual_probabilities_eventually_regular P hI hp truth regularization hr batchSize hpositive]
    with path he hreg
  obtain ⟨K,hK⟩ := hreg
  refine ⟨((K*Fintype.card O : ℕ) : ℝ) * clippedRemainderConstant floor C, ?_⟩
  have hclose : ∀ᶠ n in atTop,
      C * ‖actualPreliminaryError P hI regularization hr batchSize truth (n+1) path‖ ≤ floor := by
    have hh : Tendsto (fun n => C * ‖actualPreliminaryError P hI regularization hr batchSize truth (n+1) path‖)
        atTop (𝓝 0) := by
      simpa using (he.comp (tendsto_add_atTop_nat 1)).norm.const_mul C
    exact (hh.eventually (Iio_mem_nhds hf)).mono (fun n hn => hn.le)
  filter_upwards [hclose] with n hn
  let h := actualPreliminary P hI regularization hr batchSize path (n+1)
  let data := actualRecords P hI regularization hr batchSize path (n+1)
  have hfeature (r : Fin (n+1) × O) : ‖recordFeature data r‖ ≤ C := by
    rw [show recordFeature data r = GeneralPOVM.responseVector P
      (GeneralPOVM.actualState P hI regularization hr batchSize path r.1).action r.2 from
        actual_recordFeature_eq P hI regularization hr batchSize path (n+1) r]
    exact GeneralPOVM.responseVector_norm_le P _ _
  have hbad : badRowCount truth data floor ≤ K*Fintype.card O := by
    apply badRowCount_bound truth data floor K
    intro t ht y
    rw [show fittedProbability truth data (t,y) = GeneralPOVM.bornProbability P truth
      (GeneralPOVM.actualState P hI regularization hr batchSize path t).action y from
        actual_fittedProbability_eq P hI regularization hr batchSize truth path (n+1) (t,y)]
    exact hK t ht y
  have hb := record_remainder_bound_if_close h truth data floor C hf hC hfeature hn
  have hb' : ‖actualWeightRemainder P hI regularization hr batchSize truth floor (n+1) path‖ ≤
      (((n+1)*Fintype.card O : ℕ) : ℝ) * regularRemainderConstant floor C *
        ‖actualPreliminaryError P hI regularization hr batchSize truth (n+1) path‖^2 +
      ((K*Fintype.card O : ℕ) : ℝ) * clippedRemainderConstant floor C := by
    apply hb.trans
    exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right (by exact_mod_cast hbad)
      (by dsimp [clippedRemainderConstant]; positivity))
  simp only [Pi.smul_apply]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply (mul_le_mul_of_nonneg_left hb' (by positivity)).trans_eq
  rw [abs_of_nonneg (by positivity)]
  dsimp [α]
  simp only [Nat.cast_mul]
  have hs := Real.sq_sqrt (show 0 ≤ ((n+1 : ℕ) : ℝ) by positivity)
  have hsp : Real.sqrt ((n+1 : ℕ) : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hN : (Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹ * ((n+1 : ℕ) : ℝ) = Real.sqrt ((n+1 : ℕ) : ℝ) := by
    conv_lhs => rhs; rw [← hs]
    field_simp
  calc
    _ = ((Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹ * ((n+1 : ℕ) : ℝ)) *
        ((Fintype.card O : ℝ) * regularRemainderConstant floor C *
          ‖actualPreliminaryError P hI regularization hr batchSize truth (n+1) path‖^2) +
        (Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹ *
          ((K : ℝ) * (Fintype.card O : ℝ) * clippedRemainderConstant floor C) := by ring
    _ = _ := by rw [hN]; ring

theorem quarterScale_product (n : ℕ) :
    (BoundedResponseQuarterRate.quarterScale n / ((n+1 : ℕ) : ℝ)) *
      BoundedResponseQuarterRate.quarterScale n = (Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹ := by
  have hn : (((n+1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hs := Real.sq_sqrt (show 0 ≤ ((n+1 : ℕ) : ℝ) by positivity)
  have hsp : Real.sqrt ((n+1 : ℕ) : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  calc
    _ = BoundedResponseQuarterRate.quarterScale n ^ 2 / ((n+1 : ℕ) : ℝ) := by ring
    _ = Real.sqrt ((n+1 : ℕ) : ℝ) / ((n+1 : ℕ) : ℝ) := by rw [BoundedResponseQuarterRate.quarterScale_sq]
    _ = _ := by
      apply (div_eq_iff hn).mpr
      calc
        Real.sqrt ((n+1 : ℕ) : ℝ) = (Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹ *
            (Real.sqrt ((n+1 : ℕ) : ℝ))^2 := by field_simp
        _ = _ := by rw [hs]

/-- The same-data preliminary error times the centered derivative operator
is negligible. Only the fixed-truth operator response is treated as a
martingale; the preliminary estimate is never declared predictable. -/
theorem actual_ambientDerivative_error_rootRate
    (P : FinitePOVM (Fin (d+1)) O) (hI : GeneralPOVM.Identifying P)
    (truth : PureVector d) (floor : ℝ) (hf : 0 < floor)
    (regularization : ℝ) (hr : 0 < regularization) (batchSize : ℕ → ℕ) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure
      (GeneralPOVM.adaptiveProtocol P hI regularization hr batchSize) truth)
      (fun n path => (Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹ •
        (∑ k ∈ Finset.range (n+1), AdaptiveRidgeConsistency.actualVectorResponse
          (GeneralPOVM.adaptiveProtocol P hI regularization hr batchSize)
          (ambientDerivativeResponse P truth floor) k path)
        (preliminaryTangentError (actualPreliminary P hI regularization hr batchSize path (n+1)) truth).val)
      atTop (fun _ => 0) := by
  let e := fun n path =>
    (preliminaryTangentError (actualPreliminary P hI regularization hr batchSize path (n+1)) truth).val
  let M := fun n path => ∑ k ∈ Finset.range (n+1), AdaptiveRidgeConsistency.actualVectorResponse
    (GeneralPOVM.adaptiveProtocol P hI regularization hr batchSize)
    (ambientDerivativeResponse P truth floor) k path
  have he : TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure
      (GeneralPOVM.adaptiveProtocol P hI regularization hr batchSize) truth)
      (fun n path => BoundedResponseQuarterRate.quarterScale n • e n path) atTop (fun _ => 0) := by
    apply ProbabilityZeroAlgebra.dominated
      (actualPreliminaryError_quarterRate P hI regularization hr batchSize truth) 1 (by norm_num)
    intro n path
    simp only [norm_smul, one_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact preliminaryTangentError_norm_le _ truth
  have hprod := clm_apply_zero
    (actual_ambientDerivative_quarterRate P hI truth floor hf regularization hr batchSize)
    (tight_of_zero he)
  have heq (n : ℕ) (path : AdaptiveInfinitePath O) :
      ((BoundedResponseQuarterRate.quarterScale n / ((n+1 : ℕ) : ℝ)) • M n path)
        (BoundedResponseQuarterRate.quarterScale n • e n path) =
      (Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹ • (M n path) (e n path) := by
    rw [ContinuousLinearMap.smul_apply, map_smul, smul_smul]
    rw [quarterScale_product]
  change TendstoInMeasure _ (fun n path => (Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹ • (M n path) (e n path)) atTop (fun _ => 0)
  have hh : TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure
      (GeneralPOVM.adaptiveProtocol P hI regularization hr batchSize) truth)
      (fun n path => ((BoundedResponseQuarterRate.quarterScale n / ((n+1 : ℕ) : ℝ)) • M n path)
        (BoundedResponseQuarterRate.quarterScale n • e n path)) atTop (fun _ => 0) := hprod
  simpa only [heq] using hh

end
end QubitOracle.AdaptiveDesign.TangentGLS
