import QubitOracle.AdaptiveDesign.TangentGLSOperatorBounds

/-! The actual fitted information operator converges almost surely. This
uses consistency and the reference Fisher limit, with no independence
assumption on the fitted weights. -/
namespace QubitOracle.AdaptiveDesign.TangentGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive
open GeneralPOVM Filter MeasureTheory
open scoped BigOperators Topology InnerProductSpace Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {d : ℕ} {O : Type} [Fintype O]

theorem single_information_eq (P : FinitePOVM (Fin (d+1)) O) (truth : PureVector d)
    (floor : ℝ) (U : GlobalPFSICBorn.Action d) :
    (tangentProjector truth).comp ((gramCLM (responseVector P U)
      (fun y => (denominator floor (bornProbability P truth U y))⁻¹)).comp (tangentProjector truth)) =
    informationLift truth (protectedFisher P floor ((trueFrame d truth).conjTranspose * U.matrix)) := by
  rw [projected_gram_coordinates]
  simp_rw [trueCoordinate_responseVector, bornProbability_pure_eq_mass]
  rw [gramCLM_eq_matrix]
  rfl

variable [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]

theorem actual_trueInformation_eq_sum
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P)
    (truth : PureVector d) (floor regularization : ℝ) (hr : 0 < regularization)
    (batchSize : ℕ → ℕ) (path : AdaptiveInfinitePath O) (n : ℕ) :
    recordInformation truth (actualRecords P hI regularization hr batchSize path n) floor =
      ∑ t ∈ Finset.range n, informationLift truth (protectedFisher P floor
        ((trueFrame d truth).conjTranspose * measurementFrame P hI regularization hr batchSize path t)) := by
  have hs : (∑ t : Fin n, informationLift truth (protectedFisher P floor
      ((trueFrame d truth).conjTranspose * measurementFrame P hI regularization hr batchSize path t))) =
      ∑ t ∈ Finset.range n, informationLift truth (protectedFisher P floor
      ((trueFrame d truth).conjTranspose * measurementFrame P hI regularization hr batchSize path t)) :=
    Fin.sum_univ_eq_sum_range (fun t => informationLift truth (protectedFisher P floor
      ((trueFrame d truth).conjTranspose * measurementFrame P hI regularization hr batchSize path t))) n
  rw [← hs]
  simp only [GeneralPOVM.measurementFrame]
  simp_rw [← single_information_eq P truth floor
    (actualState P hI regularization hr batchSize path _).action]
  ext x
  simp only [recordInformation, ContinuousLinearMap.comp_apply, gramCLM_apply,
    map_sum, Fintype.sum_prod_type, ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro t _
  congr 1

theorem actual_trueInformation_tendsto
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P) (hF : FisherSymmetric P)
    (truth : PureVector d) (regularization : ℝ) (hr : 0 < regularization)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • recordInformation truth
        (actualRecords P hI regularization hr batchSize path n) (referenceFloor P))
      atTop (𝓝 (tangentProjector truth)) := by
  filter_upwards [actual_protectedFisher_tendsto P hI hp hF truth regularization hr batchSize hpositive]
    with path hpath
  have hh := ((informationLift_continuous truth).continuousAt.tendsto.comp hpath).cesaro_smul
  simpa only [informationLift_half_identity, actual_trueInformation_eq_sum, Function.comp_def] using hh

theorem actual_tangentProjector_tendsto
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P)
    (truth : PureVector d) (regularization : ℝ) (hr : 0 < regularization) (batchSize : ℕ → ℕ) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth,
      Tendsto (fun n => tangentProjector (actualPreliminary P hI regularization hr batchSize path n))
      atTop (𝓝 (tangentProjector truth)) := by
  filter_upwards [actualPreliminaryError_consistent P hI regularization hr batchSize truth] with path he
  apply tendsto_sub_nhds_zero_iff.mp
  apply squeeze_zero_norm (fun n => tangentProjector_lipschitz _ truth)
  simpa only [actualPreliminaryError, norm_zero, mul_zero] using he.norm.const_mul 6

theorem actual_fittedInformation_tendsto
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P) (hF : FisherSymmetric P)
    (truth : PureVector d) (regularization : ℝ) (hr : 0 < regularization)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • recordInformation
        (actualPreliminary P hI regularization hr batchSize path n)
        (actualRecords P hI regularization hr batchSize path n) (referenceFloor P))
      atTop (𝓝 (tangentProjector truth)) := by
  filter_upwards [actualPreliminaryError_consistent P hI regularization hr batchSize truth,
    actual_trueInformation_tendsto P hI hp hF truth regularization hr batchSize hpositive]
    with path he ht
  let C := responseBound P
  let floor := referenceFloor P
  let B := (Fintype.card O : ℝ)*(C^3/floor^2+12*C^2/floor)
  have hd : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • (recordInformation
      (actualPreliminary P hI regularization hr batchSize path n)
      (actualRecords P hI regularization hr batchSize path n) floor -
      recordInformation truth (actualRecords P hI regularization hr batchSize path n) floor))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (show Tendsto (fun n => B*‖actualPreliminaryError P hI regularization hr batchSize truth n path‖)
      atTop (𝓝 0) by simpa using he.norm.const_mul B)
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn')]
    have hb := recordInformation_difference
      (actualPreliminary P hI regularization hr batchSize path n) truth
      (actualRecords P hI regularization hr batchSize path n) floor C
      (referenceFloor_pos P hp) (responseBound_nonnegative P)
      (fun r => by rw [actual_recordFeature_eq]; exact responseVector_norm_le P _ _)
    apply (mul_le_mul_of_nonneg_left hb (inv_pos.mpr hn').le).trans_eq
    dsimp [B, actualPreliminaryError]
    simp only [← mul_assoc, inv_mul_cancel₀ hn'.ne', one_mul]
  have hh := hd.add ht
  simpa only [floor, smul_sub, sub_add_cancel, zero_add] using hh

def actualInformationError
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P)
    (regularization ridge : ℝ) (hr : 0 < regularization) (batchSize : ℕ → ℕ)
    (n : ℕ) (path : AdaptiveInfinitePath O) : HermitianSpace (d+1) →L[ℝ] HermitianSpace (d+1) :=
  let h := actualPreliminary P hI regularization hr batchSize path n
  (ridge/(n : ℝ)) • tangentProjector h + (n : ℝ)⁻¹ • recordInformation h
    (actualRecords P hI regularization hr batchSize path n) (referenceFloor P) - tangentProjector h

theorem actualInformationError_zero
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P) (hF : FisherSymmetric P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth)
      (actualInformationError P hI regularization ridge hr batchSize) atTop (fun _ => 0) := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    exact (FiniteHistoryStatistics.actualStatistic_stronglyMeasurable P hI regularization hr batchSize n
      (fun raw data => let h := nearestVector d (toMatrix raw)
        (ridge/(n : ℝ)) • tangentProjector h + (n : ℝ)⁻¹ • recordInformation h data (referenceFloor P) -
          tangentProjector h)).aestronglyMeasurable
  · filter_upwards [actual_tangentProjector_tendsto P hI truth regularization hr batchSize,
      actual_fittedInformation_tendsto P hI hp hF truth regularization hr batchSize hpositive] with path hQ hG
    have hr0 : Tendsto (fun n : ℕ => ridge/(n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa only [actualInformationError, zero_smul, zero_add, sub_self] using ((hr0.smul hQ).add hG).sub hQ

end
end QubitOracle.AdaptiveDesign.TangentGLS
