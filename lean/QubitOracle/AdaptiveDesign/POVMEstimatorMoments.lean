import QubitOracle.AdaptiveDesign.AdaptiveResponseMoments
import QubitOracle.AdaptiveDesign.GeneralPOVMRootRate
import QubitOracle.AdaptiveDesign.TangentGLSStrongConsistency

/-! Root-n moments of the actual all-record POVM estimators. The constants
may depend on the fixed POVM, dimension and ridge parameters. No sample split,
extra moment assumption, Fisher symmetry or batch-growth condition is used. -/
namespace QubitOracle.AdaptiveDesign
open Filter MeasureTheory ProbabilityTheory QubitOracle QubitOracle.Paper
open GlobalPFSICHermitian PureMatrixController P2Adaptive GeneralPOVM TangentGLS
open AdaptiveResponseStrongLaw AdaptiveRidgeConsistency CoerciveLeastSquares
open AdaptiveResponseMoments
open scoped BigOperators Topology InnerProductSpace Matrix.Norms.Frobenius
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

namespace TangentGLS
/-- A global linear bound suffices for moment transfer, even for a large
correction. The sharper exact displacement formula is unnecessary here. -/
theorem updatedState_displacement_bound {d : ℕ} (h : PureVector d) (A : tangentSpace h) :
    ‖updatedState h A-rankOneDensity h.val‖ ≤ 4*‖A‖ := by
  by_cases hA : ‖A‖ ≤ 1
  · have hb := updatedState_remainder_bound h A hA
    have ht := norm_add_le (updatedState h A-(rankOneDensity h.val+toMatrix A.val)) (toMatrix A.val)
    have he : updatedState h A-(rankOneDensity h.val+toMatrix A.val)+toMatrix A.val =
        updatedState h A-rankOneDensity h.val := by abel
    rw [he, toMatrix_norm] at ht
    change ‖updatedState h A-rankOneDensity h.val‖ ≤
      ‖updatedState h A-(rankOneDensity h.val+toMatrix A.val)‖+‖A‖ at ht
    nlinarith [norm_nonneg A, mul_nonneg (norm_nonneg A) (sub_nonneg.mpr hA)]
  · have hb := norm_sub_le (updatedState h A) (rankOneDensity h.val)
    have hu : ‖updatedState h A‖ = 1 := pureProjector_norm (updatedPureVector h A)
    rw [hu, pureProjector_norm h] at hb
    linarith

theorem actualProjectorError_norm_bound {d : ℕ} {O : Type} [Fintype O]
    [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) (n : ℕ) (path : AdaptiveInfinitePath O) :
    ‖actualProjectorError P hI hp truth regularization ridge hr hη batchSize n path‖ ≤
      ‖actualPreliminaryError P hI regularization hr batchSize truth n path‖+
        4*‖actualDelta P hI hp regularization ridge hr hη batchSize n path‖ := by
  let h := actualPreliminary P hI regularization hr batchSize path n
  let A := recordCorrection h (actualRecords P hI regularization hr batchSize path n)
    (referenceFloor P) ridge (referenceFloor_pos P hp) hη
  rw [← toMatrix_norm (actualProjectorError P hI hp truth regularization ridge hr hη batchSize n path),
    ← toMatrix_norm (actualPreliminaryError P hI regularization hr batchSize truth n path)]
  change ‖updatedState h A-rankOneDensity truth.val‖ ≤
    ‖rankOneDensity h.val-rankOneDensity truth.val‖+4*‖A‖
  have ht := norm_sub_le_norm_sub_add_norm_sub (updatedState h A) (rankOneDensity h.val) (rankOneDensity truth.val)
  linarith [updatedState_displacement_bound h A]
end TangentGLS

namespace POVMEstimatorMoments
variable {d : ℕ} {O : Type} [Fintype O]
  [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]

theorem raw_uniformMoment
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P)
    (truth : PureVector d) (regularization : ℝ) (hr : 0 < regularization)
    (batchSize : ℕ → ℕ) (p : ℕ) :
    UniformMoment (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth)
      (fun n path => Real.sqrt ((n+1:ℕ):ℝ) •
        (rawEstimator P hI regularization hr batchSize path (n+1)-(pureParameter d truth).val)) p := by
  let protocol := adaptiveProtocol P hI regularization hr batchSize
  letI : IsMarkovKernel (protocol.response truth) := protocol.response_isMarkov truth
  let μ := adaptiveInfiniteTrajectoryMeasure protocol truth
  let θ := (pureParameter d truth).val
  let κ := coercivityConstant P hI
  have hκ : 0 < κ := coercivityConstant_pos P hI
  let g := fun a y => responseVector P a y-regressionFrame P a θ
  have hmean (a) : ∫ y, g a y ∂protocol.response truth a = 0 := by
    change (∫ y, responseVector P a y-regressionFrame P a θ ∂bornKernel P truth a) = 0
    rw [integral_sub Integrable.of_finite (integrable_const _), responseVector_mean P truth]
    simp [θ]
  let S := fun n path => ∑ k ∈ Finset.range (n+1), actualVectorResponse protocol g k path
  have hS := actualVectorResponse_uniformMoment protocol truth g hmean (2*responseBound P)
    (by have h := responseBound_nonnegative P; positivity) (responseInnovation_bound P truth) p
  have hB : UniformMoment μ (fun n (_ : AdaptiveInfinitePath O) =>
      (Real.sqrt ((n+1:ℕ):ℝ))⁻¹ • (-regularization • θ)) p := by
    apply uniformMoment_of_bound _ (fun _ => aestronglyMeasurable_const)
      ‖-regularization • θ‖ (norm_nonneg _)
    intro n path
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hsqrt : 1 ≤ Real.sqrt ((n+1:ℕ):ℝ) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      norm_num
    exact mul_le_of_le_one_left (norm_nonneg _) ((inv_le_one₀ (by positivity)).mpr hsqrt)
  have hSB : UniformMoment μ (fun n path => (Real.sqrt ((n+1:ℕ):ℝ))⁻¹ •
      (S n path-regularization • θ)) p := by
    simpa only [smul_add, smul_neg, neg_smul, sub_eq_add_neg] using hS.add hB
  apply hSB.of_dominated _ (fun n =>
    (FiniteHistoryStatistics.actualStatistic_stronglyMeasurable P hI regularization hr batchSize (n+1)
      (fun raw _ => Real.sqrt ((n+1:ℕ):ℝ) • (raw-θ))).aestronglyMeasurable)
    κ⁻¹ (inv_nonneg.mpr hκ.le)
  intro n path
  have heq : rawEstimator P hI regularization hr batchSize path (n+1) =
      actualRidgeEstimate protocol (regressionFrame P) (responseVector P) regularization κ
        hr hκ.le (regressionFrame_coercive P hI) path (n+1) :=
    SequentialRidgeController.pathState_estimate_eq_ridgeEstimate
      (regressionFrame P) (responseVector P) (physicalController d)
      (SequentialRidgeController.batchRefresh batchSize) regularization κ hr hκ.le
      (regressionFrame_coercive P hI) path (n+1)
  have he := ridgeEstimate_error_bound
    (fun k => regressionFrame P (actualAction protocol path k))
    (fun k => responseVector P (actualAction protocol path k) (path k)) θ
    regularization κ hr hκ.le (fun k => regressionFrame_coercive P hI _) (n+1)
  have hN : (0:ℝ)<((n+1:ℕ):ℝ) := by positivity
  have he' : ‖rawEstimator P hI regularization hr batchSize path (n+1)-θ‖ ≤
      ‖S n path-regularization • θ‖/(((n+1:ℕ):ℝ)*κ) := by
    rw [heq]
    exact he.trans (div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos hN hκ) (by linarith))
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (by positivity)]
  calc
    _ ≤ Real.sqrt ((n+1:ℕ):ℝ)*(‖S n path-regularization • θ‖/(((n+1:ℕ):ℝ)*κ)) :=
      mul_le_mul_of_nonneg_left he' (Real.sqrt_nonneg _)
    _ = _ := by
      have hs := Real.sq_sqrt hN.le
      have hs0 : Real.sqrt ((n+1:ℕ):ℝ) ≠ 0 := (Real.sqrt_pos.mpr hN).ne'
      field_simp [hN.ne',hκ.ne',hs0]
      rw [hs]
      ring

theorem preliminary_uniformMoment
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P)
    (truth : PureVector d) (regularization : ℝ) (hr : 0 < regularization)
    (batchSize : ℕ → ℕ) (p : ℕ) :
    UniformMoment (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth)
      (fun n path => Real.sqrt ((n+1:ℕ):ℝ) •
        actualPreliminaryError P hI regularization hr batchSize truth (n+1) path) p := by
  apply (raw_uniformMoment P hI truth regularization hr batchSize p).of_dominated _
    (fun n => (FiniteHistoryStatistics.actualStatistic_stronglyMeasurable P hI regularization hr batchSize (n+1)
      (fun raw _ => Real.sqrt ((n+1:ℕ):ℝ) •
        ((pureParameter d (nearestVector d (toMatrix raw))).val-(pureParameter d truth).val))).aestronglyMeasurable)
    2 (by norm_num)
  intro n path
  simp only [norm_smul]
  have h := mul_le_mul_of_nonneg_left (actualPreliminaryError_norm_bound P hI regularization hr batchSize truth (n+1) path)
    (norm_nonneg (Real.sqrt ((n+1:ℕ):ℝ)))
  simpa only [actualPreliminaryError, actualPreliminary, mul_left_comm] using h

theorem score_uniformMoment
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P)
    (truth : PureVector d) (τ : ℝ) (hτ : 0 < τ)
    (regularization : ℝ) (hr : 0 < regularization) (batchSize : ℕ → ℕ) (p : ℕ) :
    UniformMoment (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth)
      (fun n path => (Real.sqrt ((n+1:ℕ):ℝ))⁻¹ •
        actualScoreSum P hI truth τ regularization hr batchSize (n+1) path) p := by
  exact actualVectorResponse_uniformMoment _ _ _ (ambientScoreResponse_mean P truth τ)
    (2*(τ⁻¹*responseBound P)) (by have h := responseBound_nonnegative P; positivity)
    (ambientScoreResponse_bound P truth τ hτ) p

theorem correction_uniformMoment
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) (p : ℕ) :
    UniformMoment (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth)
      (fun n path => Real.sqrt ((n+1:ℕ):ℝ) • actualDelta P hI hp regularization ridge hr hη batchSize (n+1) path) p := by
  let κ := coercivityConstant P hI
  let C := (Fintype.card O:ℝ)*((referenceFloor P)⁻¹+(referenceFloor P)⁻¹^2)*(responseBound P)^2
  have hC : 0 ≤ C := by dsimp [C]; have h := referenceFloor_pos P hp; positivity
  have hs := (score_uniformMoment P hI truth (referenceFloor P) (referenceFloor_pos P hp) regularization hr batchSize p).norm
  have hp' := (preliminary_uniformMoment P hI truth regularization hr batchSize p).norm.const_mul C
  apply (hs.add hp').of_dominated _ (fun n =>
    (FiniteHistoryStatistics.actualStatistic_stronglyMeasurable P hI regularization hr batchSize (n+1)
      (fun raw data => Real.sqrt ((n+1:ℕ):ℝ) •
        (recordCorrection (nearestVector d (toMatrix raw)) data (referenceFloor P) ridge
          (referenceFloor_pos P hp) hη).val)).aestronglyMeasurable)
    κ⁻¹ (inv_nonneg.mpr (coercivityConstant_pos P hI).le)
  intro n path
  have h := mul_le_mul_of_nonneg_left
    (actualDelta_norm_bound P hI hp truth regularization ridge hr hη batchSize (n+1) (by omega) path)
    (Real.sqrt_nonneg ((n+1:ℕ):ℝ))
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (by positivity : 0 ≤ (((n+1:ℕ):ℝ))⁻¹),
    abs_of_nonneg (by positivity : 0 ≤ (Real.sqrt ((n+1:ℕ):ℝ))⁻¹)] at h ⊢
  rw [abs_of_nonneg (by positivity)]
  convert h using 1 <;> try rfl
  have hsqrt : Real.sqrt ((n+1:ℕ):ℝ) * (((n+1:ℕ):ℝ))⁻¹ =
      (Real.sqrt ((n+1:ℕ):ℝ))⁻¹ := by
    rw [← div_eq_mul_inv, Real.sqrt_div_self]
  rw [← hsqrt]
  ring

theorem corrected_uniformMoment
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) (p : ℕ) :
    UniformMoment (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth)
      (fun n path => Real.sqrt ((n+1:ℕ):ℝ) •
        actualProjectorError P hI hp truth regularization ridge hr hη batchSize (n+1) path) p := by
  have hp' := (preliminary_uniformMoment P hI truth regularization hr batchSize p).norm
  have hd := (correction_uniformMoment P hI hp truth regularization ridge hr hη batchSize p).norm.const_mul 4
  apply (hp'.add hd).of_dominated _ (fun n =>
    (FiniteHistoryStatistics.actualStatistic_stronglyMeasurable P hI regularization hr batchSize (n+1)
      (fun raw data => Real.sqrt ((n+1:ℕ):ℝ) •
        ((pureParameter d (estimateFromRaw raw data (referenceFloor P) ridge (referenceFloor_pos P hp) hη)).val-
          (pureParameter d truth).val))).aestronglyMeasurable) 1 (by norm_num)
  intro n path
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), one_mul]
  rw [abs_of_nonneg (by positivity)]
  have h := mul_le_mul_of_nonneg_left
    (actualProjectorError_norm_bound P hI hp truth regularization ridge hr hη batchSize (n+1) path)
    (Real.sqrt_nonneg ((n+1:ℕ):ℝ))
  simpa only [actualProjectorError, actualEstimate, mul_add, mul_left_comm] using h

end POVMEstimatorMoments
end
end QubitOracle.AdaptiveDesign
