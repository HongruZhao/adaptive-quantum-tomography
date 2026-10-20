import QubitOracle.AdaptiveDesign.TangentGLSLinearization

/-! Stochastic consequences of the literal normal equation. The all-data
correction cancels the preliminary error and retains only the efficient score. -/
namespace QubitOracle.AdaptiveDesign.TangentGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive
open GeneralPOVM Filter MeasureTheory ProbabilityCalculus
open scoped BigOperators Topology InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

variable {d : ℕ} {O : Type} [Fintype O]
  [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]

theorem actualTangentError_norm_le_two
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (truth : PureVector d)
    (regularization : ℝ) (hr : 0 < regularization) (batchSize : ℕ → ℕ)
    (n : ℕ) (path : AdaptiveInfinitePath O) :
    ‖actualTangentError P hI truth regularization hr batchSize n path‖ ≤ 2 :=
  (preliminaryTangentError_norm_le _ truth).trans (preliminaryError_norm_le_two _ truth)

theorem actualForcing_rootRate
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P) (hF : FisherSymmetric P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth)
      (fun n path => actualForcing P hI truth regularization ridge hr batchSize (n+1) path)
      atTop (fun _ => 0) := by
  have hM := actual_ambientDerivative_error_rootRate P hI truth (referenceFloor P) (referenceFloor_pos P hp)
    regularization hr batchSize
  have hM' : TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth)
      (fun n path => tangentProjector (actualPreliminary P hI regularization hr batchSize path (n+1))
        ((Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹ • actualDerivativeSum P hI truth (referenceFloor P)
          regularization hr batchSize (n+1) path (actualTangentError P hI truth regularization hr batchSize (n+1) path)))
      atTop (fun _ => 0) := by
    apply ProbabilityZeroAlgebra.dominated hM 1 (by norm_num)
    intro n path
    apply ((tangentProjector _).le_opNorm _).trans
    exact mul_le_mul_of_nonneg_right (tangentProjector_norm_le _) (norm_nonneg _)
  have hR := actualWeightRemainder_rootRate P hI hp truth regularization hr batchSize hpositive
  have hη : TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth)
      (fun n path => (ridge*(Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹) •
        actualTangentError P hI truth regularization hr batchSize (n+1) path) atTop (fun _ => 0) := by
    apply ProbabilityZeroAlgebra.uniform_norm_bound (fun n : ℕ => (2*|ridge|)/Real.sqrt ((n+1 : ℕ) : ℝ))
      (by simpa only [Function.comp_def] using
        (constant_div_sqrt_nat_tendsto_zero (2*|ridge|)).comp (tendsto_add_atTop_nat 1))
    intro n path
    rw [norm_smul, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (show 0 ≤ (Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹ by positivity)]
    have hb := mul_le_mul_of_nonneg_left (actualTangentError_norm_le_two P hI truth regularization hr batchSize (n+1) path)
      (show 0 ≤ |ridge| *(Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹ by positivity)
    exact hb.trans_eq (by ring)
  have hB := clm_apply_zero
    ((actualInformationError_zero P hI hp hF truth regularization ridge hr batchSize hpositive).comp (tendsto_add_atTop_nat 1))
    (actual_ambientScore_rootTight P hI truth (referenceFloor P) (referenceFloor_pos P hp) regularization hr batchSize)
  have hnB := ProbabilityZeroAlgebra.dominated hB 1 (by norm_num)
    (fun n path => (show ‖-actualInformationError P hI regularization ridge hr batchSize (n+1) path
      ((Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹ • actualScoreSum P hI truth (referenceFloor P) regularization hr batchSize (n+1) path)‖ ≤
      1*‖actualInformationError P hI regularization ridge hr batchSize (n+1) path
      ((Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹ • actualScoreSum P hI truth (referenceFloor P) regularization hr batchSize (n+1) path)‖ by simp))
  simpa only [actualForcing, sub_eq_add_neg] using
    ProbabilityZeroAlgebra.add (ProbabilityZeroAlgebra.add (ProbabilityZeroAlgebra.add hM' hR) hη) hnB

theorem actualLinearError_rootRate
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P) (hF : FisherSymmetric P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth)
      (fun n path => actualLinearError P hI hp truth regularization ridge hr hη batchSize (n+1) path)
      atTop (fun _ => 0) := by
  apply ProbabilityZeroAlgebra.dominated
    (actualForcing_rootRate P hI hp hF truth regularization ridge hr batchSize hpositive)
    (coercivityConstant P hI)⁻¹ (inv_pos.mpr (coercivityConstant_pos P hI))
  intro n path
  simpa only [div_eq_mul_inv, mul_comm] using
    actualLinearError_bound P hI hp truth regularization ridge hr hη batchSize (n+1) (by omega) path

theorem actual_projectedScore_rootTight
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P)
    (truth : PureVector d) (regularization : ℝ) (hr : 0 < regularization) (batchSize : ℕ → ℕ) :
    TightNorm (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth)
      (fun n path => (Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹ •
        tangentProjector (actualPreliminary P hI regularization hr batchSize path (n+1))
          (actualScoreSum P hI truth (referenceFloor P) regularization hr batchSize (n+1) path)) atTop := by
  apply tight_dominated
    (actual_ambientScore_rootTight P hI truth (referenceFloor P) (referenceFloor_pos P hp) regularization hr batchSize) 1 (by norm_num)
  intro n path
  rw [← map_smul]
  exact ((tangentProjector _).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (tangentProjector_norm_le _) (norm_nonneg _))

theorem quarterScale_div_sqrt_zero :
    Tendsto (fun n : ℕ => BoundedResponseQuarterRate.quarterScale n / Real.sqrt ((n+1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
  have he (n : ℕ) : BoundedResponseQuarterRate.quarterScale n / Real.sqrt ((n+1 : ℕ) : ℝ) =
      (Real.sqrt (Real.sqrt ((n+1 : ℕ) : ℝ)))⁻¹ := by
    rw [div_eq_mul_inv, mul_comm]
    exact inv_mul_sqrt _ (Real.sqrt_pos.mpr (by positivity))
  simp_rw [he]
  exact tendsto_inv_atTop_zero.comp
    (Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))))

theorem actualDelta_quarterRate
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P) (hF : FisherSymmetric P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth)
      (fun n path => BoundedResponseQuarterRate.quarterScale n • actualDelta P hI hp regularization ridge hr hη batchSize (n+1) path)
      atTop (fun _ => 0) := by
  let μ := adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth
  have ht : TightNorm μ (fun n path => Real.sqrt ((n+1 : ℕ) : ℝ) •
      (actualDelta P hI hp regularization ridge hr hη batchSize (n+1) path +
        actualTangentError P hI truth regularization hr batchSize (n+1) path)) atTop := by
    have hh := tight_add (tight_of_zero (actualLinearError_rootRate P hI hp hF truth regularization ridge hr hη batchSize hpositive))
      (actual_projectedScore_rootTight P hI hp truth regularization hr batchSize)
    simpa only [actualLinearError, sub_add_cancel] using hh
  have hs : TendstoInMeasure μ (fun n (_ : AdaptiveInfinitePath O) =>
      BoundedResponseQuarterRate.quarterScale n / Real.sqrt ((n+1 : ℕ) : ℝ)) atTop (fun _ => 0) := by
    apply ProbabilityZeroAlgebra.uniform_norm_bound _ quarterScale_div_sqrt_zero
    intro n path
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [BoundedResponseQuarterRate.quarterScale]; positivity)]
  have hsum : TendstoInMeasure μ (fun n path => BoundedResponseQuarterRate.quarterScale n •
      (actualDelta P hI hp regularization ridge hr hη batchSize (n+1) path +
        actualTangentError P hI truth regularization hr batchSize (n+1) path)) atTop (fun _ => 0) := by
    apply product_bound_zero hs ht
    intro n path
    simp only [norm_smul, Real.norm_eq_abs, abs_div]
    have hn := (Real.sqrt_pos.mpr (show (0 : ℝ) < ((n+1 : ℕ) : ℝ) by positivity)).ne'
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    field_simp
    exact le_rfl
  have he := ProbabilityZeroAlgebra.dominated
    (actualPreliminaryError_quarterRate P hI regularization hr batchSize truth) 1 (by norm_num)
    (fun n path => (show ‖-(BoundedResponseQuarterRate.quarterScale n • actualTangentError P hI truth regularization hr batchSize (n+1) path)‖ ≤
      1*‖BoundedResponseQuarterRate.quarterScale n • actualPreliminaryError P hI regularization hr batchSize truth (n+1) path‖ from by
      rw [norm_neg, one_mul, norm_smul, norm_smul]
      exact mul_le_mul_of_nonneg_left (preliminaryTangentError_norm_le _ truth) (norm_nonneg _)))
  simpa only [smul_add, add_neg_cancel_right] using ProbabilityZeroAlgebra.add hsum he

end
end QubitOracle.AdaptiveDesign.TangentGLS
