import QubitOracle.AdaptiveDesign.BoundedResponseQuarterRate
import QubitOracle.AdaptiveDesign.GeneralPOVMAdaptive

/-!
# A preliminary rate for the actual all-data pure-state estimator

Bounded adaptive innovations and the uniform identifying-frame bound prove
the o_P(n^(-1/4)) rate required by the one-step remainder argument. No sample
split and no source concentration or moment axiom is introduced.
-/

namespace QubitOracle.AdaptiveDesign.GeneralPOVMQuarterRate

open Filter MeasureTheory ProbabilityTheory QubitOracle.Paper
open AdaptiveResponseStrongLaw AdaptiveRidgeConsistency CoerciveLeastSquares
open BoundedResponseQuarterRate
open scoped BigOperators Topology InnerProductSpace Matrix.Norms.Frobenius
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

variable {Theta Action Outcome E : Type*}
  [MeasurableSpace Action] [MeasurableSpace Outcome]
  [Fintype Outcome] [MeasurableSingletonClass Outcome]
  [StandardBorelSpace Outcome] [Nonempty Outcome]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem actualRidgeEstimate_quarterRate
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta)
    (frame : Action → E →ₗ[ℝ] E) (response : Action → Outcome → E) (truth : E)
    (regularization κ : ℝ) (hr : 0 < regularization)
    (hκ : 0 < κ) (hframe : ∀ a, Coercive (frame a) κ)
    (hmean : ∀ a, ∫ y, response a y ∂protocol.response theta a = frame a truth)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ a y, ‖response a y - frame a truth‖ ≤ C) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure protocol theta)
      (fun n path => quarterScale n •
        (actualRidgeEstimate protocol frame response regularization κ hr hκ.le hframe path (n+1) - truth))
      atTop (fun _ => (0 : E)) := by
  letI : IsMarkovKernel (protocol.response theta) := protocol.response_isMarkov theta
  let centered := fun a y => response a y - frame a truth
  have hc (a : Action) : ∫ y, centered a y ∂protocol.response theta a = 0 := by
    dsimp [centered]
    rw [integral_sub Integrable.of_finite (integrable_const _), hmean]
    simp
  let sumNoise := fun n path => ∑ k ∈ Finset.range (n+1), actualVectorResponse protocol centered k path
  have ha := actualVectorResponse_quarterRate protocol theta centered hc C hC hb
  have hbiased : TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure protocol theta)
      (fun n path => (quarterScale n / ((n+1 : ℕ) : ℝ)) • (sumNoise n path - regularization • truth))
      atTop (fun _ => (0 : E)) := by
    have hconstant : TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure protocol theta)
        (fun n (_ : AdaptiveInfinitePath Outcome) =>
          (quarterScale n / ((n+1 : ℕ) : ℝ)) • (-regularization • truth)) atTop (fun _ => (0 : E)) := by
      apply ProbabilityZeroAlgebra.uniform_norm_bound
        (fun n => (quarterScale n / ((n+1 : ℕ) : ℝ)) * ‖-regularization • truth‖)
        (by simpa using quarterScale_div_tendsto_zero.mul_const ‖-regularization • truth‖)
      intro n path
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg
        (div_pos (quarterScale_pos n) (by positivity)).le]
    simpa only [sumNoise, smul_sub, neg_smul, smul_neg, sub_eq_add_neg, smul_add] using
      (ProbabilityZeroAlgebra.add ha hconstant)
  apply ProbabilityZeroAlgebra.dominated hbiased (κ⁻¹) (inv_pos.mpr hκ)
  intro n path
  have he := ridgeEstimate_error_bound
    (fun k => frame (actualAction protocol path k))
    (fun k => response (actualAction protocol path k) (path k)) truth
    regularization κ hr hκ.le (fun k => hframe _) (n+1)
  have hn : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  have hdn : 0 < ((n+1 : ℕ) : ℝ) * κ := mul_pos hn hκ
  have hden : ((n+1 : ℕ) : ℝ) * κ ≤ regularization + ((n+1 : ℕ) : ℝ) * κ := by linarith
  have he' : ‖actualRidgeEstimate protocol frame response regularization κ hr hκ.le hframe path (n+1) - truth‖ ≤
      ‖sumNoise n path - regularization • truth‖ / (((n+1 : ℕ) : ℝ) * κ) :=
    he.trans (div_le_div_of_nonneg_left (norm_nonneg _) hdn hden)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (quarterScale_pos n)]
  calc
    _ ≤ quarterScale n * (‖sumNoise n path - regularization • truth‖ / (((n+1 : ℕ) : ℝ) * κ)) :=
      mul_le_mul_of_nonneg_left he' (quarterScale_pos n).le
    _ = κ⁻¹ * ‖(quarterScale n / ((n+1 : ℕ) : ℝ)) • (sumNoise n path - regularization • truth)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_pos (quarterScale_pos n) hn).le]
      field_simp

open QubitOracle GeneralPOVM GlobalPFSICHermitian PureMatrixController P2Adaptive

variable {d : ℕ} {O : Type} [Fintype O] [MeasurableSpace O]
  [MeasurableSingletonClass O] [Nonempty O]

theorem rawEstimator_quarterRate
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P)
    (regularization : ℝ) (hr : 0 < regularization) (batchSize : ℕ → ℕ) (truth : PureVector d) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth)
      (fun n path => quarterScale n •
        (rawEstimator P hI regularization hr batchSize path (n+1) - (pureParameter d truth).val))
      atTop (fun _ => (0 : HermitianSpace (d+1))) := by
  have heq (path : AdaptiveInfinitePath O) (n : ℕ) :
      rawEstimator P hI regularization hr batchSize path n =
      actualRidgeEstimate (adaptiveProtocol P hI regularization hr batchSize)
        (regressionFrame P) (responseVector P) regularization (coercivityConstant P hI)
        hr (coercivityConstant_pos P hI).le (regressionFrame_coercive P hI) path n := by
    exact SequentialRidgeController.pathState_estimate_eq_ridgeEstimate
      (regressionFrame P) (responseVector P) (physicalController d)
      (SequentialRidgeController.batchRefresh batchSize) regularization (coercivityConstant P hI)
      hr (coercivityConstant_pos P hI).le (regressionFrame_coercive P hI) path n
  simp_rw [heq]
  exact actualRidgeEstimate_quarterRate (adaptiveProtocol P hI regularization hr batchSize) truth
    (regressionFrame P) (responseVector P) (pureParameter d truth).val regularization
    (coercivityConstant P hI) hr (coercivityConstant_pos P hI) (regressionFrame_coercive P hI)
    (responseVector_mean P truth) (2 * responseBound P)
    (mul_nonneg (by norm_num) (responseBound_nonnegative P)) (responseInnovation_bound P truth)

theorem stateEstimator_quarterRate
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P)
    (regularization : ℝ) (hr : 0 < regularization) (batchSize : ℕ → ℕ) (truth : PureVector d) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth)
      (fun n path => quarterScale n •
        (stateEstimator P hI regularization hr batchSize path (n+1) - rankOneDensity truth.val))
      atTop (fun _ => (0 : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)) := by
  letI : TopologicalSpace (Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :=
    (inferInstance : NormedAddCommGroup (Matrix (Fin (d+1)) (Fin (d+1)) ℂ)).toUniformSpace.toTopologicalSpace
  let L : HermitianSpace (d+1) →L[ℝ] Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
    (toMatrixLinear (d+1)).toContinuousLinearMap
  have hraw := rawEstimator_quarterRate P hI regularization hr batchSize truth
  apply ProbabilityZeroAlgebra.dominated hraw (2 * (‖L‖+1)) (by positivity)
  intro n path
  have hp := projectedMatrix_error_le_two d truth
    (toMatrix (rawEstimator P hI regularization hr batchSize path (n+1)))
  have hl := L.le_opNorm (rawEstimator P hI regularization hr batchSize path (n+1) -
    (pureParameter d truth).val)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (quarterScale_pos n)]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (quarterScale_pos n)]
  change quarterScale n * ‖projectedMatrix d _ - rankOneDensity truth.val‖ ≤ _
  have hl' : ‖toMatrix (rawEstimator P hI regularization hr batchSize path (n+1)) - rankOneDensity truth.val‖ ≤
      ‖L‖ * ‖rawEstimator P hI regularization hr batchSize path (n+1) - (pureParameter d truth).val‖ := hl
  have h := mul_le_mul_of_nonneg_left (hp.trans (mul_le_mul_of_nonneg_left hl' (by norm_num)))
    (quarterScale_pos n).le
  nlinarith [norm_nonneg (rawEstimator P hI regularization hr batchSize path (n+1) -
    (pureParameter d truth).val), quarterScale_pos n]

end
end QubitOracle.AdaptiveDesign.GeneralPOVMQuarterRate
