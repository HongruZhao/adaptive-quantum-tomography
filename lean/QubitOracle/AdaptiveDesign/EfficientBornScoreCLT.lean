import QubitOracle.AdaptiveDesign.ProtectedBornScore
import QubitOracle.AdaptiveDesign.TangentGLSCoordinates
import QubitOracle.AdaptiveDesign.ProbabilityZeroAlgebra
import QubitOracle.AdaptiveDesign.FiniteAdaptiveResponseCLT

/-! The correctly normalized efficient score has covariance 2 I, including
all records numbered 0 through n-1. The Gaussian limit follows
from the direct bounded finite-response characteristic-function proof. -/
namespace QubitOracle.AdaptiveDesign.EfficientBornScoreCLT
open QubitOracle QubitOracle.Paper PureMatrixController P2Adaptive GeneralPOVM
open Filter MeasureTheory ProbabilityTheory AdaptiveRidgeConsistency
open scoped BigOperators Topology InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {d : ℕ} {O : Type} [Fintype O]
  [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]

def response (P : FinitePOVM (Fin (d+1)) O) (truth : PureVector d) (floor : ℝ)
    (U : GlobalPFSICBorn.Action d) (y : O) : EuclideanSpace ℝ (TangentIndex d) :=
  (2 : ℝ) • ProtectedBornScore.response P truth floor U y

theorem half_quadratic_double (u : EuclideanSpace ℝ (TangentIndex d)) :
    martingaleScoreQuadraticForm ((1/2 : ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)) ((2 : ℝ) • u) =
    martingaleScoreQuadraticForm ((2 : ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)) u := by
  simp only [martingaleScoreQuadraticForm, Matrix.smul_mulVec, Matrix.one_mulVec,
    PiLp.smul_apply, Pi.smul_apply, smul_eq_mul, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem shifted_clt
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P) (hF : FisherSymmetric P)
    (truth : PureVector d) (regularization : ℝ) (hr : 0 < regularization)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    (BoundedAdaptiveResponseCLT.problem (adaptiveProtocol P hI regularization hr batchSize) truth
      (response P truth (TangentGLS.referenceFloor P))).VectorSumConvergesToGaussian
      ((2 : ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)) := by
  obtain ⟨C,hC,hb⟩ := ProtectedBornScore.response_bounded P truth (TangentGLS.referenceFloor P)
    (TangentGLS.referenceFloor_pos P hp)
  have hb' (U : GlobalPFSICBorn.Action d) (y : O) :
      ‖response P truth (TangentGLS.referenceFloor P) U y‖ ≤ 2*C := by
    simpa only [response,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)] using
      mul_le_mul_of_nonneg_left (hb U y) (by norm_num : (0:ℝ)≤2)
  have hm (U : GlobalPFSICBorn.Action d) :
      ∫ y, response P truth (TangentGLS.referenceFloor P) U y ∂bornKernel P truth U = 0 := by
    change ∫ y, (2 : ℝ) • ProtectedBornScore.response P truth (TangentGLS.referenceFloor P) U y ∂bornKernel P truth U = 0
    rw [integral_smul, ProtectedBornScore.response_mean_zero, smul_zero]
  apply FiniteAdaptiveCharacteristic.vector_clt_of_secondMoment_limit _ _ _ hm (2*C) (by positivity) hb' _
    (Matrix.PosDef.smul Matrix.PosDef.one (by norm_num))
  intro u
  have hh := ProtectedBornScore.actual_secondMoment_limit P hI hF truth (TangentGLS.referenceFloor P)
    (TangentGLS.referenceFloor_pos P hp) (ProtectedBornScore.referenceFloor_le P hp)
    regularization hr batchSize hpositive ((2 : ℝ) • u)
  rw [half_quadratic_double] at hh
  simpa only [AdaptiveConditionalMoments.secondMoment, response, inner_smul_right,
    inner_smul_left, conj_trivial] using hh

def fullScore (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P)
    (truth : PureVector d) (regularization : ℝ) (hr : 0 < regularization) (batchSize : ℕ → ℕ)
    (n : ℕ) (path : AdaptiveInfinitePath O) : EuclideanSpace ℝ (TangentIndex d) :=
  (Real.sqrt (n : ℝ))⁻¹ • ∑ k ∈ Finset.range n, actualVectorResponse
    (adaptiveProtocol P hI regularization hr batchSize) (response P truth (TangentGLS.referenceFloor P)) k path

theorem sum_endpoint_difference {E : Type*} [AddCommGroup E] (f : ℕ → E) (n : ℕ) :
    (∑ k ∈ Finset.range n, f k) - (∑ k ∈ Finset.range n, f (k+1)) = f 0-f n := by
  have h := (Finset.sum_range_succ f n).symm.trans (Finset.sum_range_succ' f n)
  apply sub_eq_sub_iff_add_eq_add.mpr
  simpa only [add_comm] using h

theorem fullScore_measurable
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P)
    (truth : PureVector d) (regularization : ℝ) (hr : 0 < regularization) (batchSize : ℕ → ℕ) (n : ℕ) :
    Measurable (fullScore P hI truth regularization hr batchSize n) := by
  exact (Finset.measurable_sum (Finset.range n) (fun k _ =>
    BoundedAdaptiveResponseCLT.actualVectorResponse_measurable
      (adaptiveProtocol P hI regularization hr batchSize) (response P truth (TangentGLS.referenceFloor P)) k)).const_smul ((Real.sqrt (n : ℝ))⁻¹)

theorem fullScore_clt
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P) (hF : FisherSymmetric P)
    (truth : PureVector d) (regularization : ℝ) (hr : 0 < regularization)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    TendstoInDistribution (fullScore P hI truth regularization hr batchSize) atTop id
      (fun _ => adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth)
      (multivariateGaussian 0 ((2 : ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) := by
  have hclt := shifted_clt P hI hp hF truth regularization hr batchSize hpositive
  dsimp only [MartingaleCLTProblem.VectorSumConvergesToGaussian, BoundedAdaptiveResponseCLT.problem] at hclt
  apply tendstoInDistribution_of_tendstoInMeasure_sub _ _ hclt _
    (fun n => (fullScore_measurable P hI truth regularization hr batchSize n).aemeasurable)
  obtain ⟨C,hC,hb⟩ := ProtectedBornScore.response_bounded P truth (TangentGLS.referenceFloor P)
    (TangentGLS.referenceFloor_pos P hp)
  apply ProbabilityZeroAlgebra.uniform_norm_bound (fun n : ℕ => (4*C)/Real.sqrt (n : ℝ))
    (constant_div_sqrt_nat_tendsto_zero (4*C))
  intro n path
  change ‖(Real.sqrt (n : ℝ))⁻¹ • (∑ k ∈ Finset.range n, actualVectorResponse (adaptiveProtocol P hI regularization hr batchSize)
      (response P truth (TangentGLS.referenceFloor P)) k path) -
    (∑ k ∈ Finset.range n, (Real.sqrt (n : ℝ))⁻¹ • actualVectorResponse (adaptiveProtocol P hI regularization hr batchSize)
      (response P truth (TangentGLS.referenceFloor P)) (k+1) path)‖ ≤ _
  rw [← Finset.smul_sum, ← smul_sub, sum_endpoint_difference]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hbound (k : ℕ) : ‖actualVectorResponse
      (adaptiveProtocol P hI regularization hr batchSize) (response P truth (TangentGLS.referenceFloor P)) k path‖ ≤ 2*C := by
    dsimp only [actualVectorResponse,response]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact mul_le_mul_of_nonneg_left (hb _ _) (by norm_num)
  have hh := mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add (hbound 0) (hbound n)))
    (show (0 : ℝ) ≤ (Real.sqrt (n : ℝ))⁻¹ by positivity)
  exact hh.trans_eq (by ring)

end
end QubitOracle.AdaptiveDesign.EfficientBornScoreCLT
