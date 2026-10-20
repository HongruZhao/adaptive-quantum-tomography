-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMPilotMomentLimits
import QubitOracle.AdaptiveDesign.EfficientBornScoreCLT
import QubitOracle.AdaptiveDesign.FiniteAdaptiveResponseCLT

/-! The actual unweighted tangent score has the efficient Gaussian limit.
The bounded finite-response characteristic-function proof supplies the CLT
without any external statistical axiom. -/
namespace QubitOracle.AdaptiveDesign.PVMPilotGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian GlobalPFSICBorn
open PureMatrixController P2Adaptive TangentGLS PVMGeometry PVMPilotBorn
open PVMUniformMoments Filter MeasureTheory ProbabilityTheory AdaptiveRidgeConsistency
open scoped BigOperators InnerProductSpace Topology Matrix.Norms.Elementwise
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
variable [PVMPilotSchedule.Schedule]
variable {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d]

lemma basisProbability_le_one (theta : PhysicalParameter (d+1)) (U : Action d) (k : Fin (d+1)) :
    basisProbability theta U k ≤ 1 := by
  have h := Finset.single_le_sum (s:=Finset.univ) (fun k _ => basisProbability_nonnegative theta U k)
    (Finset.mem_univ k)
  simpa only [basisProbability_sum] using h

lemma scoreResponse_unweighted (truth : PureVector d) (a : ℕ × Action d) (o : Outcome d) :
    scoreResponse truth a o = centeredBasis (pureParameter d truth)
      (fun a b k => basisEffect (settingBasis a.2 b) k) a o := by
  simp only [scoreResponse, floor, denominator, max_eq_right (basisProbability_le_one _ _ _),
    inv_one, one_smul]

def coordinateScore (truth : PureVector d) (a : ℕ × Action d) (o : Outcome d) :
    EuclideanSpace ℝ (TangentIndex d) :=
  (2*(d+1:ℝ)) • trueCoordinate truth (scoreResponse truth a o)

lemma coordinateScore_mean (truth : PureVector d) (a : ℕ × Action d) :
    ∫ o, coordinateScore truth a o ∂bornKernel (pureParameter d truth) a=0 := by
  simp only [coordinateScore, integral_smul,
    (trueCoordinate truth).integral_comp_comm Integrable.of_finite, scoreResponse_mean, map_zero, smul_zero]

lemma coordinateScore_bound (truth : PureVector d) (a : ℕ × Action d) (o : Outcome d) :
    ‖coordinateScore truth a o‖ ≤ (2*(d+1:ℝ))*‖trueCoordinate truth‖*(2*basisBound d) := by
  rw [coordinateScore,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have h : ‖scoreResponse truth a o‖ ≤ 2*basisBound d := by
    simpa only [floor, inv_one, one_mul] using scoreResponse_bound truth a o
  calc
    _ ≤ (2*(d+1:ℝ))*(‖trueCoordinate truth‖*(2*basisBound d)) :=
      mul_le_mul_of_nonneg_left (((trueCoordinate truth).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left h (norm_nonneg _))) (by positivity)
    _ = _ := by ring

lemma quadratic_smul {I : Type} [Fintype I] (M : Matrix I I ℝ)
    (u : EuclideanSpace ℝ I) (c : ℝ) :
    martingaleScoreQuadraticForm (c • M) u = c*martingaleScoreQuadraticForm M u := by
  simp only [martingaleScoreQuadraticForm,Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]

lemma quadratic_sum {I J : Type} [Fintype I] [Fintype J]
    (M : J → Matrix I I ℝ) (u : EuclideanSpace ℝ I) :
    martingaleScoreQuadraticForm (∑ j, M j) u = ∑ j, martingaleScoreQuadraticForm (M j) u := by
  simp only [martingaleScoreQuadraticForm,Matrix.sum_mulVec,dotProduct_sum]

lemma quadratic_moment {I O : Type} [Fintype I] [Fintype O]
    (p : O → ℝ) (v : O → EuclideanSpace ℝ I) (u : EuclideanSpace ℝ I) :
    martingaleScoreQuadraticForm (fun i j => ∑ o, p o*(v o i*v o j)) u =
      ∑ o, p o*⟪u,v o⟫_ℝ^2 := by
  classical
  have he : (fun i j => ∑ o, p o*(v o i*v o j)) =
      ∑ o, p o • Matrix.vecMulVec (v o).ofLp (v o).ofLp := by
    ext i j
    simp only [Matrix.sum_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,smul_eq_mul]
  rw [he]
  simp only [martingaleScoreQuadraticForm,Matrix.sum_mulVec,dotProduct_sum,Matrix.smul_mulVec,
    dotProduct_smul,Matrix.vecMulVec_mulVec,EuclideanSpace.inner_eq_star_dotProduct,star_trivial,pow_two]
  apply Finset.sum_congr rfl
  intro o _
  change p o*((u.ofLp ⬝ᵥ (v o).ofLp)*((v o).ofLp ⬝ᵥ u.ofLp)) = _
  rw [dotProduct_comm u.ofLp (v o).ofLp]

lemma basisMoment_quadratic (B : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (u : EuclideanSpace ℝ (TangentIndex d)) :
    martingaleScoreQuadraticForm (basisMoment B) u =
      ∑ k, fixedChartBasisProbability B k *
        ⟪u, WithLp.toLp 2 (fixedChartBasisGradient B k)-
          ∑ l, fixedChartBasisProbability B l • WithLp.toLp 2 (fixedChartBasisGradient B l)⟫_ℝ^2 := by
  have hh := quadratic_moment (fixedChartBasisProbability B)
    (fun k => WithLp.toLp 2 (fixedChartBasisGradient B k)-
      ∑ l, fixedChartBasisProbability B l • WithLp.toLp 2 (fixedChartBasisGradient B l)) u
  convert hh using 1
  congr 1
  ext i j
  simp only [basisMoment,PiLp.sub_apply,WithLp.ofLp_sum,WithLp.ofLp_smul,
    WithLp.ofLp_toLp,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma coordinateScore_secondMoment (truth : PureVector d) (a : ℕ × Action d)
    (u : EuclideanSpace ℝ (TangentIndex d)) :
    ∫ o, ⟪u,coordinateScore truth a o⟫_ℝ^2 ∂bornKernel (pureParameter d truth) a =
      martingaleScoreQuadraticForm ((2*(d+1:ℝ))^2 • coordinateMoment truth a) u := by
  rw [integral_bornKernel,quadratic_smul,coordinateMoment,quadratic_sum]
  simp only [quadratic_smul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [basisMoment_quadratic]
  simp only [coordinateScore,scoreResponse_unweighted,centeredBasis,centeredLookup,map_sub,map_sum,map_smul,
    basis_coordinate,basis_probability_true,inner_smul_right,mul_pow,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma actual_score_secondMoment_limit (truth : PureVector d) (batchSize : ℕ → ℕ)
    (hpositive : ∀ j, 0 < batchSize j) (u : EuclideanSpace ℝ (TangentIndex d)) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth),
      Tendsto (fun k => AdaptiveConditionalMoments.secondMoment
        (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth) (coordinateScore truth) u
        ((PVMPilotAdaptive.adaptiveProtocol d batchSize).design (k+1)
          (adaptiveInfinitePathPrefix (k+1) path))) atTop
        (𝓝 (martingaleScoreQuadraticForm ((2:ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)) u)) := by
  filter_upwards [actual_moment_limits truth batchSize hpositive] with path hp
  have hcont : Continuous (fun M : Matrix (TangentIndex d) (TangentIndex d) ℝ =>
      martingaleScoreQuadraticForm M u) := by
    unfold martingaleScoreQuadraticForm Matrix.mulVec dotProduct
    fun_prop
  have hl := hcont.continuousAt.tendsto.comp (hp.2.const_smul ((2*(d+1:ℝ))^2))
  have he : (2*(d+1:ℝ))^2 • ((1/(2*(d+1:ℝ)^2)) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)) =
      (2:ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ) := by
    rw [smul_smul]
    congr 1
    field_simp
    <;> ring
  rw [he] at hl
  have heq k : AdaptiveConditionalMoments.secondMoment
      (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth) (coordinateScore truth) u
      ((PVMPilotAdaptive.adaptiveProtocol d batchSize).design (k+1) (adaptiveInfinitePathPrefix (k+1) path)) =
      martingaleScoreQuadraticForm ((2*(d+1:ℝ))^2 • coordinateMoment truth
        (k+1,(PVMPilotAdaptive.actualState d batchSize path (k+1)).action)) u :=
    coordinateScore_secondMoment truth _ u
  simp_rw [heq]
  exact hl.comp (tendsto_add_atTop_nat 1)

/-- The CLT input is proved from the actual adaptive protocol and the
finite PVM moment identities; no covariance limit is assumed. -/
theorem shifted_score_clt (truth : PureVector d) (batchSize : ℕ → ℕ)
    (hpositive : ∀ j, 0 < batchSize j) :
    (BoundedAdaptiveResponseCLT.problem (PVMPilotAdaptive.adaptiveProtocol d batchSize)
      (pureParameter d truth) (coordinateScore truth)).VectorSumConvergesToGaussian
      ((2:ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)) := by
  let C := (2*(d+1:ℝ))*‖trueCoordinate truth‖*(2*basisBound d)
  have hC : 0 ≤ C := by have hb := basisBound_nonnegative d; positivity
  apply FiniteAdaptiveCharacteristic.vector_clt_of_secondMoment_limit _ _ _ (coordinateScore_mean truth)
    C hC (coordinateScore_bound truth) _ (Matrix.PosDef.smul Matrix.PosDef.one (by norm_num))
  exact actual_score_secondMoment_limit truth batchSize hpositive

def fullScore (truth : PureVector d) (batchSize : ℕ → ℕ) (n : ℕ)
    (path : AdaptiveInfinitePath (PVMPilotAdaptive.PVMOutcome d)) : EuclideanSpace ℝ (TangentIndex d) :=
  (Real.sqrt (n:ℝ))⁻¹ • ∑ k ∈ Finset.range n, actualVectorResponse
    (PVMPilotAdaptive.adaptiveProtocol d batchSize) (coordinateScore truth) k path

lemma fullScore_measurable (truth : PureVector d) (batchSize : ℕ → ℕ) (n : ℕ) :
    Measurable (fullScore truth batchSize n) :=
  (Finset.measurable_sum (Finset.range n) (fun k _ =>
    BoundedAdaptiveResponseCLT.actualVectorResponse_measurable
      (PVMPilotAdaptive.adaptiveProtocol d batchSize) (coordinateScore truth) k)).const_smul ((Real.sqrt (n:ℝ))⁻¹)

lemma fullScore_clt (truth : PureVector d) (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    TendstoInDistribution (fullScore truth batchSize) atTop id
      (fun _ => adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth))
      (multivariateGaussian 0 ((2:ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) := by
  have hclt := shifted_score_clt truth batchSize hpositive
  dsimp only [MartingaleCLTProblem.VectorSumConvergesToGaussian,BoundedAdaptiveResponseCLT.problem] at hclt
  apply tendstoInDistribution_of_tendstoInMeasure_sub _ _ hclt _
    (fun n => (fullScore_measurable truth batchSize n).aemeasurable)
  let C := (2*(d+1:ℝ))*‖trueCoordinate truth‖*(2*basisBound d)
  have hb (k : ℕ) (path : AdaptiveInfinitePath (PVMPilotAdaptive.PVMOutcome d)) :
      ‖actualVectorResponse (PVMPilotAdaptive.adaptiveProtocol d batchSize) (coordinateScore truth) k path‖ ≤ C :=
    coordinateScore_bound truth _ _
  apply ProbabilityZeroAlgebra.uniform_norm_bound (fun n : ℕ => (2*C)/Real.sqrt (n:ℝ))
    (constant_div_sqrt_nat_tendsto_zero (2*C))
  intro n path
  change ‖(Real.sqrt (n:ℝ))⁻¹ • (∑ k ∈ Finset.range n, actualVectorResponse
      (PVMPilotAdaptive.adaptiveProtocol d batchSize) (coordinateScore truth) k path)-
    (∑ k ∈ Finset.range n, (Real.sqrt (n:ℝ))⁻¹ • actualVectorResponse
      (PVMPilotAdaptive.adaptiveProtocol d batchSize) (coordinateScore truth) (k+1) path)‖ ≤ _
  rw [← Finset.smul_sum,← smul_sub,EfficientBornScoreCLT.sum_endpoint_difference]
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hh := mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add (hb 0 path) (hb n path)))
    (show (0:ℝ)≤(Real.sqrt (n:ℝ))⁻¹ by positivity)
  exact hh.trans_eq (by ring)

lemma fullScore_eq_coordinate (truth : PureVector d) (batchSize : ℕ → ℕ) (n : ℕ)
    (path : AdaptiveInfinitePath (PVMPilotAdaptive.PVMOutcome d)) :
    fullScore truth batchSize n path = (2:ℝ) • trueCoordinate truth
      (((d+1:ℝ)/Real.sqrt (n:ℝ)) • tangentProjector truth (scoreSum truth batchSize n path)) := by
  simp only [fullScore,scoreSum,actualVectorResponse,coordinateScore,map_smul,map_sum,
    trueCoordinate_projection,← Finset.smul_sum,smul_smul,div_eq_mul_inv]
  module

end
end QubitOracle.AdaptiveDesign.PVMPilotGLS

-/
