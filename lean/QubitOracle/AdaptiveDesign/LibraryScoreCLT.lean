import QubitOracle.AdaptiveDesign.LibraryFrameLimit
import QubitOracle.AdaptiveDesign.AdaptiveConditionalMoments
import QubitOracle.AdaptiveDesign.AdaptiveRidgeConsistency
import QubitOracle.AdaptiveDesign.BoundedAdaptiveResponseCLT
import QubitOracle.AdaptiveDesign.EfficientBornScoreCLT
import QubitOracle.AdaptiveDesign.FiniteAdaptiveResponseCLT
import QubitOracle.AdaptiveDesign.GeneralPOVMBorn
import QubitOracle.AdaptiveDesign.GlobalPFSIC
import QubitOracle.AdaptiveDesign.GlobalPFSICBornModel
import QubitOracle.AdaptiveDesign.GlobalPFSICFisher
import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel
import QubitOracle.AdaptiveDesign.GlobalPFSICLibrary
import QubitOracle.AdaptiveDesign.GlobalPFSICTransport
import QubitOracle.AdaptiveDesign.LibraryUnweightedMoments
import QubitOracle.AdaptiveDesign.P2AdaptiveTheorem
import QubitOracle.AdaptiveDesign.ProbabilityZeroAlgebra
import QubitOracle.AdaptiveDesign.PureHermitianController
import QubitOracle.AdaptiveDesign.PureMatrixController
import QubitOracle.AdaptiveDesign.RidgeBatchSchedule
import QubitOracle.AdaptiveDesign.SequentialRidgeController
import QubitOracle.AdaptiveDesign.TangentGLSCoordinates
import QubitOracle.Paper.AdaptiveTrajectoryExperiment
import QubitOracle.Paper.FiniteAdaptiveBornScoreClosure
import QubitOracle.Paper.FiniteKernelPathSpace
import QubitOracle.Paper.MartingaleCLT
import QubitOracle.Paper.PureStateFoundations
import QubitOracle.TwoBasis
/-! The literal optional-library Born experiment supplies the Gaussian
limit for the unweighted tangent innovation, with its actual covariance. -/
namespace QubitOracle.AdaptiveDesign.LibraryUnweighted
open QubitOracle QubitOracle.Paper GlobalPFSIC GlobalPFSICHermitian GlobalPFSICBorn
open PureMatrixController P2Adaptive TangentGLS Filter MeasureTheory ProbabilityTheory
open AdaptiveRidgeConsistency
open scoped BigOperators Topology InnerProductSpace Matrix.Norms.Elementwise
noncomputable section
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

lemma quadratic_smul {I : Type} [Fintype I] (M : Matrix I I ℝ)
    (u : EuclideanSpace ℝ I) (c : ℝ) :
    martingaleScoreQuadraticForm (c • M) u = c*martingaleScoreQuadraticForm M u := by
  simp only [martingaleScoreQuadraticForm,Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]

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

lemma actual_ray_limit {d : ℕ} (hd : 0 < d) (truth : PureVector d)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol hd batchSize) (pureParameter d truth),
      Tendsto (fun n => frameProjector (measurementFrame hd batchSize path n)) atTop
        (𝓝 (rankOneDensity truth.val)) := by
  filter_upwards [rawEstimator_consistent hd batchSize (pureParameter d truth)] with path hraw
  have hfrozen := SequentialRidgeController.consistent_estimate_at_batch_refresh
    (rawEstimator hd batchSize path) (pureParameter d truth).1 hraw batchSize hpositive
  simp only [measurementFrame_eq_frozenController, frameProjector]
  exact hermitianController_firstProjector_tendsto d truth (pureParameter d truth).1 rfl _ hfrozen

lemma actual_moment_limit {d : ℕ} (hd : 0 < d) (truth : PureVector d)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol hd batchSize) (pureParameter d truth),
      Tendsto (fun n => moment ((trueFrame d truth).conjTranspose*measurementFrame hd batchSize path n))
        atTop (𝓝 ((noiseConstant d/2) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) := by
  filter_upwards [actual_ray_limit hd truth batchSize hpositive] with path hp
  rw [← trueFrame_projector d truth] at hp
  exact (moment_limits hd _
    (fun n => relative_unitary _ _ (trueFrame_unitary d truth) (measurementFrame_unitary hd batchSize path n))
    (relative_overlap_tendsto _ (trueFrame_unitary d truth) _ hp)).2

lemma probability_coordinate {d : ℕ} (hd : 0 < d) (truth : PureVector d)
    (U : Action d) (o : Outcome d) :
    bornProbability hd (pureParameter d truth) U o =
      transportedMass ((trueFrame d truth).conjTranspose*U.matrix) o :=
  GeneralPOVM.bornProbability_pure_eq_mass (measurementPOVM d hd) truth U o

lemma effect_coordinate {d : ℕ} (hd : 0 < d) (truth : PureVector d)
    (U : Action d) (o : Outcome d) :
    trueCoordinate truth (responseVector hd U o) =
      WithLp.toLp 2 (transportedGradient ((trueFrame d truth).conjTranspose*U.matrix) o) :=
  trueCoordinate_responseVector (measurementPOVM d hd) truth U o

def innovation {d : ℕ} (hd : 0 < d) (truth : PureVector d) (U : Action d) (o : Outcome d) :=
  responseVector hd U o-regressionFrame hd U (pureParameter d truth).val

def scoreResponse {d : ℕ} (hd : 0 < d) (truth : PureVector d) (U : Action d) (o : Outcome d) :=
  (2/gramConstant d) • trueCoordinate truth (innovation hd truth U o)

lemma innovation_mean {d : ℕ} (hd : 0 < d) (truth : PureVector d) (U : Action d) :
    ∫ o, innovation hd truth U o ∂bornKernel hd (pureParameter d truth) U = 0 := by
  simp only [innovation]
  rw [integral_sub Integrable.of_finite (integrable_const _), responseVector_mean]
  simp

lemma scoreResponse_mean {d : ℕ} (hd : 0 < d) (truth : PureVector d) (U : Action d) :
    ∫ o, scoreResponse hd truth U o ∂bornKernel hd (pureParameter d truth) U = 0 := by
  simp only [scoreResponse, integral_smul,
    (trueCoordinate truth).integral_comp_comm Integrable.of_finite, innovation_mean, map_zero, smul_zero]

def scoreBound {d : ℕ} (hd : 0 < d) (truth : PureVector d) : ℝ :=
  |2/gramConstant d| * ‖trueCoordinate truth‖*(2*responseBound hd)

lemma scoreBound_nonnegative {d : ℕ} (hd : 0 < d) (truth : PureVector d) :
    0 ≤ scoreBound hd truth := by
  have h := responseBound_nonnegative hd
  unfold scoreBound
  positivity

lemma scoreResponse_bound {d : ℕ} (hd : 0 < d) (truth : PureVector d) (U : Action d) (o : Outcome d) :
    ‖scoreResponse hd truth U o‖ ≤ scoreBound hd truth := by
  rw [scoreResponse, norm_smul, Real.norm_eq_abs]
  have hh := mul_le_mul_of_nonneg_left
    (((trueCoordinate truth).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (responseInnovation_bound hd (pureParameter d truth) U o)
        (norm_nonneg _))) (abs_nonneg (2/gramConstant d))
  exact hh.trans_eq (by unfold scoreBound; ring)

lemma score_secondMoment {d : ℕ} (hd : 0 < d) (truth : PureVector d) (U : Action d)
    (u : EuclideanSpace ℝ (TangentIndex d)) :
    ∫ o, ⟪u, scoreResponse hd truth U o⟫_ℝ^2 ∂bornKernel hd (pureParameter d truth) U =
      martingaleScoreQuadraticForm ((2/gramConstant d)^2 •
        moment ((trueFrame d truth).conjTranspose*U.matrix)) u := by
  change (∫ o, ⟪u, scoreResponse hd truth U o⟫_ℝ^2 ∂finiteMassMeasure
    (bornProbability hd (pureParameter d truth) U)
    (bornProbability_nonnegative hd (pureParameter d truth) U)
    (bornProbability_sum hd (pureParameter d truth) U)) = _
  rw [integral_finiteMassMeasure, quadratic_smul]
  have hh := quadratic_moment
    (transportedMass ((trueFrame d truth).conjTranspose*U.matrix))
    (fun o => WithLp.toLp 2 (transportedGradient ((trueFrame d truth).conjTranspose*U.matrix) o)-
      WithLp.toLp 2 (mean ((trueFrame d truth).conjTranspose*U.matrix))) u
  have hm : moment ((trueFrame d truth).conjTranspose*U.matrix) =
      (fun i j => ∑ o, transportedMass ((trueFrame d truth).conjTranspose*U.matrix) o*
        ((WithLp.toLp 2 (transportedGradient ((trueFrame d truth).conjTranspose*U.matrix) o)-
          WithLp.toLp 2 (mean ((trueFrame d truth).conjTranspose*U.matrix))) i*
         (WithLp.toLp 2 (transportedGradient ((trueFrame d truth).conjTranspose*U.matrix) o)-
          WithLp.toLp 2 (mean ((trueFrame d truth).conjTranspose*U.matrix))) j)) := rfl
  rw [hm, hh, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro o _
  have hc : trueCoordinate truth (regressionFrame hd U (pureParameter d truth).val) =
      WithLp.toLp 2 (mean ((trueFrame d truth).conjTranspose*U.matrix)) := by
    change trueCoordinate truth (∑ y, bornProbability hd (pureParameter d truth) U y • responseVector hd U y) = _
    simp only [map_sum, ContinuousLinearMap.map_smul, probability_coordinate, effect_coordinate]
    ext x
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mean]
  simp only [scoreResponse, innovation, map_sub, hc, effect_coordinate, probability_coordinate,
    inner_smul_right, mul_pow, smul_eq_mul]
  ring

lemma scaled_noise_constant {d : ℕ} (hd : 0 < d) :
    (2/gramConstant d)^2*(noiseConstant d/2) = 2*tangentVariance d := by
  rw [← variance_ratio hd]
  ring

theorem shifted_score_clt {d : ℕ} (hd : 0 < d) (truth : PureVector d)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    (BoundedAdaptiveResponseCLT.problem (adaptiveProtocol hd batchSize)
      (pureParameter d truth) (scoreResponse hd truth)).VectorSumConvergesToGaussian
        ((2*tangentVariance d) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)) := by
  letI : Nonempty (Outcome d) := ⟨(false,0,Sum.inl ⟨0,hd⟩)⟩
  have hv : 0 < 2*tangentVariance d := by
    rw [← variance_ratio hd]
    exact mul_pos (by norm_num) (div_pos (constants_positive hd).2 (sq_pos_of_pos (constants_positive hd).1))
  apply FiniteAdaptiveCharacteristic.vector_clt_of_secondMoment_limit _ _ _ (scoreResponse_mean hd truth)
    (scoreBound hd truth) (scoreBound_nonnegative hd truth) (scoreResponse_bound hd truth) _
    (Matrix.PosDef.smul Matrix.PosDef.one hv)
  intro u
  filter_upwards [actual_moment_limit hd truth batchSize hpositive] with path hp
  have hc : Continuous (fun M : Matrix (TangentIndex d) (TangentIndex d) ℝ =>
      martingaleScoreQuadraticForm M u) := by
    unfold martingaleScoreQuadraticForm Matrix.mulVec dotProduct
    fun_prop
  have hh := hc.continuousAt.tendsto.comp (hp.const_smul ((2/gramConstant d)^2))
  rw [smul_smul, scaled_noise_constant hd] at hh
  have heq (k : ℕ) : AdaptiveConditionalMoments.secondMoment
      (adaptiveProtocol hd batchSize) (pureParameter d truth) (scoreResponse hd truth) u
      ((adaptiveProtocol hd batchSize).design (k+1) (adaptiveInfinitePathPrefix (k+1) path)) =
        martingaleScoreQuadraticForm ((2/gramConstant d)^2 •
          moment ((trueFrame d truth).conjTranspose*measurementFrame hd batchSize path (k+1))) u :=
    score_secondMoment hd truth _ u
  simp_rw [heq]
  exact hh.comp (tendsto_add_atTop_nat 1)

def fullScore {d : ℕ} (hd : 0 < d) (truth : PureVector d) (batchSize : ℕ → ℕ) (n : ℕ)
    (path : AdaptiveInfinitePath (Outcome d)) : EuclideanSpace ℝ (TangentIndex d) :=
  (Real.sqrt (n:ℝ))⁻¹ • ∑ k ∈ Finset.range n, actualVectorResponse
    (adaptiveProtocol hd batchSize) (scoreResponse hd truth) k path

lemma fullScore_measurable {d : ℕ} (hd : 0 < d) (truth : PureVector d) (batchSize : ℕ → ℕ) (n : ℕ) :
    Measurable (fullScore hd truth batchSize n) := by
  letI : Nonempty (Outcome d) := ⟨(false,0,Sum.inl ⟨0,hd⟩)⟩
  exact (Finset.measurable_sum (Finset.range n) (fun k _ =>
    BoundedAdaptiveResponseCLT.actualVectorResponse_measurable
      (adaptiveProtocol hd batchSize) (scoreResponse hd truth) k)).const_smul ((Real.sqrt (n:ℝ))⁻¹)

theorem fullScore_clt {d : ℕ} (hd : 0 < d) (truth : PureVector d) (batchSize : ℕ → ℕ)
    (hpositive : ∀ j, 0 < batchSize j) :
    TendstoInDistribution (fullScore hd truth batchSize) atTop id
      (fun _ => adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol hd batchSize) (pureParameter d truth))
      (multivariateGaussian 0 ((2*tangentVariance d) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) := by
  letI : Nonempty (Outcome d) := ⟨(false,0,Sum.inl ⟨0,hd⟩)⟩
  have hclt := shifted_score_clt hd truth batchSize hpositive
  dsimp only [MartingaleCLTProblem.VectorSumConvergesToGaussian,BoundedAdaptiveResponseCLT.problem] at hclt
  apply tendstoInDistribution_of_tendstoInMeasure_sub _ _ hclt _
    (fun n => (fullScore_measurable hd truth batchSize n).aemeasurable)
  apply ProbabilityZeroAlgebra.uniform_norm_bound (fun n : ℕ => (2*scoreBound hd truth)/Real.sqrt (n:ℝ))
    (constant_div_sqrt_nat_tendsto_zero (2*scoreBound hd truth))
  intro n path
  change ‖(Real.sqrt (n:ℝ))⁻¹ • (∑ k ∈ Finset.range n, actualVectorResponse
      (adaptiveProtocol hd batchSize) (scoreResponse hd truth) k path)-
    (∑ k ∈ Finset.range n, (Real.sqrt (n:ℝ))⁻¹ • actualVectorResponse
      (adaptiveProtocol hd batchSize) (scoreResponse hd truth) (k+1) path)‖ ≤ _
  rw [← Finset.smul_sum, ← smul_sub, EfficientBornScoreCLT.sum_endpoint_difference,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hb (k : ℕ) : ‖actualVectorResponse (adaptiveProtocol hd batchSize)
      (scoreResponse hd truth) k path‖ ≤ scoreBound hd truth := scoreResponse_bound hd truth _ _
  have hh := mul_le_mul_of_nonneg_left
    ((norm_sub_le _ _).trans (add_le_add (hb 0) (hb n)))
    (show (0:ℝ) ≤ (Real.sqrt (n:ℝ))⁻¹ by positivity)
  exact hh.trans_eq (by ring)

end
end QubitOracle.AdaptiveDesign.LibraryUnweighted
