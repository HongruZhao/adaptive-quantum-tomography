import QubitOracle.AdaptiveDesign.AdaptiveRidgeConsistency
import QubitOracle.AdaptiveDesign.BoundedAdaptiveResponseCLT
import QubitOracle.AdaptiveDesign.P1BoundedResponseCLT
import QubitOracle.AdaptiveDesign.P1CharacteristicBounds
import QubitOracle.AdaptiveDesign.P1ObservedRidge
import QubitOracle.AdaptiveDesign.P1WeightedBorn
import QubitOracle.AdaptiveDesign.P1WeightedController
import QubitOracle.AdaptiveDesign.P1WeightedCovariance
import QubitOracle.AdaptiveDesign.P1WeightedGeometry
import QubitOracle.AdaptiveDesign.P1WeightedLimits
import QubitOracle.AdaptiveDesign.P1WeightedMoments
import QubitOracle.AdaptiveDesign.P1WeightedPolicy
import QubitOracle.AdaptiveDesign.ProbabilityZeroAlgebra
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.AdaptiveTrajectoryExperiment
import QubitOracle.Paper.FiniteAdaptiveBornScoreClosure
import QubitOracle.Paper.MartingaleCLT
import QubitOracle.Paper.MixedProbabilityFloor
import QubitOracle.Paper.OneQubitCyclicBornPath
import QubitOracle.Paper.OneQubitLabeledThreeAxisBornKernel
/-! The efficient influence-sum CLT for the actual P1 experiment. -/
namespace QubitOracle.AdaptiveDesign.P1Weighted
open QubitOracle QubitOracle.Paper Filter MeasureTheory ProbabilityTheory
open AdaptiveRidgeConsistency
open scoped BigOperators Topology InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
local instance : MeasurableSpace LabeledBinaryOutcome := ⊤
local instance : Nonempty LabeledBinaryOutcome := ⟨(0, .plus)⟩

def matrixMap (A : Mat) : Vector →L[ℝ] Vector := A.toEuclideanLin.toContinuousLinearMap

theorem residual_outer_mean (θ : OneQubitPhysicalParameter) (a : Action) :
    noiseCovariance θ.1 a = ∑ z, probability θ a z • blochOuter (fun i => residual θ.1 a z i) := by
  ext i j
  rw [← residual_second_moment,integral_eq_sum]
  simp [Matrix.sum_apply,Matrix.smul_apply,blochOuter]

theorem residual_quadratic_mean (θ : OneQubitPhysicalParameter) (a : Action) (u : Vector) :
    ∫ z, ⟪u,residual θ.1 a z⟫_ℝ^2 ∂kernel θ a =
      martingaleScoreQuadraticForm (noiseCovariance θ.1 a) u := by
  rw [integral_eq_sum,residual_outer_mean]
  change _ = quadratic _ u.ofLp
  rw [quadratic_sum]
  simp only [quadratic_smul,quadratic_outer,EuclideanSpace.inner_eq_star_dotProduct,star_trivial,
    blochDot,dotProduct]

theorem matrixMap_inner (A : Mat) (u x : Vector) :
    ⟪u,matrixMap A x⟫_ℝ = ⟪matrixMap A.transpose u,x⟫_ℝ := by
  simp [matrixMap,Matrix.toEuclideanLin_apply,EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  ring

theorem quadratic_conjugate (A V : Mat) (u : Vector) :
    martingaleScoreQuadraticForm V (matrixMap A.transpose u) =
      martingaleScoreQuadraticForm (A*V*A.transpose) u := by
  simp [martingaleScoreQuadraticForm,matrixMap,Matrix.toEuclideanLin_apply,
    Matrix.mulVec,Matrix.mul_apply,dotProduct,Fin.sum_univ_succ]
  ring

def influence (loss : Loss) (θ : Fin 3 → ℝ) (a : Action) (z : LabeledBinaryOutcome) : Vector :=
  matrixMap (meanGramTarget loss θ)⁻¹ (residual θ a z)

theorem influence_mean (loss : Loss) (θ : OneQubitPhysicalParameter) (a : Action) :
    ∫ z, influence loss θ.1 a z ∂kernel θ a = 0 := by
  change ∫ z, matrixMap (meanGramTarget loss θ.1)⁻¹ (residual θ.1 a z) ∂kernel θ a = 0
  rw [(matrixMap _).integral_comp_comm Integrable.of_finite,residual_mean,map_zero]

theorem influence_bound (loss : Loss) (θ : OneQubitPhysicalParameter) (a : Action) (z : LabeledBinaryOutcome) :
    ‖influence loss θ.1 a z‖ ≤ ‖matrixMap (meanGramTarget loss θ.1)⁻¹‖*6 :=
  ((matrixMap _).le_opNorm _).trans (mul_le_mul_of_nonneg_left (residual_bound θ a z) (norm_nonneg _))

theorem influence_secondMoment (loss : Loss) (θ : OneQubitPhysicalParameter) (a : Action) (u : Vector) :
    ∫ z, ⟪u,influence loss θ.1 a z⟫_ℝ^2 ∂kernel θ a =
      martingaleScoreQuadraticForm
        ((meanGramTarget loss θ.1)⁻¹ * noiseCovariance θ.1 a * ((meanGramTarget loss θ.1)⁻¹).transpose) u := by
  simp_rw [influence,matrixMap_inner]
  rw [residual_quadratic_mean,quadratic_conjugate]

theorem meanGram_inv_transpose (loss : Loss) (θ : Fin 3 → ℝ) (hθ : blochNormSq θ < 1) :
    ((meanGramTarget loss θ)⁻¹).transpose = (meanGramTarget loss θ)⁻¹ := by
  simpa only [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial] using
    (meanGram_posDef loss θ hθ).inv.isHermitian

theorem influence_shifted_clt (loss : Loss) (ridge : ℝ) (hr : 0 < ridge)
    (refresh : ℕ → Bool) (hrefresh : ∀ K, ∃ n, K ≤ n ∧ refresh n = true)
    (θ : OneQubitPhysicalParameter) (hθ : blochNormSq θ.1 < 1) :
    (BoundedAdaptiveResponseCLT.problem (protocol (policy loss ridge refresh)) θ
      (influence loss θ.1)).VectorSumConvergesToGaussian (covarianceTarget loss θ.1) := by
  apply bounded_response_vector_clt _ _ _ (influence_mean loss θ) _ (by positivity)
    (influence_bound loss θ) _ (covariance_posDef loss θ.1 hθ)
  intro u
  filter_upwards [noise_current_tendsto loss ridge hr refresh hrefresh θ hθ] with path hp
  have hcont : Continuous (fun V : Mat => martingaleScoreQuadraticForm
      ((meanGramTarget loss θ.1)⁻¹ * V * ((meanGramTarget loss θ.1)⁻¹).transpose) u) := by
    unfold martingaleScoreQuadraticForm Matrix.mulVec dotProduct
    fun_prop
  have hh := hcont.continuousAt.tendsto.comp (hp.comp (tendsto_add_atTop_nat 1))
  rw [meanGram_inv_transpose loss θ.1 hθ,inverse_sandwich loss θ.1 hθ] at hh
  have he : ∀ a, responseVariance θ (fun a z => ⟪u,influence loss θ.1 a z⟫_ℝ) a =
      martingaleScoreQuadraticForm
        ((meanGramTarget loss θ.1)⁻¹ * noiseCovariance θ.1 a * ((meanGramTarget loss θ.1)⁻¹).transpose) u := by
    intro a
    rw [← influence_secondMoment,integral_eq_sum]
    rfl
  simpa only [he,Function.comp_def,meanGram_inv_transpose loss θ.1 hθ] using hh

def influenceSum (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool) (θ : Fin 3 → ℝ)
    (n : ℕ) (path : Path) : Vector :=
  (Real.sqrt (n:ℝ))⁻¹ • ∑ t ∈ Finset.range n,
    influence loss θ (actualAction (policy loss ridge refresh) t path) (path t)

theorem influenceSum_measurable (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool) (θ : Fin 3 → ℝ) (n : ℕ) :
    Measurable (influenceSum loss ridge refresh θ n) := by
  exact (Finset.measurable_sum (Finset.range n) (fun k _ =>
    BoundedAdaptiveResponseCLT.actualVectorResponse_measurable
      (protocol (policy loss ridge refresh)) (influence loss θ) k)).const_smul ((Real.sqrt (n:ℝ))⁻¹)

theorem sum_endpoint_difference {E : Type*} [AddCommGroup E] (f : ℕ → E) (n : ℕ) :
    (∑ k ∈ Finset.range n, f k) - (∑ k ∈ Finset.range n, f (k+1)) = f 0-f n := by
  have h := (Finset.sum_range_succ f n).symm.trans (Finset.sum_range_succ' f n)
  apply sub_eq_sub_iff_add_eq_add.mpr
  simpa only [add_comm] using h

theorem influenceSum_clt (loss : Loss) (ridge : ℝ) (hr : 0 < ridge)
    (refresh : ℕ → Bool) (hrefresh : ∀ K, ∃ n, K ≤ n ∧ refresh n = true)
    (θ : OneQubitPhysicalParameter) (hθ : blochNormSq θ.1 < 1) :
    TendstoInDistribution (influenceSum loss ridge refresh θ.1) atTop id
      (fun _ => adaptiveInfiniteTrajectoryMeasure (protocol (policy loss ridge refresh)) θ)
      (multivariateGaussian 0 (covarianceTarget loss θ.1)) := by
  have hc := influence_shifted_clt loss ridge hr refresh hrefresh θ hθ
  dsimp only [MartingaleCLTProblem.VectorSumConvergesToGaussian,BoundedAdaptiveResponseCLT.problem] at hc
  apply tendstoInDistribution_of_tendstoInMeasure_sub _ _ hc _
    (fun n => (influenceSum_measurable loss ridge refresh θ.1 n).aemeasurable)
  let C := ‖matrixMap (meanGramTarget loss θ.1)⁻¹‖*6
  apply ProbabilityZeroAlgebra.uniform_norm_bound (fun n : ℕ => (2*C)/Real.sqrt (n:ℝ))
    (constant_div_sqrt_nat_tendsto_zero (2*C))
  intro n path
  change ‖(Real.sqrt (n:ℝ))⁻¹ • (∑ k ∈ Finset.range n,
    influence loss θ.1 (actualAction (policy loss ridge refresh) k path) (path k)) -
    (∑ k ∈ Finset.range n, (Real.sqrt (n:ℝ))⁻¹ •
      influence loss θ.1 (actualAction (policy loss ridge refresh) (k+1) path) (path (k+1)))‖ ≤ _
  rw [← Finset.smul_sum,← smul_sub,sum_endpoint_difference,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  have hb := (norm_sub_le _ _).trans (add_le_add
    (influence_bound loss θ (actualAction (policy loss ridge refresh) 0 path) (path 0))
    (influence_bound loss θ (actualAction (policy loss ridge refresh) n path) (path n)))
  have hh := mul_le_mul_of_nonneg_left hb (show (0:ℝ)≤(Real.sqrt (n:ℝ))⁻¹ by positivity)
  exact hh.trans_eq (by dsimp [C]; ring)

end
end QubitOracle.AdaptiveDesign.P1Weighted
