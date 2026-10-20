import QubitOracle.AdaptiveDesign.AdaptiveResponseMoments
import QubitOracle.AdaptiveDesign.P1ControllerFourthMoment
import QubitOracle.AdaptiveDesign.P1GaussianQuadratic
import QubitOracle.AdaptiveDesign.P1ObservedRidge
import QubitOracle.AdaptiveDesign.P1WeightedBorn
import QubitOracle.AdaptiveDesign.P1WeightedController
import QubitOracle.AdaptiveDesign.P1WeightedCovariance
import QubitOracle.AdaptiveDesign.P1WeightedEndpoints
import QubitOracle.AdaptiveDesign.P1WeightedGeometry
import QubitOracle.AdaptiveDesign.P1WeightedOptimality
import QubitOracle.AdaptiveDesign.P1WeightedPolicy
import QubitOracle.AdaptiveDesign.WeakMeanLossTransfer
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.AdaptiveTrajectoryExperiment
import QubitOracle.Paper.MixedProbabilityFloor
import QubitOracle.Paper.MixedRotationalTarget
import QubitOracle.Paper.OneQubitCyclicBornPath
import QubitOracle.Paper.OneQubitLabeledThreeAxisBornKernel
import QubitOracle.Paper.QubitFoundations
/-! Expected quadratic loss for the actual mixed-qubit physical
estimator. Uniform integrability is derived from its fourth moment. -/
namespace QubitOracle.AdaptiveDesign.P1Weighted
open QubitOracle QubitOracle.Paper MeasureTheory ProbabilityTheory Filter AdaptiveResponseMoments
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
local instance P1QuadraticMeanLoss_measurable : MeasurableSpace LabeledBinaryOutcome := ⊤
local instance P1QuadraticMeanLoss_nonempty : Nonempty LabeledBinaryOutcome := ⟨(0,.plus)⟩

theorem quadratic_smul_vector (W : Mat) (a : ℝ) (x : Fin 3 → ℝ) :
    quadratic W (a • x)=a^2*quadratic W x := by
  simp [quadratic,Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  ring

theorem quadratic_nonneg (W : Mat) (hW : W.PosSemidef) (x : Fin 3 → ℝ) :
    0 ≤ quadratic W x := by
  simpa only [quadratic,star_trivial] using hW.dotProduct_mulVec_nonneg x

theorem physical_quadratic_mean (loss : Loss) (ridge : ℝ) (hr : 0 < ridge)
    (refresh : ℕ → Bool) (hrefresh : ∀ K, ∃ n, K ≤ n ∧ refresh n=true)
    (θ : OneQubitPhysicalParameter) (hθ : blochNormSq θ.1 < 1) (W : Mat) (hW : W.PosSemidef) :
    Tendsto (fun n : ℕ => (n:ℝ)*∫ path,
      quadratic W (controller loss n (estimate loss ridge refresh n path)-θ.1)
      ∂adaptiveInfiniteTrajectoryMeasure (protocol (policy loss ridge refresh)) θ)
      atTop (𝓝 ((W*covarianceTarget loss θ.1).trace)) := by
  let μ := adaptiveInfiniteTrajectoryMeasure (protocol (policy loss ridge refresh)) θ
  let ν := multivariateGaussian (0:Vector) (covarianceTarget loss θ.1)
  let X := fun n path => quadratic W (controllerError loss ridge refresh θ.1 n path).ofLp
  let Z := fun z : Vector => quadratic W z.ofLp
  have hw : TendstoInDistribution X atTop Z (fun _ => μ) ν :=
    (controller_normal loss ridge hr refresh hrefresh θ hθ).continuous_comp
      (g:=fun z : Vector => quadratic W z.ofLp) (quadratic_continuous W)
  have hs : TendstoInDistribution (fun n => X (n+1)) atTop Z (fun _ => μ) ν :=
    ⟨fun n => hw.forall_aemeasurable (n+1),hw.aemeasurable_limit,
      hw.tendsto.comp (tendsto_add_atTop_nat 1)⟩
  have hm : UniformMoment μ (fun n => X (n+1)) 2 := by
    apply (controller_fourthMoment loss ridge hr refresh θ hθ).norm_sq_of_four.of_dominated _
      (fun n => (hs.forall_aemeasurable n).aestronglyMeasurable) (entrySize W)
      (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)))
    intro n path
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simpa only [X,Real.norm_eq_abs,EuclideanSpace.real_norm_sq_eq,blochNormSq] using
      quadratic_abs_le W (controllerError loss ridge refresh θ.1 (n+1) path).ofLp
  obtain ⟨K,hK,hKm⟩ := hm
  have ht := WeakMeanLossTransfer.mean_tendsto_of_weak_and_secondMoment
    (fun n => X (n+1)) Z hs (fun n => (hKm n).1) (gaussian_quadratic_memLp W _)
    (fun n => Eventually.of_forall (fun path => quadratic_nonneg W hW _))
    (Eventually.of_forall (fun z => quadratic_nonneg W hW _)) K hK
    (fun n => by simpa only [Real.norm_eq_abs,sq_abs] using (hKm n).2)
  rw [show (∫ z, Z z ∂ν)=(W*covarianceTarget loss θ.1).trace from
    gaussian_quadratic_mean W _ (covariance_posDef loss θ.1 hθ).posSemidef] at ht
  apply (tendsto_add_atTop_iff_nat 1).mp
  have he (n : ℕ) (path : Path) : X n path=(n:ℝ)*
      quadratic W (controller loss n (estimate loss ridge refresh n path)-θ.1) := by
    change quadratic W (Real.sqrt (n:ℝ) • (controller loss n (estimate loss ridge refresh n path)-θ.1)) = _
    rw [quadratic_smul_vector,Real.sq_sqrt (Nat.cast_nonneg n)]
  simpa only [he,integral_const_mul] using ht

def qubitFrobeniusLoss (θ s : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2, Complex.normSq (qubitDensityMatrix s i j-qubitDensityMatrix θ i j)

theorem qubitFrobeniusLoss_eq (θ s : Fin 3 → ℝ) :
    qubitFrobeniusLoss θ s=blochNormSq (s-θ)/2 := by
  simp [qubitFrobeniusLoss,qubitDensityMatrix,pauliLinear,Complex.normSq_apply,
    blochNormSq,Fin.sum_univ_succ,Matrix.one_apply]
  ring

theorem frobenius_mean (ridge : ℝ) (hr : 0 < ridge)
    (refresh : ℕ → Bool) (hrefresh : ∀ K, ∃ n, K ≤ n ∧ refresh n=true)
    (θ : OneQubitPhysicalParameter) (hθ : blochNormSq θ.1 < 1) :
    Tendsto (fun n : ℕ => (n:ℝ)*∫ path,
      qubitFrobeniusLoss θ.1 (controller .frobenius n (estimate .frobenius ridge refresh n path))
      ∂adaptiveInfiniteTrajectoryMeasure (protocol (policy .frobenius ridge refresh)) θ)
      atTop (𝓝 ((2+mixedRadialGap θ.1)^2/2)) := by
  have ht := physical_quadratic_mean .frobenius ridge hr refresh hrefresh θ hθ
    ((1/2:ℝ) • (1:Mat)) (Matrix.PosSemidef.one.smul (by norm_num))
  have he (s : Fin 3 → ℝ) : qubitFrobeniusLoss θ.1 s = quadratic ((1/2:ℝ) • (1:Mat)) (s-θ.1) := by
    rw [qubitFrobeniusLoss_eq,quadratic_smul,quadratic_one]
    ring
  simp_rw [Matrix.smul_mul,one_mul,Matrix.trace_smul,smul_eq_mul,covariance_frobenius_value θ.1 hθ] at ht
  simpa only [he,one_div,mul_comm,div_eq_mul_inv,one_mul] using ht

end
end QubitOracle.AdaptiveDesign.P1Weighted
