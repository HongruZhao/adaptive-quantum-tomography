import QubitOracle.AdaptiveDesign.P1QuadraticMeanLoss
import QubitOracle.AdaptiveDesign.AdaptiveResponseMoments
import QubitOracle.AdaptiveDesign.MixedBuresContinuousQuadratic
import QubitOracle.AdaptiveDesign.P1ControllerBounds
import QubitOracle.AdaptiveDesign.P1ControllerFourthMoment
import QubitOracle.AdaptiveDesign.P1GaussianQuadratic
import QubitOracle.AdaptiveDesign.P1ObservedRidge
import QubitOracle.AdaptiveDesign.P1WeightedBorn
import QubitOracle.AdaptiveDesign.P1WeightedController
import QubitOracle.AdaptiveDesign.P1WeightedCovariance
import QubitOracle.AdaptiveDesign.P1WeightedEndpoints
import QubitOracle.AdaptiveDesign.P1WeightedGeometry
import QubitOracle.AdaptiveDesign.P1WeightedInformation
import QubitOracle.AdaptiveDesign.P1WeightedNormality
import QubitOracle.AdaptiveDesign.P1WeightedOptimality
import QubitOracle.AdaptiveDesign.P1WeightedPolicy
import QubitOracle.AdaptiveDesign.WeakMeanLossTransfer
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.AdaptiveTrajectoryExperiment
import QubitOracle.Paper.MixedOracleGeometry
import QubitOracle.Paper.MixedProbabilityFloor
import QubitOracle.Paper.MixedRotationalTarget
import QubitOracle.Paper.OneQubitCyclicBornPath
import QubitOracle.Paper.OneQubitLabeledThreeAxisBornKernel
import QubitOracle.Paper.OneQubitMixedBuresFidelityLocalRemainder
import QubitOracle.Paper.P1BuresOptimality
/-! Expected Bures loss of the actual adaptive mixed-qubit output,
derived from its CLT, exact loss identity and proved fourth moment. -/
namespace QubitOracle.AdaptiveDesign.P1Weighted
open QubitOracle QubitOracle.Paper MeasureTheory ProbabilityTheory Filter AdaptiveResponseMoments
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
local instance P1BuresMeanLoss_measurable : MeasurableSpace LabeledBinaryOutcome := ⊤
local instance P1BuresMeanLoss_nonempty : Nonempty LabeledBinaryOutcome := ⟨(0,.plus)⟩

theorem bures_mean (ridge : ℝ) (hr : 0 < ridge)
    (refresh : ℕ → Bool) (hrefresh : ∀ K, ∃ n, K ≤ n ∧ refresh n=true)
    (θ : OneQubitPhysicalParameter) (hθ : blochNormSq θ.1 < 1) :
    Tendsto (fun n : ℕ => (n:ℝ)*∫ path,
      mixedQubitBlochBuresSqBetween θ.1 (controller .bures n (estimate .bures ridge refresh n path))
      ∂adaptiveInfiniteTrajectoryMeasure (protocol (policy .bures ridge refresh)) θ)
      atTop (𝓝 (9/4:ℝ)) := by
  let μ := adaptiveInfiniteTrajectoryMeasure (protocol (policy .bures ridge refresh)) θ
  let ν := multivariateGaussian (0:Vector) (covarianceTarget .bures θ.1)
  let θv : Vector := WithLp.toLp 2 θ.1
  have hθv : ‖θv‖ < 1 := by
    have hh := bloch_norm_sq θ.1
    change ‖θv‖^2 = blochNormSq θ.1 at hh
    nlinarith [norm_nonneg θv]
  let s := fun n path => WithLp.toLp 2 (controller .bures n (estimate .bures ridge refresh n path))
  have hm (n : ℕ) : Measurable (s n) :=
    historyStatistic_measurable .bures ridge refresh n
      (fun st => WithLp.toLp 2 (controller .bures n (st.gram⁻¹.mulVec st.rhs)))
  have hp (n : ℕ) (path : Path) : ‖s n path‖ ≤ 1 := controller_norm_le_one .bures _ _
  have hc : TendstoInMeasure μ s atTop (fun _ => θv) := by
    apply tendstoInMeasure_of_tendsto_ae (fun n => (hm n).aestronglyMeasurable)
    filter_upwards [controller_consistent .bures ridge hr refresh θ hθ] with path hh
    exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).continuousAt.tendsto.comp hh
  let f := MixedBuresContinuousQuadratic.form θv
  let X := fun n path => f (s n path) (controllerError .bures ridge refresh θ.1 n path)
  let Z := fun z : Vector => f θv z
  have hclt : TendstoInDistribution (controllerError .bures ridge refresh θ.1) atTop
      (id : Vector → Vector) (fun _ => μ) ν := controller_normal .bures ridge hr refresh hrefresh θ hθ
  have hswap : Continuous (fun zs : Vector × Vector => (zs.2,zs.1)) :=
    continuous_snd.prodMk continuous_fst
  have hcont : Continuous (fun zs : Vector × Vector => f zs.2 zs.1) := by
    unfold f
    change Continuous ((fun sz : Vector × Vector => MixedBuresContinuousQuadratic.form θv sz.1 sz.2) ∘
      (fun zs : Vector × Vector => (zs.2,zs.1)))
    apply Continuous.comp
    · exact MixedBuresContinuousQuadratic.form_continuous θv hθv
    · exact hswap
  have hw : TendstoInDistribution X atTop Z (fun _ => μ) ν := by
    have hh := hclt.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g:=fun zs : Vector × Vector => f zs.2 zs.1) hcont
      hc (fun n => (hm n).aemeasurable)
    exact hh
  have hs : TendstoInDistribution (fun n => X (n+1)) atTop Z (fun _ => μ) ν :=
    ⟨fun n => hw.forall_aemeasurable (n+1),hw.aemeasurable_limit,
      hw.tendsto.comp (tendsto_add_atTop_nat 1)⟩
  have hXm : UniformMoment μ (fun n => X (n+1)) 2 := by
    apply (controller_fourthMoment .bures ridge hr refresh θ hθ).norm_sq_of_four.of_dominated _
      (fun n => (hs.forall_aemeasurable n).aestronglyMeasurable)
      ((1+4/(MixedBuresContinuousQuadratic.gap θv)^2)/2) (by positivity)
    intro n path
    rw [Real.norm_of_nonneg (MixedBuresContinuousQuadratic.form_nonneg _ _ _),
      Real.norm_of_nonneg (sq_nonneg _)]
    exact MixedBuresContinuousQuadratic.form_bound _ _ _ hθv (hp _ _)
  let W : Mat := (1/4:ℝ) • (qubitSLDFisherInv θ.1)⁻¹
  have hZ (z : Vector) : Z z=quadratic W z.ofLp := MixedBuresContinuousQuadratic.form_at_truth θv z hθv
  have hZm : MemLp Z 2 ν := by
    rw [show Z=(fun z : Vector => quadratic W z.ofLp) from funext hZ]
    exact gaussian_quadratic_memLp W (covarianceTarget .bures θ.1)
  have hZmean : ∫ z, Z z ∂ν = (9/4:ℝ) := by
    simp_rw [hZ]
    rw [gaussian_quadratic_mean W _ (covariance_posDef .bures θ.1 hθ).posSemidef]
    have hh := optimal_criterion_value .bures θ.1 hθ
    change P1.buresDesignCriterion θ.1 (informationTarget .bures θ.1) = (9/4:ℝ) at hh
    simpa only [W,Matrix.smul_mul,Matrix.trace_smul,smul_eq_mul,
      covariance_eq_information_inv .bures θ.1 hθ,P1.buresDesignCriterion] using hh
  obtain ⟨K,hK,hKm⟩ := hXm
  have ht := WeakMeanLossTransfer.mean_tendsto_of_weak_and_secondMoment
    (fun n => X (n+1)) Z hs (fun n => (hKm n).1) hZm
    (fun _ => Eventually.of_forall (fun _ => MixedBuresContinuousQuadratic.form_nonneg _ _ _))
    (Eventually.of_forall (fun _ => MixedBuresContinuousQuadratic.form_nonneg _ _ _)) K hK
    (fun n => by simpa only [Real.norm_eq_abs,sq_abs] using (hKm n).2)
  rw [hZmean] at ht
  have he (n : ℕ) (path : Path) : X n path=(n:ℝ)*
      mixedQubitBlochBuresSqBetween θ.1 (controller .bures n (estimate .bures ridge refresh n path)) := by
    have herr : controllerError .bures ridge refresh θ.1 n path=Real.sqrt (n:ℝ) • (s n path-θv) := by
      ext i
      rfl
    change f (s n path) (controllerError .bures ridge refresh θ.1 n path) = _
    unfold f
    rw [herr,MixedBuresContinuousQuadratic.form_smul,Real.sq_sqrt (Nat.cast_nonneg n),
      ← MixedBuresContinuousQuadratic.exact_loss θv (s n path) hθv (hp n path),
      MixedBuresContinuousQuadratic.bloch_bures θv (s n path) hθv.le]
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [he,integral_const_mul] using ht

end
end QubitOracle.AdaptiveDesign.P1Weighted
