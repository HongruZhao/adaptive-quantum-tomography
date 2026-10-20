import QubitOracle.Paper.AdaptiveLANExperimentBridge
import QubitOracle.Paper.QuadraticRiskAttainability

/-!
# Adaptive score-root efficiency

This module formalizes the efficiency bridge needed for an adaptive
likelihood or estimating-equation root.  It does not invoke the iid-only MLE
theorem.  Instead it separates the argument into four checkable layers:

1. the estimator is a root of the adaptive score;
2. Taylor expansion at that root has an explicit remainder;
3. replacing the observed Hessian by the limiting information has an
   action remainder tending to zero in probability;
4. capped-risk convergence and uniform quadratic tails remove the gap
   between weak convergence and quadratic-risk convergence.

The deterministic identity is proved in Lean.  The probabilistic linear
representation follows from the two displayed remainder convergences, and
Mathlib's Slutsky theorem then gives the inverse-information Gaussian limit.
No new axiom is introduced.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace Topology

noncomputable section

/-! ## Convergence-in-probability closure lemmas -/

/-- Vector-valued sums preserve convergence to zero in probability. -/
theorem tendstoInMeasure_add_zero_vector
    {Omega I E : Type*} [MeasurableSpace Omega]
    [SeminormedAddCommGroup E]
    {mu : Measure Omega} {l : Filter I}
    {f g : I -> Omega -> E}
    (hf : TendstoInMeasure mu f l 0)
    (hg : TendstoInMeasure mu g l 0) :
    TendstoInMeasure mu (fun i omega => f i omega + g i omega) l 0 := by
  rw [tendstoInMeasure_iff_norm] at hf hg ⊢
  intro epsilon hepsilon
  have hhalf : 0 < epsilon / 2 := half_pos hepsilon
  have hf' := hf (epsilon / 2) hhalf
  have hg' := hg (epsilon / 2) hhalf
  have hsum : Tendsto (fun i =>
      mu {omega | epsilon / 2 <= ‖f i omega‖} +
        mu {omega | epsilon / 2 <= ‖g i omega‖}) l (nhds 0) := by
    simpa using hf'.add hg'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => bot_le) ?_
  intro i
  simp only [Pi.zero_apply, sub_zero]
  calc
    mu {omega | epsilon <= ‖f i omega + g i omega‖} <=
        mu ({omega | epsilon / 2 <= ‖f i omega‖} ∪
          {omega | epsilon / 2 <= ‖g i omega‖}) := by
      apply measure_mono
      intro omega homega
      change epsilon <= ‖f i omega + g i omega‖ at homega
      simp only [Set.mem_union, Set.mem_ofPred_eq]
      by_cases hfhalf : epsilon / 2 <= ‖f i omega‖
      · exact Or.inl hfhalf
      · right
        have hf_lt : ‖f i omega‖ < epsilon / 2 := lt_of_not_ge hfhalf
        by_contra hghalf
        have hg_lt : ‖g i omega‖ < epsilon / 2 := lt_of_not_ge hghalf
        have htriangle := norm_add_le (f i omega) (g i omega)
        linarith
    _ <= mu {omega | epsilon / 2 <= ‖f i omega‖} +
        mu {omega | epsilon / 2 <= ‖g i omega‖} := measure_union_le _ _

/-- Applying a fixed continuous linear map preserves convergence to zero in
probability.  This is the continuity step used to multiply a score remainder
by the inverse limiting information. -/
theorem tendstoInMeasure_continuousLinearMap_zero
    {Omega I E F : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {mu : Measure Omega} {l : Filter I}
    (L : E →L[ℝ] F) {f : I -> Omega -> E}
    (hf : TendstoInMeasure mu f l 0) :
    TendstoInMeasure mu (fun i omega => L (f i omega)) l 0 := by
  rw [tendstoInMeasure_iff_norm] at hf ⊢
  simp only [Pi.zero_apply, sub_zero] at hf ⊢
  intro epsilon hepsilon
  by_cases hL : ‖L‖ = 0
  · have hLzero : L = 0 := norm_eq_zero.mp hL
    simpa [hLzero, not_le.mpr hepsilon] using
      (tendsto_const_nhds : Tendsto (fun _ : I => (0 : ENNReal)) l (nhds 0))
  · have hLpos : 0 < ‖L‖ :=
      lt_of_le_of_ne (norm_nonneg L) (Ne.symm hL)
    have hbase := hf (epsilon / ‖L‖) (div_pos hepsilon hLpos)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbase
      (fun _ => bot_le) ?_
    intro i
    apply measure_mono
    intro omega homega
    change epsilon <= ‖L (f i omega)‖ at homega
    change epsilon / ‖L‖ <= ‖f i omega‖
    apply (div_le_iff₀ hLpos).2
    calc
      epsilon <= ‖L (f i omega)‖ := homega
      _ <= ‖L‖ * ‖f i omega‖ := L.le_opNorm _
      _ = ‖f i omega‖ * ‖L‖ := mul_comm _ _

/-! ## Exact inverse-information algebra -/

/-- Matrix action in the LAN API is the standard continuous linear action on
Euclidean space. -/
theorem lanMatrixAction_eq_toEuclideanCLM
    {D : Type*} [Fintype D] [DecidableEq D]
    (A : Matrix D D ℝ) (z : LANParameter D) :
    lanMatrixAction A z = Matrix.toEuclideanCLM (𝕜 := ℝ) A z :=
  rfl

/-- Positive definiteness makes inverse information cancel information on a
local parameter vector. -/
theorem lanMatrixAction_inv_apply
    {D : Type*} [Fintype D] [DecidableEq D]
    (M : Matrix D D ℝ) (hM : M.PosDef) (z : LANParameter D) :
    lanMatrixAction M⁻¹ (lanMatrixAction M z) = z := by
  letI : Invertible M := hM.isUnit.invertible
  ext i
  change (M⁻¹).mulVec (M.mulVec (fun j => z j)) i = z i
  have hcancel : M⁻¹.mulVec (M.mulVec (fun j => z j)) = (fun j => z j) :=
    Matrix.inv_mulVec_eq_vec rfl
  exact congrFun hcancel i

/-- Matrix subtraction is respected by the LAN action. -/
theorem lanMatrixAction_matrix_sub
    {D : Type*} [Fintype D]
    (A B : Matrix D D ℝ) (z : LANParameter D) :
    lanMatrixAction (A - B) z = lanMatrixAction A z - lanMatrixAction B z := by
  ext i
  simp [lanMatrixAction, Matrix.sub_mulVec]

/-- Vector subtraction is respected by the LAN action. -/
theorem lanMatrixAction_vector_sub
    {D : Type*} [Fintype D] [DecidableEq D]
    (A : Matrix D D ℝ) (x y : LANParameter D) :
    lanMatrixAction A (x - y) = lanMatrixAction A x - lanMatrixAction A y := by
  change Matrix.toEuclideanCLM (𝕜 := ℝ) A (x - y) =
    Matrix.toEuclideanCLM (𝕜 := ℝ) A x -
      Matrix.toEuclideanCLM (𝕜 := ℝ) A y
  exact map_sub _ x y

/-- Deterministic score-root identity.

If `score = 0` and
`score = Delta - H Z + r`, then
`Z - M⁻¹ Delta = M⁻¹ ((M-H)Z+r)`.  Thus the asymptotic linear
representation is obtained from genuine Hessian and Taylor errors, rather
than assumed as a conclusion. -/
theorem scoreRoot_inverseInformation_identity
    {D : Type*} [Fintype D] [DecidableEq D]
    (M H : Matrix D D ℝ) (hM : M.PosDef)
    (score Delta Z r : LANParameter D)
    (hroot : score = 0)
    (htaylor : score = Delta - lanMatrixAction H Z + r) :
    Z - lanMatrixAction M⁻¹ Delta =
      lanMatrixAction M⁻¹ (lanMatrixAction (M - H) Z + r) := by
  have hzero : Delta - lanMatrixAction H Z + r = 0 :=
    htaylor.symm.trans hroot
  have hH : Delta + r = lanMatrixAction H Z := by
    calc
      Delta + r =
          (Delta - lanMatrixAction H Z + r) + lanMatrixAction H Z := by
            abel
      _ = 0 + lanMatrixAction H Z := by rw [hzero]
      _ = lanMatrixAction H Z := zero_add _
  have hresidual :
      lanMatrixAction M Z - Delta = lanMatrixAction (M - H) Z + r := by
    rw [lanMatrixAction_matrix_sub, ← hH]
    abel
  calc
    Z - lanMatrixAction M⁻¹ Delta =
        lanMatrixAction M⁻¹ (lanMatrixAction M Z) -
          lanMatrixAction M⁻¹ Delta := by
      rw [lanMatrixAction_inv_apply M hM Z]
    _ = lanMatrixAction M⁻¹ (lanMatrixAction M Z - Delta) := by
      rw [lanMatrixAction_vector_sub]
    _ = lanMatrixAction M⁻¹ (lanMatrixAction (M - H) Z + r) := by
      rw [hresidual]

/-! ## Adaptive score-root problem and asymptotic linearity -/

/-- Data of an adaptive score equation in local coordinates.  `localError`
is the normalized estimation error `Z_n`; `observedInformation` may depend on
the data and on the local interpolation point. -/
structure AdaptiveScoreRootProblem
    (D Omega : Type*) [Fintype D] where
  scoreAtLocal : ℕ -> LANParameter D -> Omega -> LANParameter D
  localError : ℕ -> Omega -> LANParameter D
  observedInformation : ℕ -> LANParameter D -> Omega -> Matrix D D ℝ
  taylorRemainder : ℕ -> Omega -> LANParameter D

namespace AdaptiveScoreRootProblem

variable {D : Type*} {Omega : Type} [Fintype D] [DecidableEq D]

/-- Observed information evaluated at the score root. -/
def informationAtRoot (problem : AdaptiveScoreRootProblem D Omega)
    (n : ℕ) (omega : Omega) : Matrix D D ℝ :=
  problem.observedInformation n (problem.localError n omega) omega

/-- Error made by replacing the observed Hessian action at the root by the
limiting information action. -/
def hessianActionRemainder (problem : AdaptiveScoreRootProblem D Omega)
    (M : Matrix D D ℝ) (n : ℕ) (omega : Omega) : LANParameter D :=
  lanMatrixAction (M - problem.informationAtRoot n omega)
    (problem.localError n omega)

/-- The residual in the desired asymptotic linear representation. -/
def asymptoticLinearResidual (problem : AdaptiveScoreRootProblem D Omega)
    (M : Matrix D D ℝ) (Delta : ℕ -> Omega -> LANParameter D)
    (n : ℕ) (omega : Omega) : LANParameter D :=
  problem.localError n omega - lanMatrixAction M⁻¹ (Delta n omega)

/-- The adaptive estimating equation vanishes at the proposed root, almost
surely under the base trajectory law. -/
def IsScoreRoot [MeasurableSpace Omega] (problem : AdaptiveScoreRootProblem D Omega)
    (mu : Measure Omega) : Prop :=
  ∀ n, (fun omega => problem.scoreAtLocal n (problem.localError n omega) omega) =ᵐ[mu]
    (fun _ => 0)

/-- Exact Taylor expansion of the adaptive score at the random root. -/
def HasScoreTaylorExpansion [MeasurableSpace Omega]
    (problem : AdaptiveScoreRootProblem D Omega)
    (mu : Measure Omega) (Delta : ℕ -> Omega -> LANParameter D) : Prop :=
  ∀ n, (fun omega => problem.scoreAtLocal n (problem.localError n omega) omega) =ᵐ[mu]
    (fun omega =>
      Delta n omega -
        lanMatrixAction (problem.informationAtRoot n omega) (problem.localError n omega) +
          problem.taylorRemainder n omega)

/-- Uniform Hessian linearization at the score root.  A protocol-specific
proof may establish this from a uniform Hessian law on local neighborhoods
and tightness of `localError`; here the exact resulting Hessian-action error
is displayed rather than hidden in an efficiency conclusion. -/
def HasUniformHessianLinearizationAtRoot [MeasurableSpace Omega]
    (problem : AdaptiveScoreRootProblem D Omega)
    (mu : Measure Omega) (M : Matrix D D ℝ) : Prop :=
  TendstoInMeasure mu (problem.hessianActionRemainder M) atTop 0

/-- The precise `o_P(1)` asymptotic linear representation. -/
def HasAsymptoticLinearRepresentation [MeasurableSpace Omega]
    (problem : AdaptiveScoreRootProblem D Omega)
    (mu : Measure Omega) (M : Matrix D D ℝ)
    (Delta : ℕ -> Omega -> LANParameter D) : Prop :=
  TendstoInMeasure mu (problem.asymptoticLinearResidual M Delta) atTop 0

/-- The deterministic identity lifted to almost-everywhere score-root and
Taylor identities. -/
theorem asymptoticLinearResidual_ae_eq
    [MeasurableSpace Omega]
    (problem : AdaptiveScoreRootProblem D Omega)
    (mu : Measure Omega) (M : Matrix D D ℝ) (hM : M.PosDef)
    (Delta : ℕ -> Omega -> LANParameter D)
    (hroot : problem.IsScoreRoot mu)
    (htaylor : problem.HasScoreTaylorExpansion mu Delta) :
    ∀ n, problem.asymptoticLinearResidual M Delta n =ᵐ[mu]
      (fun omega => lanMatrixAction M⁻¹
        (problem.hessianActionRemainder M n omega + problem.taylorRemainder n omega)) := by
  intro n
  filter_upwards [hroot n, htaylor n] with omega hrootOmega htaylorOmega
  simpa [asymptoticLinearResidual, hessianActionRemainder] using
    scoreRoot_inverseInformation_identity
    M (problem.informationAtRoot n omega) hM
    (problem.scoreAtLocal n (problem.localError n omega) omega)
    (Delta n omega) (problem.localError n omega) (problem.taylorRemainder n omega)
    hrootOmega htaylorOmega

/-- A score root plus Taylor remainder convergence and uniform Hessian
linearization yields `Z_n = M⁻¹ Delta_n + o_P(1)`. -/
theorem asymptoticLinearRepresentation_of_scoreRoot
    [MeasurableSpace Omega]
    (problem : AdaptiveScoreRootProblem D Omega)
    (mu : Measure Omega) (M : Matrix D D ℝ) (hM : M.PosDef)
    (Delta : ℕ -> Omega -> LANParameter D)
    (hroot : problem.IsScoreRoot mu)
    (htaylor : problem.HasScoreTaylorExpansion mu Delta)
    (hHessian : problem.HasUniformHessianLinearizationAtRoot mu M)
    (hTaylorRemainder :
      TendstoInMeasure mu problem.taylorRemainder atTop 0) :
    problem.HasAsymptoticLinearRepresentation mu M Delta := by
  have hCombined : TendstoInMeasure mu
      (fun n omega => problem.hessianActionRemainder M n omega +
        problem.taylorRemainder n omega) atTop 0 :=
    tendstoInMeasure_add_zero_vector hHessian hTaylorRemainder
  have hMapped : TendstoInMeasure mu
      (fun n omega => lanMatrixAction M⁻¹
        (problem.hessianActionRemainder M n omega + problem.taylorRemainder n omega))
      atTop 0 := by
    simpa only [lanMatrixAction_eq_toEuclideanCLM] using
      tendstoInMeasure_continuousLinearMap_zero
        (Matrix.toEuclideanCLM (𝕜 := ℝ) M⁻¹) hCombined
  exact hMapped.congr_left fun n =>
    (problem.asymptoticLinearResidual_ae_eq mu M hM Delta hroot htaylor n).symm

/-- Slutsky transfer: score convergence and the proved asymptotic linear
representation give the inverse-information transform of the Gaussian score
as the estimator limit.  The limit is written as `M⁻¹ G`, `G ~ N(0,M)`,
without adding a separate Gaussian mapping axiom. -/
theorem tendstoInDistribution_inverseInformationGaussian
    [MeasurableSpace Omega]
    (problem : AdaptiveScoreRootProblem D Omega)
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (M : Matrix D D ℝ)
    (Delta : ℕ -> Omega -> LANParameter D)
    (hScore : TendstoInDistribution Delta atTop id
      (fun _ => mu) (multivariateGaussian 0 M))
    (hLinear : problem.HasAsymptoticLinearRepresentation mu M Delta)
    (hResidualMeasurable : ∀ n,
      AEMeasurable (problem.asymptoticLinearResidual M Delta n) mu) :
    TendstoInDistribution problem.localError atTop
      (fun z => lanMatrixAction M⁻¹ z)
      (fun _ => mu) (multivariateGaussian 0 M) := by
  have hMapped := hScore.continuous_comp
    (g := fun z => lanMatrixAction M⁻¹ z) (by
      change Continuous (Matrix.toEuclideanCLM (𝕜 := ℝ) M⁻¹)
      exact (Matrix.toEuclideanCLM (𝕜 := ℝ) M⁻¹).continuous)
  have hSlutsky := hMapped.add_of_tendstoInMeasure_const
    hLinear hResidualMeasurable
  have hSequence :
      (fun n =>
        (fun omega => lanMatrixAction M⁻¹ (Delta n omega)) +
          problem.asymptoticLinearResidual M Delta n) =
        problem.localError := by
    funext n omega
    simp [asymptoticLinearResidual]
  rw [← hSequence]
  simpa [Function.comp_def] using hSlutsky

/-- Turn the normalized score root into a statistic of the fixed-sample
adaptive local experiment. -/
def statistic
    [MeasurableSpace Omega]
    (problem : AdaptiveScoreRootProblem D Omega)
    (P : ℕ -> LANParameter D -> Measure Omega)
    (hP : ∀ n h, IsProbabilityMeasure (P n h))
    (hMeasurable : ∀ n, Measurable (problem.localError n)) :
    (n : ℕ) -> Statistic
      (fixedSampleExperiment (D := D) (Omega := Omega) P hP n) (LANParameter D) :=
  fun n =>
    { toFun := problem.localError n
      measurable := hMeasurable n }

end AdaptiveScoreRootProblem

/-! ## Gaussian efficiency and adaptive martingale-LAN assembly -/

/-- A score-root estimator is locally asymptotically minimax once the
score-root algebra, Gaussian score convergence, experiment convergence,
capped-risk convergence, and uniform quadratic tails have each been checked.

Weak convergence alone is intentionally not used as a quadratic-risk
statement: `hCapped` is the explicit risk-level Slutsky bridge, and `hTail`
is the explicit uniform-integrability bridge. -/
theorem adaptiveScoreRoot_attains_minimax_of_gaussian_score
    {D : Type*} {Omega : Type} [Fintype D] [DecidableEq D]
    [MeasurableSpace Omega]
    (P : ℕ -> LANParameter D -> Measure Omega)
    (hP : ∀ n h, IsProbabilityMeasure (P n h))
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (problem : AdaptiveScoreRootProblem D Omega)
    (M : Matrix D D ℝ) (hM : M.PosDef)
    (Delta : ℕ -> Omega -> LANParameter D)
    (hroot : problem.IsScoreRoot mu)
    (htaylor : problem.HasScoreTaylorExpansion mu Delta)
    (hHessian : problem.HasUniformHessianLinearizationAtRoot mu M)
    (hTaylorRemainder : TendstoInMeasure mu problem.taylorRemainder atTop 0)
    (hScore : TendstoInDistribution Delta atTop id
      (fun _ => mu) (multivariateGaussian 0 M))
    (hResidualMeasurable : ∀ n,
      AEMeasurable (problem.asymptoticLinearResidual M Delta n) mu)
    (hEstimatorMeasurable : ∀ n, Measurable (problem.localError n))
    (hExperiment : ExperimentsConverge
      (fixedSampleExperiment (D := D) (Omega := Omega) P hP)
      (gaussianScoreExperiment M))
    (hCapped : ∀ I : Finset (LANParameter D), I.Nonempty ->
      CappedFiniteLocalRisksConvergeToCenteredGaussian M
        (fixedSampleExperiment (D := D) (Omega := Omega) P hP)
        (problem.statistic P hP hEstimatorMeasurable) I)
    (hTail : ∀ I : Finset (LANParameter D), I.Nonempty ->
      HasUniformFiniteLocalQuadraticTails
        (fixedSampleExperiment (D := D) (Omega := Omega) P hP)
        (problem.statistic P hP hEstimatorMeasurable) I) :
    problem.HasAsymptoticLinearRepresentation mu M Delta ∧
      TendstoInDistribution problem.localError atTop
        (fun z => lanMatrixAction M⁻¹ z)
        (fun _ => mu) (multivariateGaussian 0 M) ∧
      AttainsGaussianLocalAsymptoticMinimaxBound M
        (fixedSampleExperiment (D := D) (Omega := Omega) P hP)
        (problem.statistic P hP hEstimatorMeasurable) := by
  have hLinear := problem.asymptoticLinearRepresentation_of_scoreRoot
    mu M hM Delta hroot htaylor hHessian hTaylorRemainder
  exact ⟨hLinear,
    problem.tendstoInDistribution_inverseInformationGaussian
      mu M Delta hScore hLinear hResidualMeasurable,
    gaussianScore_localAsymptoticMinimax_attained_of_cappedGaussian_of_uniformTails
      M hM (fixedSampleExperiment (D := D) (Omega := Omega) P hP) hExperiment
      (problem.statistic P hP hEstimatorMeasurable) hCapped hTail⟩

/-- End-to-end adaptive score-root efficiency theorem.

Hall--Heyde and Cramer--Wold produce the multivariate martingale score limit;
the explicit RN likelihood remainder produces adaptive LAN and convergence
of experiments; the proved score-root identity and Hessian/Taylor errors
produce asymptotic linearity; finally capped risks and uniform tails give
attainment of the all-estimator minimax lower bound. -/
theorem adaptiveMartingaleLAN_scoreRoot_attains_minimax
    {D : Type*} {Omega : Type} [Fintype D] [DecidableEq D]
    [MeasurableSpace Omega]
    (P : ℕ -> LANParameter D -> Measure Omega)
    (hP : ∀ n h, IsProbabilityMeasure (P n h))
    (mu : Measure Omega) [hmu : IsProbabilityMeasure mu]
    (hbase : ∀ n, P n 0 = mu)
    (filtration : ℕ -> Filtration ℕ (inferInstance : MeasurableSpace Omega))
    (increment : ℕ -> ℕ -> Omega -> MartingaleScoreSpace D)
    (M : Matrix D D ℝ) (hM : M.PosDef)
    (hMDS : MartingaleCLTProblem.IsSquareIntegrableMartingaleDifferenceArray
      (fixedSampleMartingaleProblem (D := D) mu hmu filtration increment))
    (hLindeberg : MartingaleCLTProblem.HasConditionalLindeberg
      (fixedSampleMartingaleProblem (D := D) mu hmu filtration increment))
    (hCovariance : MartingaleCLTProblem.ConditionalCovarianceConverges
      (fixedSampleMartingaleProblem (D := D) mu hmu filtration increment) M)
    (hTerminalMeasurable : ∀ n,
      AEMeasurable
        ((fixedSampleMartingaleProblem (D := D) mu hmu filtration increment).terminalSum n) mu)
    (hDomination : ∀ n h, P n h ≪ P n 0)
    (hLANRemainder : LANRemainderConvergesInProbability
      (fixedSampleExperiment (D := D) (Omega := Omega) P hP) M
      (fixedSampleMartingaleProblem (D := D) mu hmu filtration increment).terminalSum)
    (problem : AdaptiveScoreRootProblem D Omega)
    (hroot : problem.IsScoreRoot mu)
    (htaylor : problem.HasScoreTaylorExpansion mu
      (fixedSampleMartingaleProblem (D := D) mu hmu filtration increment).terminalSum)
    (hHessian : problem.HasUniformHessianLinearizationAtRoot mu M)
    (hTaylorRemainder : TendstoInMeasure mu problem.taylorRemainder atTop 0)
    (hResidualMeasurable : ∀ n,
      AEMeasurable (problem.asymptoticLinearResidual M
        (fixedSampleMartingaleProblem (D := D) mu hmu filtration increment).terminalSum n) mu)
    (hEstimatorMeasurable : ∀ n, Measurable (problem.localError n))
    (hCapped : ∀ I : Finset (LANParameter D), I.Nonempty ->
      CappedFiniteLocalRisksConvergeToCenteredGaussian M
        (fixedSampleExperiment (D := D) (Omega := Omega) P hP)
        (problem.statistic P hP hEstimatorMeasurable) I)
    (hTail : ∀ I : Finset (LANParameter D), I.Nonempty ->
      HasUniformFiniteLocalQuadraticTails
        (fixedSampleExperiment (D := D) (Omega := Omega) P hP)
        (problem.statistic P hP hEstimatorMeasurable) I) :
    problem.HasAsymptoticLinearRepresentation mu M
        (fixedSampleMartingaleProblem (D := D) mu hmu filtration increment).terminalSum ∧
      TendstoInDistribution problem.localError atTop
        (fun z => lanMatrixAction M⁻¹ z)
        (fun _ => mu) (multivariateGaussian 0 M) ∧
      AttainsGaussianLocalAsymptoticMinimaxBound M
        (fixedSampleExperiment (D := D) (Omega := Omega) P hP)
        (problem.statistic P hP hEstimatorMeasurable) := by
  have hScore := martingale_score_clt_multivariate
    (fixedSampleMartingaleProblem (D := D) mu hmu filtration increment) M hM
    hMDS hLindeberg hCovariance hTerminalMeasurable
  have hExperiment :=
    adaptiveExperimentsConverge_gaussianScore_of_martingale_conditions
      P hP mu hmu hbase filtration increment M hM hMDS hLindeberg
      hCovariance hTerminalMeasurable hDomination hLANRemainder
  exact adaptiveScoreRoot_attains_minimax_of_gaussian_score
    P hP mu problem M hM
    (fixedSampleMartingaleProblem (D := D) mu hmu filtration increment).terminalSum
    hroot htaylor hHessian hTaylorRemainder hScore hResidualMeasurable
    hEstimatorMeasurable hExperiment hCapped hTail

end

end QubitOracle.Paper
