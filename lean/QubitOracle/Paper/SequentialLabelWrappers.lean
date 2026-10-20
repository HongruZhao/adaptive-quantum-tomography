import QubitOracle.Paper.AdaptiveLANAssembly
import QubitOracle.Paper.ProtocolRegularity
import QubitOracle.Paper.MixedBuresLocal
import QubitOracle.Paper.MixedInformationBound

namespace QubitOracle.Paper.Label

open Filter MeasureTheory

open scoped BigOperators

noncomputable section

/-- `eq:emp-info-intro`: realized normalized accumulated information. -/
theorem eq_emp_info_intro
    {Theta M Y D : Type*} [Fintype Y]
    (model : FiniteScoreModel Theta M Y D) (theta : Theta)
    (h : SequentialHistory M Y) :
    empiricalInformation model theta h =
      (h.length : ℝ)⁻¹ • accumulatedInformation model theta h :=
  rfl

/-- `eq:SI-alternating-filtration`: finite-history representation of the
before-setting, after-setting, and after-outcome information stages. -/
theorem eq_SI_alternating_filtration
    {M Y : Type*} (h : SequentialHistory M Y) (m : M) (y : Y) :
    revealSetting h m = (h, m) ∧
      revealOutcome (revealSetting h m) y = (m, y) :: h :=
  ⟨rfl, rfl⟩

/-- `eq:SI-shotwise-kernel`: initial exploration and later convex-mixture
policy masses. -/
theorem eq_SI_shotwise_kernel
    {M Y : Type*} [Fintype M]
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (exploit explore : AdaptivePolicy M Y)
    (h : SequentialHistory M Y) (m : M) :
    (shotwisePolicyKernel true epsilon hepsilon0 hepsilon1 exploit explore).mass h m =
        explore.mass h m ∧
      (shotwisePolicyKernel false epsilon hepsilon0 hepsilon1 exploit explore).mass h m =
        (1 - epsilon) * exploit.mass h m + epsilon * explore.mass h m := by
  simp [shotwisePolicyKernel]

/-- `lem:SI-full-likelihood`: exact finite discrete adaptive path
factorization and policy cancellation. -/
theorem lem_SI_full_likelihood
    {Theta M Y : Type*} [Fintype M] [Fintype Y]
    (q : AdaptivePolicy M Y) (p : OutcomeKernel Theta M Y)
    (theta theta' : Theta) (h : SequentialHistory M Y)
    (hq : policyPathMass q h ≠ 0) :
    adaptivePathMass q p theta' h / adaptivePathMass q p theta h =
      shotwiseLikelihoodRatio p theta theta' h :=
  finiteAdaptiveLikelihoodRatio_factorization q p theta theta' h hq

/-- `eq:SI-conditional-born-mass`: conditional outcome mass. -/
theorem eq_SI_conditional_born_mass
    {Theta M Y : Type*} [Fintype Y]
    (p : OutcomeKernel Theta M Y) (theta : Theta) (m : M) (y : Y) :
    conditionalBornMass p theta m y = p.mass (theta, m) y :=
  rfl

/-- `eq:SI-full-likelihood-product`: the full likelihood ratio is the
product of shotwise Born-mass ratios in the finite model. -/
theorem eq_SI_full_likelihood_product
    {Theta M Y : Type*} [Fintype M] [Fintype Y]
    (q : AdaptivePolicy M Y) (p : OutcomeKernel Theta M Y)
    (theta theta' : Theta) (h : SequentialHistory M Y)
    (hq : policyPathMass q h ≠ 0) :
    adaptivePathMass q p theta' h / adaptivePathMass q p theta h =
      shotwiseLikelihoodRatio p theta theta' h :=
  finiteAdaptiveLikelihoodRatio_factorization q p theta theta' h hq

/-- `eq:SI-full-score-increment`: one-shot score definition. -/
theorem eq_SI_full_score_increment
    {Theta M Y D : Type*} [Fintype Y]
    (model : FiniteScoreModel Theta M Y D)
    (theta : Theta) (m : M) (y : Y) :
    scoreIncrement model theta m y = model.score theta m y :=
  rfl

/-- `eq:SI-full-conditional-information`: entrywise conditional Fisher
information identity. -/
theorem eq_SI_full_conditional_information
    {Theta M Y D : Type*} [Fintype Y]
    (model : FiniteScoreModel Theta M Y D)
    (theta : Theta) (m : M) (j k : D) :
    conditionalInformation model theta m j k =
      ∑ y, model.outcome.mass (theta, m) y *
        (model.score theta m y j * model.score theta m y k) :=
  conditionalInformation_apply model theta m j k

/-- `eq:SI-full-central-sequence`: normalized accumulated score. -/
theorem eq_SI_full_central_sequence
    {Theta M Y D : Type*} [Fintype Y]
    (model : FiniteScoreModel Theta M Y D) (theta : Theta)
    (regularWeight : SequentialHistory M Y -> M -> ℝ)
    (h : SequentialHistory M Y) :
    weightedCentralSequence model theta regularWeight h =
      (Real.sqrt (h.length : ℝ))⁻¹ •
        weightedHistoryScore model theta regularWeight h :=
  rfl

/-- `eq:SI-full-score-martingale`: conditional score centering and
conditional covariance identity in the finite regular model. -/
theorem eq_SI_full_score_martingale
    {Theta M Y D : Type*} [Fintype Y]
    (model : FiniteScoreModel Theta M Y D)
    (theta : Theta) (m : M) (regularWeight : ℝ) :
    finiteOutcomeExpectation model.outcome theta m
        (fun y => regularWeight • model.score theta m y) = 0 ∧
      finiteOutcomeExpectation model.outcome theta m
        (fun y => regularWeight •
          Matrix.vecMulVec (model.score theta m y) (model.score theta m y)) =
        regularWeight • conditionalInformation model theta m := by
  exact ⟨finiteOutcomeExpectation_weightedScore_eq_zero
      model theta m regularWeight,
    finiteOutcomeExpectation_weightedScoreOuter_eq_information
      model theta m regularWeight⟩

/-- `eq:main-predictable-information`: normalized accumulated regular
conditional information. -/
theorem eq_main_predictable_information
    {Theta M Y D : Type*} [Fintype Y]
    (model : FiniteScoreModel Theta M Y D) (theta : Theta)
    (regularWeight : SequentialHistory M Y -> M -> ℝ)
    (h : SequentialHistory M Y) :
    weightedEmpiricalInformation model theta regularWeight h =
      (h.length : ℝ)⁻¹ •
        weightedAccumulatedInformation model theta regularWeight h :=
  rfl

/-- `eq:SI-full-hessian-identity`: the conditional expected negative
log-mass Hessian equals conditional Fisher information. -/
theorem eq_SI_full_hessian_identity
    {Theta M Y D : Type*} [Fintype Y]
    (model : FiniteLogDerivativeModel Theta M Y D)
    (theta : Theta) (m : M) :
    finiteOutcomeExpectation model.outcome theta m
        (fun y => model.observedInformation theta m y) =
      conditionalInformation model.toFiniteScoreModel theta m :=
  finiteOutcomeExpectation_observedInformation_eq_information model theta m

/-- `eq:main-tail-score-moment`: finite conditional tail-score moment. -/
theorem eq_main_tail_score_moment
    {Y E : Type*} [Fintype Y] [Norm E]
    (mass : Y -> ℝ) (score : Y -> E) (epsilon : ℝ) (n : ℕ) :
    finiteTailScoreMoment mass score epsilon n =
      ∑ y, mass y * ‖score y‖ ^ 2 *
        lindebergIndicator (epsilon * Real.sqrt (n : ℝ)) ‖score y‖ :=
  rfl

/-- `eq:main-martingale-Lindeberg`: finite normalized Lindeberg sum and its
exact vanishing under zero conditional tail moments. -/
theorem eq_main_martingale_Lindeberg
    {ι : Type*} (rounds : Finset ι) (regularWeight tailMoment : ι -> ℝ)
    (n : ℕ) :
    finiteMartingaleLindebergSum rounds regularWeight tailMoment n =
        (n : ℝ)⁻¹ * ∑ t ∈ rounds, regularWeight t * tailMoment t ∧
      ((∀ t ∈ rounds, tailMoment t = 0) ->
        finiteMartingaleLindebergSum rounds regularWeight tailMoment n = 0) := by
  exact ⟨rfl, fun htail =>
    finiteMartingaleLindebergSum_eq_zero
      rounds regularWeight tailMoment n htail⟩

/-- `eq:SI-full-LAN-Taylor`: deterministic finite-sum Taylor assembly. -/
theorem eq_SI_full_LAN_Taylor
    {ι : Type*} (rounds : Finset ι)
    (logRatio linear quadratic remainder : ι -> ℝ)
    (hstep : ∀ i ∈ rounds,
      logRatio i = linear i - (1 / 2 : ℝ) * quadratic i + remainder i) :
    (∑ i ∈ rounds, logRatio i) =
      (∑ i ∈ rounds, linear i) -
        (1 / 2 : ℝ) * (∑ i ∈ rounds, quadratic i) +
          ∑ i ∈ rounds, remainder i :=
  finite_LAN_Taylor_sum rounds logRatio linear quadratic remainder hstep

/-- `eq:SI-full-LAN-remainder`: total cubic remainder bound. -/
theorem eq_SI_full_LAN_remainder
    {ι : Type*} (rounds : Finset ι) (remainder : ι -> ℝ)
    (n : ℕ) (C radius : ℝ) (hn : 0 < n)
    (hC : 0 ≤ C) (hradius : 0 ≤ radius)
    (hcard : rounds.card ≤ n)
    (hrem : ∀ i ∈ rounds,
      |remainder i| ≤
        (C * radius ^ 3 / Real.sqrt (n : ℝ)) / (n : ℝ)) :
    |∑ i ∈ rounds, remainder i| ≤
      C * radius ^ 3 / Real.sqrt (n : ℝ) :=
  finite_LAN_cubic_remainder_bound rounds remainder n C radius hn
    hC hradius hcard hrem

/-- `eq:main-score-CLT`: martingale score CLT from the explicit Hall--Heyde
premises. -/
theorem eq_main_score_CLT
    {D : Type*} [Fintype D] [DecidableEq D]
    (problem : MartingaleCLTProblem D) (M : Matrix D D ℝ)
    (hM : M.PosDef)
    (hMDS : problem.IsSquareIntegrableMartingaleDifferenceArray)
    (hLindeberg : problem.HasConditionalLindeberg)
    (hCovariance : problem.ConditionalCovarianceConverges M) :
    problem.SumConvergesToGaussian M :=
  adaptiveScoreCLT_of_martingale_conditions
    problem M hM hMDS hLindeberg hCovariance

/-- `eq:SI-full-score-CLT`: supplementary statement of the same martingale
score CLT. -/
theorem eq_SI_full_score_CLT
    {D : Type*} [Fintype D] [DecidableEq D]
    (problem : MartingaleCLTProblem D) (M : Matrix D D ℝ)
    (hM : M.PosDef)
    (hMDS : problem.IsSquareIntegrableMartingaleDifferenceArray)
    (hLindeberg : problem.HasConditionalLindeberg)
    (hCovariance : problem.ConditionalCovarianceConverges M) :
    problem.SumConvergesToGaussian M :=
  adaptiveScoreCLT_of_martingale_conditions
    problem M hM hMDS hLindeberg hCovariance

/-- `eq:main-regular-LAN-step`: deterministic regular likelihood Taylor
assembly before stochastic limits are applied. -/
theorem eq_main_regular_LAN_step
    {ι : Type*} (rounds : Finset ι)
    (logRatio linear quadratic remainder : ι -> ℝ)
    (hstep : ∀ i ∈ rounds,
      logRatio i = linear i - (1 / 2 : ℝ) * quadratic i + remainder i) :
    (∑ i ∈ rounds, logRatio i) =
      (∑ i ∈ rounds, linear i) -
        (1 / 2 : ℝ) * (∑ i ∈ rounds, quadratic i) +
          ∑ i ∈ rounds, remainder i :=
  finite_LAN_Taylor_sum rounds logRatio linear quadratic remainder hstep

/-- `prop:primitive-adaptive-LAN`: score CLT plus convergence in probability
of the full LAN error under explicit sufficient conditions. -/
theorem prop_primitive_adaptive_LAN
    {D Omega : Type*} [Fintype D] [DecidableEq D]
    [MeasurableSpace Omega] {mu : Measure Omega}
    (problem : AdaptiveLANProblem D Omega mu) (M : Matrix D D ℝ)
    (hM : M.PosDef)
    (hMDS : problem.martingale.IsSquareIntegrableMartingaleDifferenceArray)
    (hLindeberg : problem.martingale.HasConditionalLindeberg)
    (hCovariance : problem.martingale.ConditionalCovarianceConverges M)
    (hregular : TendstoInMeasure mu problem.errors.regularTaylorError atTop 0)
    (hhessian : TendstoInMeasure mu problem.errors.hessianReplacementError atTop 0)
    (hexception : TendstoInMeasure mu problem.errors.exceptionalComparisonError atTop 0) :
    problem.martingale.SumConvergesToGaussian M ∧
      TendstoInMeasure mu problem.errors.fullLANError atTop 0 :=
  adaptive_quantum_LAN_of_conditions problem M hM hMDS hLindeberg
    hCovariance hregular hhessian hexception

/-- `eq:main-LAN-from-conditions`: full LAN-error convergence component of
the primitive adaptive-LAN proposition. -/
theorem eq_main_LAN_from_conditions
    {D Omega : Type*} [Fintype D] [DecidableEq D]
    [MeasurableSpace Omega] {mu : Measure Omega}
    (problem : AdaptiveLANProblem D Omega mu) (M : Matrix D D ℝ)
    (hM : M.PosDef)
    (hMDS : problem.martingale.IsSquareIntegrableMartingaleDifferenceArray)
    (hLindeberg : problem.martingale.HasConditionalLindeberg)
    (hCovariance : problem.martingale.ConditionalCovarianceConverges M)
    (hregular : TendstoInMeasure mu problem.errors.regularTaylorError atTop 0)
    (hhessian : TendstoInMeasure mu problem.errors.hessianReplacementError atTop 0)
    (hexception : TendstoInMeasure mu problem.errors.exceptionalComparisonError atTop 0) :
    TendstoInMeasure mu problem.errors.fullLANError atTop 0 :=
  (adaptive_quantum_LAN_of_conditions problem M hM hMDS hLindeberg
    hCovariance hregular hhessian hexception).2

/-- `prop:SI-adaptive-LAN`: supplementary form of the same general adaptive
LAN sufficient-condition theorem. -/
theorem prop_SI_adaptive_LAN
    {D Omega : Type*} [Fintype D] [DecidableEq D]
    [MeasurableSpace Omega] {mu : Measure Omega}
    (problem : AdaptiveLANProblem D Omega mu) (M : Matrix D D ℝ)
    (hM : M.PosDef)
    (hMDS : problem.martingale.IsSquareIntegrableMartingaleDifferenceArray)
    (hLindeberg : problem.martingale.HasConditionalLindeberg)
    (hCovariance : problem.martingale.ConditionalCovarianceConverges M)
    (hregular : TendstoInMeasure mu problem.errors.regularTaylorError atTop 0)
    (hhessian : TendstoInMeasure mu problem.errors.hessianReplacementError atTop 0)
    (hexception : TendstoInMeasure mu problem.errors.exceptionalComparisonError atTop 0) :
    problem.martingale.SumConvergesToGaussian M ∧
      TendstoInMeasure mu problem.errors.fullLANError atTop 0 :=
  adaptive_quantum_LAN_of_conditions problem M hM hMDS hLindeberg
    hCovariance hregular hhessian hexception

/-- `eq:SI-adaptive-LAN`: uniform LAN-error convergence component. -/
theorem eq_SI_adaptive_LAN
    {D Omega : Type*} [Fintype D] [DecidableEq D]
    [MeasurableSpace Omega] {mu : Measure Omega}
    (problem : AdaptiveLANProblem D Omega mu) (M : Matrix D D ℝ)
    (hM : M.PosDef)
    (hMDS : problem.martingale.IsSquareIntegrableMartingaleDifferenceArray)
    (hLindeberg : problem.martingale.HasConditionalLindeberg)
    (hCovariance : problem.martingale.ConditionalCovarianceConverges M)
    (hregular : TendstoInMeasure mu problem.errors.regularTaylorError atTop 0)
    (hhessian : TendstoInMeasure mu problem.errors.hessianReplacementError atTop 0)
    (hexception : TendstoInMeasure mu problem.errors.exceptionalComparisonError atTop 0) :
    TendstoInMeasure mu problem.errors.fullLANError atTop 0 :=
  (adaptive_quantum_LAN_of_conditions problem M hM hMDS hLindeberg
    hCovariance hregular hhessian hexception).2

end

/-! ## Protocol-specific regularity equations -/

theorem eq_main_SDQM_defect
    {Y D : Type*} [Fintype Y] [Fintype D]
    (pLocal pBase : Y -> Real) (score : Y -> D -> Real)
    (u : D -> Real) :
    finiteDQMDefect pLocal pBase score u =
      ∑ y, (Real.sqrt (pLocal y) - Real.sqrt (pBase y) -
        (1 / 2 : Real) * (∑ j, u j * score y j) *
          Real.sqrt (pBase y)) ^ 2 :=
  rfl

theorem eq_main_SDQM_sum
    {Omega I : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (rounds : Nat -> Finset I)
    (defect : Nat -> Omega -> I -> Real) (B : Real)
    (hB : 0 <= B)
    (hcard : ∀ n, (rounds n).card <= n)
    (hnonnegative : ∀ n omega i, i ∈ rounds n -> 0 <= defect n omega i)
    (hrate : ∀ n, 0 < n -> ∀ omega i, i ∈ rounds n ->
      defect n omega i <= B / (n : Real) ^ 2) :
    TendstoInMeasure mu
      (fun n omega => ∑ i ∈ rounds n, defect n omega i) atTop 0 :=
  protocolDQMRate_tendstoInMeasure
    mu rounds defect B hB hcard hnonnegative hrate

theorem eq_SI_protocol_DQM_defect
    {Y D : Type*} [Fintype Y] [Fintype D]
    (pLocal pBase : Y -> Real) (score : Y -> D -> Real)
    (u : D -> Real) :
    finiteDQMDefect pLocal pBase score u =
      ∑ y, (Real.sqrt (pLocal y) - Real.sqrt (pBase y) -
        (1 / 2 : Real) * (∑ j, u j * score y j) *
          Real.sqrt (pBase y)) ^ 2 :=
  eq_main_SDQM_defect pLocal pBase score u

theorem eq_SI_protocol_DQM_rate
    {Y D : Type*} [Fintype Y] [Fintype D]
    (pLocal pBase : Y -> Real) (score : Y -> D -> Real)
    (u : D -> Real) (n : Nat) (A : Real) (hA : 0 <= A)
    (hrem : ∀ y,
      |finiteDQMResidual pLocal pBase score u y| <= A / (n : Real)) :
    finiteDQMDefect pLocal pBase score u <=
      ((Fintype.card Y : Real) * A ^ 2) / (n : Real) ^ 2 :=
  finiteDQMDefect_le_card_mul_sq_div
    pLocal pBase score u n A hA hrem

theorem eq_SI_protocol_SDQM_from_rate
    {Omega I : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (rounds : Nat -> Finset I)
    (defect : Nat -> Omega -> I -> Real) (B : Real)
    (hB : 0 <= B)
    (hcard : ∀ n, (rounds n).card <= n)
    (hnonnegative : ∀ n omega i, i ∈ rounds n -> 0 <= defect n omega i)
    (hrate : ∀ n, 0 < n -> ∀ omega i, i ∈ rounds n ->
      defect n omega i <= B / (n : Real) ^ 2) :
    TendstoInMeasure mu
      (fun n omega => ∑ i ∈ rounds n, defect n omega i) atTop 0 :=
  eq_main_SDQM_sum mu rounds defect B hB hcard hnonnegative hrate

theorem eq_SI_protocol_score_centering
    {Theta M Y D : Type*} [Fintype Y]
    (model : FiniteScoreModel Theta M Y D)
    (theta : Theta) (m : M) (regularWeight : Real) :
    finiteOutcomeExpectation model.outcome theta m
      (fun y => regularWeight • model.score theta m y) = 0 :=
  protocolRegularScore_centered model theta m regularWeight

theorem eq_SI_mixed_probability_floor_LAN
    (theta axis : Fin 3 -> Real)
    (haxis : blochNormSq axis <= 1) (y : BinaryOutcome) :
    binaryBornProbability (blochDot theta axis) y =
        (1 + y.sign * blochDot theta axis) / 2 ∧
      (1 - blochNorm theta) / 2 <=
        binaryBornProbability (blochDot theta axis) y := by
  exact ⟨rfl, mixedProjectiveBornProbability_floor theta axis haxis y⟩

theorem eq_SI_mixed_info_bound
    (theta axis : Fin 3 -> Real)
    (hinterior : blochNormSq theta < 1)
    (haxis : blochNormSq axis = 1) :
    mixedInformationFrobeniusNorm (mixedAxisFisher theta axis) <=
      (1 - blochNormSq theta)⁻¹ :=
  mixedAxisInformationFrobeniusNorm_le
    theta axis hinterior haxis

theorem eq_SI_rank_one_Bures_LAN
    {d : Nat} (a : Real) (h : TangentIndex d -> Real)
    (hchart : a ^ 2 * tangentRadiusSq h <= 4) :
    0 <= buresChartLoss (a • h) -
        (a ^ 2 * tangentRadiusSq h) / 4 ∧
      buresChartLoss (a • h) -
        (a ^ 2 * tangentRadiusSq h) / 4 <=
          a ^ 4 * (tangentRadiusSq h) ^ 2 / 16 :=
  buresChartLoss_smul_remainder_bounds a h hchart

theorem eq_main_local_Bures_bound
    {d : Nat} (shots : Nat) (hshots : 0 < shots)
    (a : Real) (h : TangentIndex d -> Real) (R : Real)
    (hR : 0 <= R) (hradius : tangentRadiusSq h <= R)
    (ha : a ^ 2 = ((shots : Real))⁻¹)
    (hchart : a ^ 2 * tangentRadiusSq h <= 4) :
    buresChartLoss (a • h) <=
      (R / 4 + R ^ 2 / 16) / (shots : Real) :=
  pureProtocolBuresCompact_upper
    shots hshots a h R hR hradius ha hchart

theorem eq_SI_uniform_Bures_local
    {d : Nat} (shots : Nat) (hshots : 0 < shots)
    (a : Real) (h : TangentIndex d -> Real) (R : Real)
    (hR : 0 <= R) (hradius : tangentRadiusSq h <= R)
    (ha : a ^ 2 = ((shots : Real))⁻¹)
    (hchart : a ^ 2 * tangentRadiusSq h <= 4) :
    buresChartLoss (a • h) <=
      (R / 4 + R ^ 2 / 16) / (shots : Real) :=
  eq_main_local_Bures_bound
    shots hshots a h R hR hradius ha hchart

theorem eq_SI_protocol_rankOne_Bures_verified
    {d : Nat} (shots : Nat) (hshots : 0 < shots)
    (a : Real) (h : TangentIndex d -> Real) (R : Real)
    (hR : 0 <= R) (hradius : tangentRadiusSq h <= R)
    (ha : a ^ 2 = ((shots : Real))⁻¹)
    (hchart : a ^ 2 * tangentRadiusSq h <= 4) :
    buresChartLoss (a • h) <=
      (R / 4 + R ^ 2 / 16) / (shots : Real) :=
  eq_SI_uniform_Bures_local
    shots hshots a h R hR hradius ha hchart

theorem eq_SI_protocol_mixed_Bures_verified_scalar
    (shots : Nat) (hshots : 0 < shots)
    (a : Real) (theta h : Fin 3 -> Real) (R : Real)
    (hinterior : blochNormSq theta < 1)
    (hR : 0 <= R) (hradius : blochNormSq h <= R)
    (ha : a ^ 2 = ((shots : Real))⁻¹)
    (hlocal :
      2 * |blochDot theta (a • h)| + blochNormSq (a • h) <=
        1 - blochNormSq theta) :
    mixedBlochBuresSq theta (a • h) <=
      (2 * R / (1 - blochNormSq theta)) / (shots : Real) :=
  mixedBlochBuresSq_compact_upper
    shots hshots a theta h R hinterior hR hradius ha hlocal

/-- The two deterministic protocol branches of the local Bures condition.
The mixed component is currently stated in the scalar Bloch-fidelity form;
the matrix Uhlmann-fidelity identification is a separate pending bridge. -/
theorem eq_SI_protocol_Bures_verified
    (mixedShots : Nat) (hmixedShots : 0 < mixedShots)
    (mixedScale : Real) (theta mixedH : Fin 3 -> Real) (mixedR : Real)
    (hinterior : blochNormSq theta < 1)
    (hmixedR : 0 <= mixedR) (hmixedRadius : blochNormSq mixedH <= mixedR)
    (hmixedScale : mixedScale ^ 2 = ((mixedShots : Real))⁻¹)
    (hmixedLocal :
      2 * |blochDot theta (mixedScale • mixedH)| +
          blochNormSq (mixedScale • mixedH) <=
        1 - blochNormSq theta)
    {d : Nat} (pureShots : Nat) (hpureShots : 0 < pureShots)
    (pureScale : Real) (pureH : TangentIndex d -> Real) (pureR : Real)
    (hpureR : 0 <= pureR) (hpureRadius : tangentRadiusSq pureH <= pureR)
    (hpureScale : pureScale ^ 2 = ((pureShots : Real))⁻¹)
    (hpureChart : pureScale ^ 2 * tangentRadiusSq pureH <= 4) :
    mixedBlochBuresSq theta (mixedScale • mixedH) <=
        (2 * mixedR / (1 - blochNormSq theta)) / (mixedShots : Real) ∧
      buresChartLoss (pureScale • pureH) <=
        (pureR / 4 + pureR ^ 2 / 16) / (pureShots : Real) :=
  ⟨eq_SI_protocol_mixed_Bures_verified_scalar
      mixedShots hmixedShots mixedScale theta mixedH mixedR hinterior
        hmixedR hmixedRadius hmixedScale hmixedLocal,
    eq_SI_protocol_rankOne_Bures_verified
      pureShots hpureShots pureScale pureH pureR hpureR hpureRadius
        hpureScale hpureChart⟩

end QubitOracle.Paper.Label
