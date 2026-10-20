import QubitOracle.Paper.SourceFaithfulRLSConfidenceEllipsoid
import QubitOracle.Paper.OneQubitPersistentExcitation
import QubitOracle.Paper.ControllerInformationConvergenceLabels

/-!
# One-qubit APS confidence to controller-rate bridge

This module connects the cited Abbasi--Yadkori--Pal--Szepesvari (2011)
confidence ellipsoid to the concrete non-LAN controller interface used by the
paper.  The remaining protocol-specific inputs are visible: measurability of
the confidence events, summability of their confidence levels, and a
deterministic rate bound on each good event.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace QubitOracle.Paper

noncomputable section

open PopularRLSConditions SourceFaithfulSelfNormalized

/-- At every time, the source-faithful APS good event supplies exactly the
one-qubit self-normalized confidence certificate used by the deterministic
persistent-excitation reduction. -/
theorem aps2011GoodEvent_oneQubitSelfNormalizedConfidence
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {R : Real}
    (data : SelfNormalizedMartingaleData Omega 3 mu R)
    (truth : Fin 3 -> Real) (observation : Nat -> Omega -> Real)
    (regularization parameterRadius delta : Real)
    (omega : Omega)
    (hgood : omega ∈ aps2011Theorem2GoodEvent data truth observation
      regularization parameterRadius delta)
    (t : Nat) :
    OneQubitSelfNormalizedConfidence
      (aps2011Theorem2Gram data regularization t omega)
      (aps2011Theorem2Estimator data observation regularization t omega)
      truth
      (aps2011Theorem2Radius data regularization parameterRadius delta
        t omega) := by
  let q : Real :=
    weightedNormSq
      (aps2011Theorem2Gram data regularization t omega)
      (aps2011Theorem2Error data truth observation regularization t omega)
  have hsqrt_le : Real.sqrt q <=
      aps2011Theorem2Radius data regularization parameterRadius delta
        t omega := by
    simpa [aps2011Theorem2GoodEvent,
      aps2011Theorem2WeightedError, q] using hgood t
  have hradius_nonnegative : 0 <=
      aps2011Theorem2Radius data regularization parameterRadius delta
        t omega :=
    (Real.sqrt_nonneg q).trans hsqrt_le
  refine ⟨hradius_nonnegative, ?_⟩
  have hq_le : q <=
      (aps2011Theorem2Radius data regularization parameterRadius delta
        t omega) ^ 2 := by
    by_cases hq : 0 <= q
    · have hsqrt_sq : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq
      nlinarith [Real.sqrt_nonneg q]
    · have hq_nonpos : q <= 0 := le_of_not_ge hq
      exact hq_nonpos.trans (sq_nonneg _)
  have herror :
      oneQubitRLSError
          (aps2011Theorem2Estimator data observation regularization t omega)
          truth =
        aps2011Theorem2Error data truth observation regularization t omega :=
    rfl
  change weightedNormSq
      (aps2011Theorem2Gram data regularization t omega)
      (oneQubitRLSError
        (aps2011Theorem2Estimator data observation regularization t omega)
        truth) <=
      (aps2011Theorem2Radius data regularization parameterRadius delta
        t omega) ^ 2
  rw [herror]
  exact hq_le

/-- A measurable confidence event of probability at least `1 - delta` has
failure probability at most `delta`.  Measurability is stated explicitly
because it is needed by complement arithmetic and is protocol-specific. -/
theorem confidenceBadEvent_measure_le
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (goodEvent : Set Omega) (delta : Real)
    (hMeasurable : MeasurableSet goodEvent)
    (hDeltaLeOne : delta <= 1)
    (hConfidence : ENNReal.ofReal (1 - delta) <= mu goodEvent) :
    mu goodEventᶜ <= ENNReal.ofReal delta := by
  rw [measure_compl hMeasurable (measure_ne_top mu goodEvent)]
  rw [measure_univ]
  calc
    1 - mu goodEvent <= 1 - ENNReal.ofReal (1 - delta) :=
      tsub_le_tsub_left hConfidence 1
    _ = ENNReal.ofReal delta := by
      have hnonnegative : 0 <= 1 - delta := sub_nonneg.mpr hDeltaLeOne
      symm
      simpa using (ENNReal.ofReal_sub (p := 1) hnonnegative)

/-- Summable confidence levels imply summable failure probabilities.  This is
the exact Borel--Cantelli input used by `ControllerRatePrimitives`. -/
theorem confidenceBadEvents_tsum_ne_top
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (goodEvent : Nat -> Set Omega) (delta : Nat -> Real)
    (hMeasurable : forall n, MeasurableSet (goodEvent n))
    (hDeltaLeOne : forall n, delta n <= 1)
    (hConfidence : forall n,
      ENNReal.ofReal (1 - delta n) <= mu (goodEvent n))
    (hDeltaSummable : (∑' n, ENNReal.ofReal (delta n)) ≠ ⊤) :
    (∑' n, mu (goodEvent n)ᶜ) ≠ ⊤ := by
  have hsum_le :
      (∑' n, mu (goodEvent n)ᶜ) <=
        ∑' n, ENNReal.ofReal (delta n) :=
    ENNReal.tsum_le_tsum fun n =>
      confidenceBadEvent_measure_le (goodEvent n) (delta n)
        (hMeasurable n) (hDeltaLeOne n) (hConfidence n)
  intro htop
  rw [htop] at hsum_le
  exact hDeltaSummable (top_unique hsum_le)

/-! ## Concrete polynomial confidence schedule -/

/-- The standard summable schedule `delta_n = (n + 2)^{-2}`.  Unlike a
geometric schedule, its logarithm remains of order `log n`, which preserves
the desired RLS rate. -/
def oneQubitPolynomialConfidenceLevel (n : Nat) : Real :=
  1 / (((n + 2 : Nat) : Real) ^ 2)

theorem oneQubitPolynomialConfidenceLevel_positive (n : Nat) :
    0 < oneQubitPolynomialConfidenceLevel n := by
  unfold oneQubitPolynomialConfidenceLevel
  positivity

theorem oneQubitPolynomialConfidenceLevel_lt_one (n : Nat) :
    oneQubitPolynomialConfidenceLevel n < 1 := by
  have hnNat : 2 <= n + 2 := by omega
  have hn : (2 : Real) <= ((n + 2 : Nat) : Real) := by
    exact_mod_cast hnNat
  have hden : 1 < (((n + 2 : Nat) : Real) ^ 2) := by
    nlinarith
  rw [oneQubitPolynomialConfidenceLevel,
    div_lt_iff₀ (by positivity : 0 < (((n + 2 : Nat) : Real) ^ 2))]
  simpa using hden

theorem oneQubitPolynomialConfidenceLevel_summable :
    Summable oneQubitPolynomialConfidenceLevel := by
  have hbase : Summable (fun n : Nat => 1 / ((n : Real) ^ 2)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift :
      Summable (fun n : Nat => 1 / (((n + 2 : Nat) : Real) ^ 2)) :=
    (summable_nat_add_iff 2).mpr hbase
  change Summable (fun n : Nat => 1 / (((n + 2 : Nat) : Real) ^ 2))
  exact hshift

theorem oneQubitPolynomialConfidenceLevel_tsum_ne_top :
    (∑' n, ENNReal.ofReal (oneQubitPolynomialConfidenceLevel n)) ≠ (⊤ : ENNReal) :=
  oneQubitPolynomialConfidenceLevel_summable.tsum_ofReal_ne_top

/-! ## Concrete exploration rate -/

/-- A terminal exploration schedule strong enough for the paper's
`n^(1/4)` localization requirement. -/
def oneQubitThreeQuarterExploration (n : Nat) : Real :=
  (n : Real) ^ ((3 : Real) / 4)

/-- The terminal condition itself also implies the weaker, unscaled
controller rate required by `ControllerRatePrimitives`. -/
theorem controllerRateScale_tendsto_zero_of_terminal
    (expectedExploration : Nat -> Real)
    (hterminal : TerminalExplorationRate expectedExploration) :
    Tendsto (controllerRateScale expectedExploration) atTop (nhds 0) := by
  have hscaled : Tendsto
      (fun n : Nat =>
        natQuarterPower n * controllerRateScale expectedExploration n)
      atTop (nhds 0) := by
    simpa [controllerRateScale] using
      nquarter_rate_tendsto_zero expectedExploration hterminal
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n => Real.sqrt_nonneg _
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnReal : (1 : Real) <= (n : Real) := by exact_mod_cast hn
    have hsqrtOne : 1 <= Real.sqrt (n : Real) := by
      simpa using Real.sqrt_le_sqrt hnReal
    have hquarterOne : 1 <= natQuarterPower n := by
      simpa [natQuarterPower] using Real.sqrt_le_sqrt hsqrtOne
    have hscaleNonnegative :
        0 <= controllerRateScale expectedExploration n :=
      Real.sqrt_nonneg _
    simpa using
      (mul_le_mul_of_nonneg_right hquarterOne hscaleNonnegative)
  · exact hscaled

/-- The concrete `n^(3/4)` exploration mass satisfies
`sqrt n * log n / E_n -> 0`. -/
theorem oneQubitThreeQuarterExploration_terminal :
    TerminalExplorationRate oneQubitThreeQuarterExploration := by
  have hreal : Tendsto
      (fun x : Real => Real.log x / x ^ ((1 : Real) / 4))
      atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : Real) < 1 / 4)).tendsto_div_nhds_zero
  have hnat : Tendsto
      (fun n : Nat =>
        Real.log (n : Real) / (n : Real) ^ ((1 : Real) / 4))
      atTop (nhds 0) :=
    hreal.comp tendsto_natCast_atTop_atTop
  change Tendsto
    (fun n : Nat =>
      Real.sqrt (n : Real) * Real.log (n : Real) /
        oneQubitThreeQuarterExploration n)
    atTop (nhds 0)
  apply hnat.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hx : 0 < (n : Real) := by exact_mod_cast hn
  have h14 : (n : Real) ^ ((1 : Real) / 4) ≠ 0 :=
    (Real.rpow_pos_of_pos hx _).ne'
  have h34 : (n : Real) ^ ((3 : Real) / 4) ≠ 0 :=
    (Real.rpow_pos_of_pos hx _).ne'
  have hpow :
      (n : Real) ^ ((1 : Real) / 2) *
          (n : Real) ^ ((1 : Real) / 4) =
        (n : Real) ^ ((3 : Real) / 4) := by
    rw [← Real.rpow_add hx]
    norm_num
  rw [oneQubitThreeQuarterExploration, Real.sqrt_eq_rpow]
  apply (div_eq_div_iff h14 h34).2
  calc
    Real.log (n : Real) * (n : Real) ^ ((3 : Real) / 4) =
        Real.log (n : Real) *
          ((n : Real) ^ ((1 : Real) / 2) *
            (n : Real) ^ ((1 : Real) / 4)) := by rw [hpow]
    _ = ((n : Real) ^ ((1 : Real) / 2) * Real.log (n : Real)) *
          (n : Real) ^ ((1 : Real) / 4) := by ring

theorem oneQubitThreeQuarterExploration_controllerRate_tendsto_zero :
    Tendsto (controllerRateScale oneQubitThreeQuarterExploration)
      atTop (nhds 0) :=
  controllerRateScale_tendsto_zero_of_terminal
    oneQubitThreeQuarterExploration
    oneQubitThreeQuarterExploration_terminal

theorem oneQubitThreeQuarterExploration_eventually_positive :
    ∀ᶠ n in atTop, 0 < oneQubitThreeQuarterExploration n := by
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _

theorem oneQubitThreeQuarterExploration_log_ratio_tendsto_zero :
    Tendsto
      (fun n : Nat =>
        Real.log (n : Real) / oneQubitThreeQuarterExploration n)
      atTop (nhds 0) := by
  have hreal : Tendsto
      (fun x : Real => Real.log x / x ^ ((3 : Real) / 4))
      atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : Real) < 3 / 4)).tendsto_div_nhds_zero
  simpa only [Function.comp_def, oneQubitThreeQuarterExploration] using
    hreal.comp tendsto_natCast_atTop_atTop

theorem oneQubitThreeQuarterExploration_fraction_tendsto_zero :
    Tendsto
      (fun n : Nat => oneQubitThreeQuarterExploration n / (n : Real))
      atTop (nhds 0) := by
  have hreal : Tendsto
      (fun x : Real => x ^ (-((1 : Real) / 4))) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by norm_num : (0 : Real) < 1 / 4)
  have hnat : Tendsto
      (fun n : Nat => (n : Real) ^ (-((1 : Real) / 4)))
      atTop (nhds 0) :=
    hreal.comp tendsto_natCast_atTop_atTop
  apply hnat.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hx : 0 < (n : Real) := by exact_mod_cast hn
  calc
    (n : Real) ^ (-((1 : Real) / 4)) =
        (n : Real) ^ (((3 : Real) / 4) - 1) := by norm_num
    _ = (n : Real) ^ ((3 : Real) / 4) / (n : Real) ^ (1 : Real) :=
      Real.rpow_sub hx _ _
    _ = oneQubitThreeQuarterExploration n / (n : Real) := by
      rw [Real.rpow_one, oneQubitThreeQuarterExploration]

/-- Fully discharged paper-specific RLS schedule conditions for the concrete
`n^(3/4)` exploration mass. -/
theorem oneQubitThreeQuarterRLSApplicationConditions :
    PaperRLSApplicationConditions oneQubitThreeQuarterExploration :=
  { expectedExploration_positive :=
      oneQubitThreeQuarterExploration_eventually_positive
    persistentExploration :=
      oneQubitThreeQuarterExploration_log_ratio_tendsto_zero
    vanishingExplorationFraction :=
      oneQubitThreeQuarterExploration_fraction_tendsto_zero }

/-- Confidence events with a summable failure schedule and a deterministic
good-event rate produce the complete controller-rate certificate. -/
def controllerRatePrimitives_of_confidenceEvents
    {Omega E : Type*} [MeasurableSpace Omega] [NormedAddCommGroup E]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (controller : Nat -> Omega -> E) (truth : E)
    (expectedExploration : Nat -> Real)
    (goodEvent : Nat -> Set Omega) (delta : Nat -> Real)
    (hMeasurable : forall n, MeasurableSet (goodEvent n))
    (hDeltaLeOne : forall n, delta n <= 1)
    (hConfidence : forall n,
      ENNReal.ofReal (1 - delta n) <= mu (goodEvent n))
    (hDeltaSummable : (∑' n, ENNReal.ofReal (delta n)) ≠ ⊤)
    (constant : Real) (hConstant : 0 <= constant)
    (hBound : forall n omega, omega ∈ goodEvent n ->
      ‖controller n omega - truth‖ <=
        constant * controllerRateScale expectedExploration n)
    (hRate : Tendsto (controllerRateScale expectedExploration)
      atTop (nhds 0)) :
    ControllerRatePrimitives mu controller truth expectedExploration := by
  refine
    { badEvent := fun n => (goodEvent n)ᶜ
      badEvent_tsum_ne_top := confidenceBadEvents_tsum_ne_top
        goodEvent delta hMeasurable hDeltaLeOne hConfidence hDeltaSummable
      constant := constant
      constant_nonnegative := hConstant
      bound_on_good := ?_
      rate_tendsto_zero := hRate }
  intro n omega hnotBad
  apply hBound n omega
  simpa using hnotBad

/-- Source-cited one-qubit RLS controller theorem.  Its only scientific axiom
is the exact APS 2011 Theorem 2 confidence ellipsoid; all additional
paper-specific assumptions are displayed as arguments. -/
def controllerRatePrimitives_of_aps2011_theorem2
    {Omega E : Type*} [MeasurableSpace Omega] [NormedAddCommGroup E]
    {mu : Measure Omega} [IsProbabilityMeasure mu] {R : Real}
    (data : SelfNormalizedMartingaleData Omega 3 mu R)
    (hR : 0 <= R)
    (thetaStar : Fin 3 -> Real) (observation : Nat -> Omega -> Real)
    (hLinearObservation : forall k,
      observation (k + 1) =ᵐ[mu] fun omega =>
        dotProduct (data.regressor k omega) thetaStar +
          data.noise (k + 1) omega)
    (regularization : Real) (hRegularization : 0 < regularization)
    (parameterRadius : Real) (hParameterRadius : 0 <= parameterRadius)
    (hParameterBound : finiteEuclideanNorm thetaStar <= parameterRadius)
    (controller : Nat -> Omega -> E) (truth : E)
    (expectedExploration : Nat -> Real) (delta : Nat -> Real)
    (hDelta0 : forall n, 0 < delta n)
    (hDelta1 : forall n, delta n < 1)
    (hGoodMeasurable : forall n, MeasurableSet
      (aps2011Theorem2GoodEvent data thetaStar observation
        regularization parameterRadius (delta n)))
    (hDeltaSummable : (∑' n, ENNReal.ofReal (delta n)) ≠ ⊤)
    (constant : Real) (hConstant : 0 <= constant)
    (hBound : forall n omega,
      omega ∈ aps2011Theorem2GoodEvent data thetaStar observation
        regularization parameterRadius (delta n) ->
      ‖controller n omega - truth‖ <=
        constant * controllerRateScale expectedExploration n)
    (hRate : Tendsto (controllerRateScale expectedExploration)
      atTop (nhds 0)) :
    ControllerRatePrimitives mu controller truth expectedExploration := by
  have hConfidence : forall n,
      ENNReal.ofReal (1 - delta n) <=
        mu (aps2011Theorem2GoodEvent data thetaStar observation
          regularization parameterRadius (delta n)) := by
    intro n
    exact
      abbasiYadkoriPalSzepesvari2011_theorem2_confidenceEllipsoid_external
        data hR thetaStar observation hLinearObservation regularization
        hRegularization parameterRadius hParameterRadius hParameterBound
        (delta n) (hDelta0 n) (hDelta1 n)
  exact controllerRatePrimitives_of_confidenceEvents
    controller truth expectedExploration
    (fun n => aps2011Theorem2GoodEvent data thetaStar observation
      regularization parameterRadius (delta n))
    delta hGoodMeasurable (fun n => (hDelta1 n).le) hConfidence
    hDeltaSummable constant hConstant hBound hRate

/-- On an APS good event, an exact Pauli-block Gram identity and the displayed
determinant-radius estimate give the concrete Euclidean RLS rate. -/
theorem aps2011GoodEvent_pauliBlock_euclideanRate
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {R : Real}
    (data : SelfNormalizedMartingaleData Omega 3 mu R)
    (truth : Fin 3 -> Real) (observation : Nat -> Omega -> Real)
    (regularization parameterRadius delta : Real)
    (t blocks : Nat) (hblocks : 0 < blocks) (omega : Omega)
    (hgood : omega ∈ aps2011Theorem2GoodEvent data truth observation
      regularization parameterRadius delta)
    (hGram : aps2011Theorem2Gram data regularization t omega =
      pauliForcedExplorationGram blocks)
    (C : Real)
    (hRadiusSq :
      (aps2011Theorem2Radius data regularization parameterRadius delta
        t omega) ^ 2 <=
      C ^ 2 * Real.log
        ((pauliForcedExplorationRoundCount blocks : Real) + 1)) :
    finiteEuclideanNorm
        (oneQubitRLSError
          (aps2011Theorem2Estimator data observation regularization t omega)
          truth) <=
      Real.sqrt
        (C ^ 2 * Real.log
          ((pauliForcedExplorationRoundCount blocks : Real) + 1) /
            (blocks : Real)) := by
  apply pauliForcedExploration_RLSEuclideanError_logRate
    blocks hblocks
    (aps2011Theorem2Estimator data observation regularization t omega)
    truth
    (aps2011Theorem2Radius data regularization parameterRadius delta t omega)
    C
  · rw [← hGram]
    exact aps2011GoodEvent_oneQubitSelfNormalizedConfidence
      data truth observation regularization parameterRadius delta omega hgood t
  · exact hRadiusSq

end

end QubitOracle.Paper
