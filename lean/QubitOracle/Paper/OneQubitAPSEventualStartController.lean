import QubitOracle.Paper.ControllerErrorMeasurable
import QubitOracle.Paper.OneQubitAPSEventualController

namespace QubitOracle.Paper

open MeasureTheory

/-- Confidence levels that discard an arbitrary finite startup prefix. -/
noncomputable def oneQubitGuardedPolynomialConfidenceLevelFrom (start n : ℕ) : ℝ :=
  if start ≤ n then oneQubitPolynomialConfidenceLevel n else 1

theorem oneQubitGuardedPolynomialConfidenceLevelFrom_summable (start : ℕ) :
    Summable (oneQubitGuardedPolynomialConfidenceLevelFrom start) := by
  apply (summable_nat_add_iff start).mp
  have htail : Summable (fun n => oneQubitPolynomialConfidenceLevel (n + start)) :=
    (summable_nat_add_iff start).mpr oneQubitPolynomialConfidenceLevel_summable
  simpa [oneQubitGuardedPolynomialConfidenceLevelFrom] using htail

theorem oneQubitGuardedPolynomialConfidenceLevelFrom_tsum_ne_top (start : ℕ) :
    ∑' n, ENNReal.ofReal (oneQubitGuardedPolynomialConfidenceLevelFrom start n) ≠ ⊤ :=
  Summable.tsum_ofReal_ne_top
    (oneQubitGuardedPolynomialConfidenceLevelFrom_summable start)

/-- Before `start` the good event is empty, so no finite-time estimator bound is required. -/
def oneQubitAPSGoodEventFrom
    {Omega : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 → ℝ} {axis : ℕ → Omega → Fin 3 → ℝ}
    {outcome : ℕ → Omega → QubitRLSOutcome}
    (protocol : BinaryQubitRLSReducedProbabilityPremises Omega mu theta axis outcome)
    (hTheta : blochNormSq theta ≤ 1) (regularization : ℝ) (start n : ℕ) : Set Omega :=
  if start ≤ n then
    PopularRLSConditions.aps2011Theorem2GoodEvent
      (protocol.toSelfNormalizedMartingaleData hTheta) theta
      (oneQubitRLSObservation outcome) regularization 1
      (oneQubitPolynomialConfidenceLevel n)
  else ∅

theorem oneQubitAPSGoodEventFrom_measurable
    {Omega : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 → ℝ} {axis : ℕ → Omega → Fin 3 → ℝ}
    {outcome : ℕ → Omega → QubitRLSOutcome}
    (protocol : BinaryQubitRLSReducedProbabilityPremises Omega mu theta axis outcome)
    (hTheta : blochNormSq theta ≤ 1) (regularization : ℝ) (start n : ℕ) :
    MeasurableSet (oneQubitAPSGoodEventFrom protocol hTheta regularization start n) := by
  by_cases hn : start ≤ n
  · simpa [oneQubitAPSGoodEventFrom, hn] using
      protocol.measurableSet_apsGoodEvent hTheta regularization 1
        (oneQubitPolynomialConfidenceLevel n)
  · simp [oneQubitAPSGoodEventFrom, hn]

theorem oneQubitAPSGoodEventFrom_confidence
    {Omega : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 → ℝ} {axis : ℕ → Omega → Fin 3 → ℝ}
    {outcome : ℕ → Omega → QubitRLSOutcome}
    (protocol : BinaryQubitRLSReducedProbabilityPremises Omega mu theta axis outcome)
    (hTheta : blochNormSq theta ≤ 1) (regularization : ℝ)
    (hRegularization : 0 < regularization) (start n : ℕ) :
    ENNReal.ofReal (1 - oneQubitGuardedPolynomialConfidenceLevelFrom start n) ≤
      mu (oneQubitAPSGoodEventFrom protocol hTheta regularization start n) := by
  by_cases hn : start ≤ n
  · simp only [oneQubitGuardedPolynomialConfidenceLevelFrom,
      oneQubitAPSGoodEventFrom, hn, if_true]
    exact PopularRLSConditions.abbasiYadkoriPalSzepesvari2011_theorem2_confidenceEllipsoid_external
      (protocol.toSelfNormalizedMartingaleData hTheta) (by norm_num) theta
      (oneQubitRLSObservation outcome) (protocol.linearObservation_ae hTheta)
      regularization hRegularization 1 (by norm_num)
      (oneQubitFiniteEuclideanNorm_le_one_of_physicalBloch theta hTheta)
      (oneQubitPolynomialConfidenceLevel n)
      (oneQubitPolynomialConfidenceLevel_positive n)
      (oneQubitPolynomialConfidenceLevel_lt_one n)
  · simp [oneQubitGuardedPolynomialConfidenceLevelFrom,
      oneQubitAPSGoodEventFrom, hn]

noncomputable def oneQubitBornRLSControllerRatePrimitives_of_aps2011_eventualStart
    {Omega E : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    [NormedAddCommGroup E] {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 → ℝ} {axis : ℕ → Omega → Fin 3 → ℝ}
    {outcome : ℕ → Omega → QubitRLSOutcome}
    (protocol : BinaryQubitRLSReducedProbabilityPremises Omega mu theta axis outcome)
    (hTheta : blochNormSq theta ≤ 1) (regularization : ℝ)
    (hRegularization : 0 < regularization) (start : ℕ)
    (controller : ℕ → Omega → E) (truth : E) (constant : ℝ)
    (hConstant : 0 ≤ constant)
    (hBound : ∀ n, start ≤ n → ∀ omega ∈
      PopularRLSConditions.aps2011Theorem2GoodEvent
        (protocol.toSelfNormalizedMartingaleData hTheta) theta
        (oneQubitRLSObservation outcome) regularization 1
        (oneQubitPolynomialConfidenceLevel n),
      ‖controller n omega - truth‖ ≤
        constant * controllerRateScale oneQubitThreeQuarterExploration n) :
    ControllerRatePrimitives mu controller truth oneQubitThreeQuarterExploration := by
  apply controllerRatePrimitives_of_confidenceEvents
    controller truth oneQubitThreeQuarterExploration
    (oneQubitAPSGoodEventFrom protocol hTheta regularization start)
    (oneQubitGuardedPolynomialConfidenceLevelFrom start)
  · exact fun n => oneQubitAPSGoodEventFrom_measurable
      protocol hTheta regularization start n
  · intro n
    by_cases hn : start ≤ n
    · exact (by
        simp only [oneQubitGuardedPolynomialConfidenceLevelFrom, hn, if_true]
        exact (oneQubitPolynomialConfidenceLevel_lt_one n).le)
    · simp [oneQubitGuardedPolynomialConfidenceLevelFrom, hn]
  · exact fun n => oneQubitAPSGoodEventFrom_confidence
      protocol hTheta regularization hRegularization start n
  · exact oneQubitGuardedPolynomialConfidenceLevelFrom_tsum_ne_top start
  · exact hConstant
  · intro n omega hgood
    by_cases hn : start ≤ n
    · apply hBound n hn omega
      simpa [oneQubitAPSGoodEventFrom, hn] using hgood
    · simpa [oneQubitAPSGoodEventFrom, hn] using hgood
  · exact oneQubitThreeQuarterExploration_controllerRate_tendsto_zero

theorem oneQubitBornRLSController_of_aps2011_eventualStart
    {Omega E : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    [NormedAddCommGroup E] {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 → ℝ} {axis : ℕ → Omega → Fin 3 → ℝ}
    {outcome : ℕ → Omega → QubitRLSOutcome}
    (protocol : BinaryQubitRLSReducedProbabilityPremises Omega mu theta axis outcome)
    (hTheta : blochNormSq theta ≤ 1) (regularization : ℝ)
    (hRegularization : 0 < regularization) (start : ℕ)
    (controller : ℕ → Omega → E) (truth : E)
    (hControllerMeasurable : ∀ n, AEStronglyMeasurable (controller n) mu)
    (constant : ℝ) (hConstant : 0 ≤ constant)
    (hBound : ∀ n, start ≤ n → ∀ omega ∈
      PopularRLSConditions.aps2011Theorem2GoodEvent
        (protocol.toSelfNormalizedMartingaleData hTheta) theta
        (oneQubitRLSObservation outcome) regularization 1
        (oneQubitPolynomialConfidenceLevel n),
      ‖controller n omega - truth‖ ≤
        constant * controllerRateScale oneQubitThreeQuarterExploration n) :
    AlmostSureControllerRate mu controller truth oneQubitThreeQuarterExploration ∧
      (∀ᵐ omega ∂mu, Filter.Tendsto (fun n => controller n omega)
        Filter.atTop (nhds truth)) ∧
      TendstoInMeasure mu (scaledControllerNormError controller truth)
        Filter.atTop (fun _ => 0) := by
  let primitives := oneQubitBornRLSControllerRatePrimitives_of_aps2011_eventualStart
    protocol hTheta regularization hRegularization start controller truth constant
      hConstant hBound
  exact ⟨primitives.almostSureRate, primitives.consistent_ae,
    primitives.nquarter_tendstoInMeasure
      oneQubitThreeQuarterExploration_terminal
      (fun n => scaledControllerNormError_aestronglyMeasurable
        controller truth n (hControllerMeasurable n))⟩

end QubitOracle.Paper
