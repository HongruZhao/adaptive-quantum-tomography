import QubitOracle.Paper.ControllerErrorMeasurable

namespace QubitOracle.Paper

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

/-- Confidence schedule with two harmless finite-prefix failures. This avoids
requiring the asymptotic `sqrt(log n / E_n)` bound at `n = 0,1`, where its
right-hand side is zero. -/
def oneQubitGuardedPolynomialConfidenceLevel (n : Nat) : Real :=
  if 2 <= n then oneQubitPolynomialConfidenceLevel n else 1

theorem oneQubitGuardedPolynomialConfidenceLevel_summable :
    Summable oneQubitGuardedPolynomialConfidenceLevel := by
  apply (summable_nat_add_iff 2).mp
  have htail : Summable (fun n : Nat =>
      oneQubitPolynomialConfidenceLevel (n + 2)) :=
    (summable_nat_add_iff 2).mpr
      oneQubitPolynomialConfidenceLevel_summable
  simpa [oneQubitGuardedPolynomialConfidenceLevel] using htail

theorem oneQubitGuardedPolynomialConfidenceLevel_tsum_ne_top :
    (∑' n, ENNReal.ofReal (oneQubitGuardedPolynomialConfidenceLevel n)) ≠
      (⊤ : ENNReal) :=
  oneQubitGuardedPolynomialConfidenceLevel_summable.tsum_ofReal_ne_top

/-- Finite-time-correct physical qubit RLS theorem. The deterministic
confidence-to-controller estimate is needed only from time two onward; the
first two bad events have finite total mass and do not affect Borel--Cantelli
or any asymptotic conclusion. -/
theorem oneQubitBornRLSController_of_aps2011_eventualBound
    {Omega : Type*} {E : Type*}
    [MeasurableSpace Omega] [StandardBorelSpace Omega]
    [NormedAddCommGroup E]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 -> Real}
    {axis : Nat -> Omega -> Fin 3 -> Real}
    {outcome : Nat -> Omega -> QubitRLSOutcome}
    (protocol : BinaryQubitRLSReducedProbabilityPremises
      Omega mu theta axis outcome)
    (hTheta : QubitOracle.blochNormSq theta <= 1)
    (regularization : Real) (hRegularization : 0 < regularization)
    (controller : Nat -> Omega -> E) (truth : E)
    (hControllerMeasurable : forall n,
      AEStronglyMeasurable (controller n) mu)
    (constant : Real) (hConstant : 0 <= constant)
    (hBound : forall n, 2 <= n -> forall omega,
      omega ∈ PopularRLSConditions.aps2011Theorem2GoodEvent
        (protocol.toSelfNormalizedMartingaleData hTheta) theta
        (oneQubitRLSObservation outcome) regularization 1
        (oneQubitPolynomialConfidenceLevel n) ->
      ‖controller n omega - truth‖ <=
        constant * controllerRateScale oneQubitThreeQuarterExploration n) :
    AlmostSureControllerRate mu controller truth oneQubitThreeQuarterExploration ∧
      (∀ᵐ omega ∂mu, Tendsto (fun n => controller n omega)
        atTop (nhds truth)) ∧
      TendstoInMeasure mu (scaledControllerNormError controller truth)
        atTop (fun _ => 0) := by
  let goodEvent : Nat -> Set Omega := fun n =>
    if 2 <= n then
      PopularRLSConditions.aps2011Theorem2GoodEvent
        (protocol.toSelfNormalizedMartingaleData hTheta) theta
        (oneQubitRLSObservation outcome) regularization 1
        (oneQubitPolynomialConfidenceLevel n)
    else (∅ : Set Omega)
  have hMeasurable : forall n, MeasurableSet (goodEvent n) := by
    intro n
    by_cases hn : 2 <= n
    · simp only [goodEvent, if_pos hn]
      exact protocol.measurableSet_apsGoodEvent hTheta regularization 1
        (oneQubitPolynomialConfidenceLevel n)
    · simp [goodEvent, hn]
  have hDeltaLeOne : forall n,
      oneQubitGuardedPolynomialConfidenceLevel n <= 1 := by
    intro n
    by_cases hn : 2 <= n
    · simp only [oneQubitGuardedPolynomialConfidenceLevel, if_pos hn]
      exact (oneQubitPolynomialConfidenceLevel_lt_one n).le
    · simp [oneQubitGuardedPolynomialConfidenceLevel, hn]
  have hConfidence : forall n,
      ENNReal.ofReal (1 - oneQubitGuardedPolynomialConfidenceLevel n) <=
        mu (goodEvent n) := by
    intro n
    by_cases hn : 2 <= n
    · simp only [oneQubitGuardedPolynomialConfidenceLevel, goodEvent, if_pos hn]
      exact
        PopularRLSConditions.abbasiYadkoriPalSzepesvari2011_theorem2_confidenceEllipsoid_external
          (protocol.toSelfNormalizedMartingaleData hTheta)
          (by norm_num) theta (oneQubitRLSObservation outcome)
          (protocol.linearObservation_ae hTheta)
          regularization hRegularization 1 (by norm_num)
          (oneQubitFiniteEuclideanNorm_le_one_of_physicalBloch theta hTheta)
          (oneQubitPolynomialConfidenceLevel n)
          (oneQubitPolynomialConfidenceLevel_positive n)
          (oneQubitPolynomialConfidenceLevel_lt_one n)
    · simp [oneQubitGuardedPolynomialConfidenceLevel, goodEvent, hn]
  have hGuardedBound : forall n omega, omega ∈ goodEvent n ->
      ‖controller n omega - truth‖ <=
        constant * controllerRateScale oneQubitThreeQuarterExploration n := by
    intro n omega hgood
    by_cases hn : 2 <= n
    · apply hBound n hn omega
      simpa [goodEvent, hn] using hgood
    · simp [goodEvent, hn] at hgood
  have hPrimitives : ControllerRatePrimitives mu controller truth
      oneQubitThreeQuarterExploration :=
    controllerRatePrimitives_of_confidenceEvents
      controller truth oneQubitThreeQuarterExploration goodEvent
      oneQubitGuardedPolynomialConfidenceLevel hMeasurable hDeltaLeOne
      hConfidence oneQubitGuardedPolynomialConfidenceLevel_tsum_ne_top
      constant hConstant hGuardedBound
      oneQubitThreeQuarterExploration_controllerRate_tendsto_zero
  exact Label.thm_SI_RLS mu controller truth oneQubitThreeQuarterExploration
    hPrimitives oneQubitThreeQuarterExploration_terminal
    (fun n => scaledControllerNormError_aestronglyMeasurable
      controller truth n (hControllerMeasurable n))

end

end QubitOracle.Paper
