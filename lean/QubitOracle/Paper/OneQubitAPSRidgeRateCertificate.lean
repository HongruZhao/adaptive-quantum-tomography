import QubitOracle.Paper.OneQubitAPSConcreteEstimator

namespace QubitOracle.Paper

open MeasureTheory Filter

noncomputable section

/-- Deterministic ellipsoid-to-rate conversion for the actual qubit ridge
estimator. -/
theorem oneQubitAPSRidge_euclideanBound_of_excitation_radius
    {Omega : Type*}
    [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 -> Real}
    {axis : Nat -> Omega -> Fin 3 -> Real}
    {outcome : Nat -> Omega -> QubitRLSOutcome}
    (protocol : BinaryQubitRLSReducedProbabilityPremises
      Omega mu theta axis outcome)
    (hTheta : QubitOracle.blochNormSq theta <= 1)
    (regularization : Real)
    (n : Nat) (hn : 2 <= n) (omega : Omega)
    (hgood : omega ∈ PopularRLSConditions.aps2011Theorem2GoodEvent
      (protocol.toSelfNormalizedMartingaleData hTheta) theta
      (oneQubitRLSObservation outcome) regularization 1
      (oneQubitPolynomialConfidenceLevel n))
    (hExcitation : OneQubitPersistentExcitation
      (PopularRLSConditions.aps2011Theorem2Gram
        (protocol.toSelfNormalizedMartingaleData hTheta)
        regularization n omega)
      (oneQubitThreeQuarterExploration n))
    (C : Real) (hC : 0 <= C)
    (hRadiusSq :
      (PopularRLSConditions.aps2011Theorem2Radius
        (protocol.toSelfNormalizedMartingaleData hTheta)
        regularization 1 (oneQubitPolynomialConfidenceLevel n) n omega) ^ 2 <=
      C ^ 2 * Real.log (n : Real)) :
    PopularRLSConditions.finiteEuclideanNorm
      (oneQubitRLSError
        (oneQubitAPSRidgeController protocol hTheta regularization n omega)
        theta) <=
      C * controllerRateScale oneQubitThreeQuarterExploration n := by
  have hConfidence : OneQubitSelfNormalizedConfidence
      (PopularRLSConditions.aps2011Theorem2Gram
        (protocol.toSelfNormalizedMartingaleData hTheta)
        regularization n omega)
      (oneQubitAPSRidgeController protocol hTheta regularization n omega)
      theta
      (PopularRLSConditions.aps2011Theorem2Radius
        (protocol.toSelfNormalizedMartingaleData hTheta)
        regularization 1 (oneQubitPolynomialConfidenceLevel n) n omega) := by
    exact aps2011GoodEvent_oneQubitSelfNormalizedConfidence
      (protocol.toSelfNormalizedMartingaleData hTheta) theta
      (oneQubitRLSObservation outcome) regularization 1
      (oneQubitPolynomialConfidenceLevel n) omega hgood n
  have hBase := oneQubitRLSEuclideanError_le
    (PopularRLSConditions.aps2011Theorem2Gram
      (protocol.toSelfNormalizedMartingaleData hTheta)
      regularization n omega)
    (oneQubitAPSRidgeController protocol hTheta regularization n omega)
    theta
    (PopularRLSConditions.aps2011Theorem2Radius
      (protocol.toSelfNormalizedMartingaleData hTheta)
      regularization 1 (oneQubitPolynomialConfidenceLevel n) n omega)
    (oneQubitThreeQuarterExploration n) hConfidence hExcitation
  have hDiv :
      (PopularRLSConditions.aps2011Theorem2Radius
        (protocol.toSelfNormalizedMartingaleData hTheta)
        regularization 1 (oneQubitPolynomialConfidenceLevel n) n omega) ^ 2 /
          oneQubitThreeQuarterExploration n <=
        (C ^ 2 * Real.log (n : Real)) /
          oneQubitThreeQuarterExploration n :=
    (div_le_div_iff_of_pos_right hExcitation.excitation_positive).2 hRadiusSq
  calc
    PopularRLSConditions.finiteEuclideanNorm
        (oneQubitRLSError
          (oneQubitAPSRidgeController protocol hTheta regularization n omega)
          theta) <=
      Real.sqrt
        ((PopularRLSConditions.aps2011Theorem2Radius
          (protocol.toSelfNormalizedMartingaleData hTheta)
          regularization 1 (oneQubitPolynomialConfidenceLevel n) n omega) ^ 2 /
            oneQubitThreeQuarterExploration n) := hBase
    _ <= Real.sqrt
        ((C ^ 2 * Real.log (n : Real)) /
          oneQubitThreeQuarterExploration n) := Real.sqrt_le_sqrt hDiv
    _ = C * controllerRateScale oneQubitThreeQuarterExploration n := by
      unfold controllerRateScale
      rw [show (C ^ 2 * Real.log (n : Real)) /
          oneQubitThreeQuarterExploration n =
          C ^ 2 * (Real.log (n : Real) /
            oneQubitThreeQuarterExploration n) by ring]
      rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hC]

/-- Exactly the deterministic, protocol-specific facts still needed after the
APS source theorem: pathwise Gram coercivity and logarithmic radius growth. -/
structure OneQubitAPSRidgeRateCertificate
    {Omega : Type*}
    [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 -> Real}
    {axis : Nat -> Omega -> Fin 3 -> Real}
    {outcome : Nat -> Omega -> QubitRLSOutcome}
    (protocol : BinaryQubitRLSReducedProbabilityPremises
      Omega mu theta axis outcome)
    (hTheta : QubitOracle.blochNormSq theta <= 1)
    (regularization : Real) where
  constant : Real
  constant_nonnegative : 0 <= constant
  excitation : forall n, 2 <= n -> forall omega,
    OneQubitPersistentExcitation
      (PopularRLSConditions.aps2011Theorem2Gram
        (protocol.toSelfNormalizedMartingaleData hTheta)
        regularization n omega)
      (oneQubitThreeQuarterExploration n)
  radiusSq : forall n, 2 <= n -> forall omega,
    (PopularRLSConditions.aps2011Theorem2Radius
      (protocol.toSelfNormalizedMartingaleData hTheta)
      regularization 1 (oneQubitPolynomialConfidenceLevel n) n omega) ^ 2 <=
    constant ^ 2 * Real.log (n : Real)

/-- The rate certificate closes the concrete ridge-controller theorem. -/
theorem OneQubitAPSRidgeRateCertificate.controllerConvergence
    {Omega : Type*}
    [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 -> Real}
    {axis : Nat -> Omega -> Fin 3 -> Real}
    {outcome : Nat -> Omega -> QubitRLSOutcome}
    {protocol : BinaryQubitRLSReducedProbabilityPremises
      Omega mu theta axis outcome}
    {hTheta : QubitOracle.blochNormSq theta <= 1}
    {regularization : Real}
    (certificate : OneQubitAPSRidgeRateCertificate
      protocol hTheta regularization)
    (hRegularization : 0 < regularization) :
    AlmostSureControllerRate mu
        (oneQubitAPSRidgeController protocol hTheta regularization) theta
        oneQubitThreeQuarterExploration ∧
      (∀ᵐ omega ∂mu,
        Tendsto
          (fun n => oneQubitAPSRidgeController protocol hTheta regularization n omega)
          atTop (nhds theta)) ∧
      TendstoInMeasure mu
        (scaledControllerNormError
          (oneQubitAPSRidgeController protocol hTheta regularization) theta)
        atTop (fun _ => 0) := by
  apply oneQubitAPSRidgeController_of_aps2011_eventualEuclideanBound
    protocol hTheta regularization hRegularization
    certificate.constant certificate.constant_nonnegative
  intro n hn omega hgood
  exact oneQubitAPSRidge_euclideanBound_of_excitation_radius
    protocol hTheta regularization n hn omega hgood
    (certificate.excitation n hn omega)
    certificate.constant certificate.constant_nonnegative
    (certificate.radiusSq n hn omega)

end

end QubitOracle.Paper
