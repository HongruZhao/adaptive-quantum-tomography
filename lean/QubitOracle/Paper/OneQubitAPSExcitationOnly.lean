import QubitOracle.Paper.OneQubitAPSRadiusBound

namespace QubitOracle.Paper

open MeasureTheory Filter

noncomputable section

/-- The sole remaining deterministic rate condition at lambda one: the actual
regularized Gram matrix dominates the planned n^(3/4) exploration scale. -/
structure OneQubitAPSExcitationCertificate
    {Omega : Type*}
    [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 -> Real}
    {axis : Nat -> Omega -> Fin 3 -> Real}
    {outcome : Nat -> Omega -> QubitRLSOutcome}
    (protocol : BinaryQubitRLSReducedProbabilityPremises
      Omega mu theta axis outcome)
    (hTheta : QubitOracle.blochNormSq theta <= 1) : Prop where
  excitation : forall n, 2 <= n -> forall omega,
    OneQubitPersistentExcitation
      (PopularRLSConditions.aps2011Theorem2Gram
        (protocol.toSelfNormalizedMartingaleData hTheta) 1 n omega)
      (oneQubitThreeQuarterExploration n)

/-- Physicality proves the radius field, so excitation alone constructs the
full deterministic RLS rate certificate with constant 12. -/
noncomputable def OneQubitAPSExcitationCertificate.toRateCertificate
    {Omega : Type*}
    [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 -> Real}
    {axis : Nat -> Omega -> Fin 3 -> Real}
    {outcome : Nat -> Omega -> QubitRLSOutcome}
    {protocol : BinaryQubitRLSReducedProbabilityPremises
      Omega mu theta axis outcome}
    {hTheta : QubitOracle.blochNormSq theta <= 1}
    (certificate : OneQubitAPSExcitationCertificate protocol hTheta) :
    OneQubitAPSRidgeRateCertificate protocol hTheta 1 where
  constant := 12
  constant_nonnegative := by norm_num
  excitation := certificate.excitation
  radiusSq := by
    intro n hn omega
    simpa only [show (12 : Real) ^ 2 = 144 by norm_num] using
      oneQubitAPSRadius_one_sq_le protocol hTheta n hn omega

/-- Complete non-LAN one-qubit ridge-controller conclusion at lambda one.
Its only external scientific theorem is APS 2011; locally, the only remaining
protocol-specific deterministic input is forced-exploration coercivity. -/
theorem OneQubitAPSExcitationCertificate.controllerConvergence
    {Omega : Type*}
    [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 -> Real}
    {axis : Nat -> Omega -> Fin 3 -> Real}
    {outcome : Nat -> Omega -> QubitRLSOutcome}
    {protocol : BinaryQubitRLSReducedProbabilityPremises
      Omega mu theta axis outcome}
    {hTheta : QubitOracle.blochNormSq theta <= 1}
    (certificate : OneQubitAPSExcitationCertificate protocol hTheta) :
    AlmostSureControllerRate mu
        (oneQubitAPSRidgeController protocol hTheta 1) theta
        oneQubitThreeQuarterExploration ∧
      (∀ᵐ omega ∂mu,
        Tendsto (fun n => oneQubitAPSRidgeController protocol hTheta 1 n omega)
          atTop (nhds theta)) ∧
      TendstoInMeasure mu
        (scaledControllerNormError
          (oneQubitAPSRidgeController protocol hTheta 1) theta)
        atTop (fun _ => 0) :=
  certificate.toRateCertificate.controllerConvergence (by norm_num)

end

end QubitOracle.Paper
