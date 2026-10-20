import QubitOracle.Paper.OneQubitAPSExcitationOnly

namespace QubitOracle.Paper

open MeasureTheory Filter

noncomputable section

/-- Concrete schedule-level certificate: complete Pauli blocks are explicitly
embedded in the observed Gram matrix, with all other rounds collected in a
nonnegative quadratic-form remainder. -/
structure OneQubitPauliBlockGramCertificate
    {Omega : Type*}
    [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 -> Real}
    {axis : Nat -> Omega -> Fin 3 -> Real}
    {outcome : Nat -> Omega -> QubitRLSOutcome}
    (protocol : BinaryQubitRLSReducedProbabilityPremises
      Omega mu theta axis outcome)
    (hTheta : QubitOracle.blochNormSq theta <= 1) where
  blocks : Nat -> Nat
  remainder : Nat -> Omega -> Matrix (Fin 3) (Fin 3) Real
  gram_decomposition : forall n omega,
    PopularRLSConditions.aps2011Theorem2Gram
      (protocol.toSelfNormalizedMartingaleData hTheta) 1 n omega =
    pauliForcedExplorationGram (blocks n) + remainder n omega
  remainder_nonnegative : forall n omega x,
    0 <= oneQubitGramEnergy (remainder n omega) x
  block_lower : forall n, 2 <= n ->
    oneQubitThreeQuarterExploration n <= (blocks n : Real)

/-- A Pauli-block Gram decomposition implies the exact excitation certificate
consumed by the RLS theorem. -/
theorem OneQubitPauliBlockGramCertificate.toExcitationCertificate
    {Omega : Type*}
    [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 -> Real}
    {axis : Nat -> Omega -> Fin 3 -> Real}
    {outcome : Nat -> Omega -> QubitRLSOutcome}
    {protocol : BinaryQubitRLSReducedProbabilityPremises
      Omega mu theta axis outcome}
    {hTheta : QubitOracle.blochNormSq theta <= 1}
    (certificate : OneQubitPauliBlockGramCertificate protocol hTheta) :
    OneQubitAPSExcitationCertificate protocol hTheta := by
  constructor
  intro n hn omega
  constructor
  · unfold oneQubitThreeQuarterExploration
    exact Real.rpow_pos_of_pos (by positivity) _
  · intro x
    rw [certificate.gram_decomposition n omega]
    have hNorm : 0 <= QubitOracle.blochNormSq x := by
      unfold QubitOracle.blochNormSq
      positivity
    have hBlockScale :
        oneQubitThreeQuarterExploration n * QubitOracle.blochNormSq x <=
          (certificate.blocks n : Real) * QubitOracle.blochNormSq x :=
      mul_le_mul_of_nonneg_right (certificate.block_lower n hn) hNorm
    have hBlockIdentity :=
      oneQubitGramEnergy_pauliForcedExplorationGram (certificate.blocks n) x
    have hAdd :
        oneQubitGramEnergy (pauliForcedExplorationGram (certificate.blocks n)) x <=
          oneQubitGramEnergy
            (pauliForcedExplorationGram (certificate.blocks n) +
              certificate.remainder n omega) x := by
      unfold oneQubitGramEnergy QubitOracle.blochDot
      simp only [Matrix.add_mulVec, Pi.add_apply, mul_add,
        Finset.sum_add_distrib]
      have hRem := certificate.remainder_nonnegative n omega x
      unfold oneQubitGramEnergy QubitOracle.blochDot at hRem
      linarith
    exact hBlockScale.trans (hBlockIdentity.symm.le.trans hAdd)

/-- Complete controller conclusion from the explicit Pauli-block decomposition.
The only scientific axiom in the endpoint is APS 2011. -/
theorem OneQubitPauliBlockGramCertificate.controllerConvergence
    {Omega : Type*}
    [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 -> Real}
    {axis : Nat -> Omega -> Fin 3 -> Real}
    {outcome : Nat -> Omega -> QubitRLSOutcome}
    {protocol : BinaryQubitRLSReducedProbabilityPremises
      Omega mu theta axis outcome}
    {hTheta : QubitOracle.blochNormSq theta <= 1}
    (certificate : OneQubitPauliBlockGramCertificate protocol hTheta) :
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
  certificate.toExcitationCertificate.controllerConvergence

end

end QubitOracle.Paper
