import QubitOracle.Paper.OneQubitAPSEventualStartController
import QubitOracle.Paper.OneQubitAPSConcreteEstimator
import QubitOracle.Paper.OneQubitAPSRidgeRateCertificate
import QubitOracle.Paper.OneQubitAPSRadiusBound
import QubitOracle.Paper.OneQubitPauliBlockGramCertificate

namespace QubitOracle.Paper

open MeasureTheory

theorem oneQubitAPSRidgeController_of_aps2011_eventualStartEuclideanBound
    {Omega : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 → ℝ} {axis : ℕ → Omega → Fin 3 → ℝ}
    {outcome : ℕ → Omega → QubitRLSOutcome}
    (protocol : BinaryQubitRLSReducedProbabilityPremises Omega mu theta axis outcome)
    (hTheta : blochNormSq theta ≤ 1) (regularization : ℝ)
    (hRegularization : 0 < regularization) (start : ℕ)
    (constant : ℝ) (hConstant : 0 ≤ constant)
    (hEuclideanBound : ∀ n, start ≤ n → ∀ omega ∈
      PopularRLSConditions.aps2011Theorem2GoodEvent
        (protocol.toSelfNormalizedMartingaleData hTheta) theta
        (oneQubitRLSObservation outcome) regularization 1
        (oneQubitPolynomialConfidenceLevel n),
      PopularRLSConditions.finiteEuclideanNorm
        (oneQubitRLSError
          (oneQubitAPSRidgeController protocol hTheta regularization n omega) theta) ≤
        constant * controllerRateScale oneQubitThreeQuarterExploration n) :
    AlmostSureControllerRate mu
        (oneQubitAPSRidgeController protocol hTheta regularization) theta
        oneQubitThreeQuarterExploration ∧
      (∀ᵐ omega ∂mu, Filter.Tendsto
        (fun n => oneQubitAPSRidgeController protocol hTheta regularization n omega)
        Filter.atTop (nhds theta)) ∧
      TendstoInMeasure mu
        (scaledControllerNormError
          (oneQubitAPSRidgeController protocol hTheta regularization) theta)
        Filter.atTop (fun _ => 0) := by
  apply oneQubitBornRLSController_of_aps2011_eventualStart
    protocol hTheta regularization hRegularization start
      (oneQubitAPSRidgeController protocol hTheta regularization) theta
      (fun n => oneQubitAPSRidgeController_aestronglyMeasurable
        protocol hTheta regularization n) constant hConstant
  intro n hn omega hgood
  change ‖oneQubitRLSError
    (oneQubitAPSRidgeController protocol hTheta regularization n omega) theta‖ ≤ _
  exact (piNorm_le_finiteEuclideanNorm_three _).trans
    (hEuclideanBound n hn omega hgood)

/-- An APS ridge-rate certificate whose deterministic bounds begin after `start`. -/
structure OneQubitAPSEventualRidgeRateCertificate
    {Omega : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 → ℝ} {axis : ℕ → Omega → Fin 3 → ℝ}
    {outcome : ℕ → Omega → QubitRLSOutcome}
    (protocol : BinaryQubitRLSReducedProbabilityPremises Omega mu theta axis outcome)
    (hTheta : blochNormSq theta ≤ 1) (regularization : ℝ) (start : ℕ) where
  start_ge_two : 2 ≤ start
  constant : ℝ
  constant_nonnegative : 0 ≤ constant
  excitation : ∀ n, start ≤ n → ∀ omega,
    OneQubitPersistentExcitation
      (PopularRLSConditions.aps2011Theorem2Gram
        (protocol.toSelfNormalizedMartingaleData hTheta) regularization n omega)
      (oneQubitThreeQuarterExploration n)
  radiusSq : ∀ n, start ≤ n → ∀ omega,
    PopularRLSConditions.aps2011Theorem2Radius
        (protocol.toSelfNormalizedMartingaleData hTheta) regularization 1
        (oneQubitPolynomialConfidenceLevel n) n omega ^ 2 ≤
      constant ^ 2 * Real.log n

theorem OneQubitAPSEventualRidgeRateCertificate.controllerConvergence
    {Omega : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 → ℝ} {axis : ℕ → Omega → Fin 3 → ℝ}
    {outcome : ℕ → Omega → QubitRLSOutcome}
    {protocol : BinaryQubitRLSReducedProbabilityPremises Omega mu theta axis outcome}
    {hTheta : blochNormSq theta ≤ 1} {regularization : ℝ} {start : ℕ}
    (certificate : OneQubitAPSEventualRidgeRateCertificate
      protocol hTheta regularization start)
    (hRegularization : 0 < regularization) :
    AlmostSureControllerRate mu
        (oneQubitAPSRidgeController protocol hTheta regularization) theta
        oneQubitThreeQuarterExploration ∧
      (∀ᵐ omega ∂mu, Filter.Tendsto
        (fun n => oneQubitAPSRidgeController protocol hTheta regularization n omega)
        Filter.atTop (nhds theta)) ∧
      TendstoInMeasure mu
        (scaledControllerNormError
          (oneQubitAPSRidgeController protocol hTheta regularization) theta)
        Filter.atTop (fun _ => 0) := by
  apply oneQubitAPSRidgeController_of_aps2011_eventualStartEuclideanBound
    protocol hTheta regularization hRegularization start
      certificate.constant certificate.constant_nonnegative
  intro n hn omega hgood
  exact oneQubitAPSRidge_euclideanBound_of_excitation_radius
    protocol hTheta regularization n (certificate.start_ge_two.trans hn) omega hgood
      (certificate.excitation n hn omega) certificate.constant
      certificate.constant_nonnegative (certificate.radiusSq n hn omega)

/-- At ridge parameter one, the radius estimate is automatic; only eventual excitation remains. -/
structure OneQubitAPSEventualExcitationCertificate
    {Omega : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 → ℝ} {axis : ℕ → Omega → Fin 3 → ℝ}
    {outcome : ℕ → Omega → QubitRLSOutcome}
    (protocol : BinaryQubitRLSReducedProbabilityPremises Omega mu theta axis outcome)
    (hTheta : blochNormSq theta ≤ 1) (start : ℕ) : Prop where
  start_ge_two : 2 ≤ start
  excitation : ∀ n, start ≤ n → ∀ omega,
    OneQubitPersistentExcitation
      (PopularRLSConditions.aps2011Theorem2Gram
        (protocol.toSelfNormalizedMartingaleData hTheta) 1 n omega)
      (oneQubitThreeQuarterExploration n)

noncomputable def OneQubitAPSEventualExcitationCertificate.toRateCertificate
    {Omega : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 → ℝ} {axis : ℕ → Omega → Fin 3 → ℝ}
    {outcome : ℕ → Omega → QubitRLSOutcome}
    {protocol : BinaryQubitRLSReducedProbabilityPremises Omega mu theta axis outcome}
    {hTheta : blochNormSq theta ≤ 1} {start : ℕ}
    (certificate : OneQubitAPSEventualExcitationCertificate protocol hTheta start) :
    OneQubitAPSEventualRidgeRateCertificate protocol hTheta 1 start where
  start_ge_two := certificate.start_ge_two
  constant := 12
  constant_nonnegative := by norm_num
  excitation := certificate.excitation
  radiusSq := by
    intro n hn omega
    have h := oneQubitAPSRadius_one_sq_le protocol hTheta n
      (certificate.start_ge_two.trans hn) omega
    norm_num at h ⊢
    exact h

theorem OneQubitAPSEventualExcitationCertificate.controllerConvergence
    {Omega : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 → ℝ} {axis : ℕ → Omega → Fin 3 → ℝ}
    {outcome : ℕ → Omega → QubitRLSOutcome}
    {protocol : BinaryQubitRLSReducedProbabilityPremises Omega mu theta axis outcome}
    {hTheta : blochNormSq theta ≤ 1} {start : ℕ}
    (certificate : OneQubitAPSEventualExcitationCertificate protocol hTheta start) :
    AlmostSureControllerRate mu
        (oneQubitAPSRidgeController protocol hTheta 1) theta
        oneQubitThreeQuarterExploration ∧
      (∀ᵐ omega ∂mu, Filter.Tendsto
        (fun n => oneQubitAPSRidgeController protocol hTheta 1 n omega)
        Filter.atTop (nhds theta)) ∧
      TendstoInMeasure mu
        (scaledControllerNormError
          (oneQubitAPSRidgeController protocol hTheta 1) theta)
        Filter.atTop (fun _ => 0) :=
  certificate.toRateCertificate.controllerConvergence (by norm_num)

/-- A physically meaningful Pauli-block certificate: block domination is only eventual. -/
structure OneQubitEventualPauliBlockGramCertificate
    {Omega : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 → ℝ} {axis : ℕ → Omega → Fin 3 → ℝ}
    {outcome : ℕ → Omega → QubitRLSOutcome}
    (protocol : BinaryQubitRLSReducedProbabilityPremises Omega mu theta axis outcome)
    (hTheta : blochNormSq theta ≤ 1) (start : ℕ) where
  start_ge_two : 2 ≤ start
  blocks : ℕ → ℕ
  remainder : ℕ → Omega → Matrix (Fin 3) (Fin 3) ℝ
  gram_decomposition : ∀ n omega,
    PopularRLSConditions.aps2011Theorem2Gram
        (protocol.toSelfNormalizedMartingaleData hTheta) 1 n omega =
      pauliForcedExplorationGram (blocks n) + remainder n omega
  remainder_nonnegative : ∀ n omega x,
    0 ≤ oneQubitGramEnergy (remainder n omega) x
  block_lower : ∀ n, start ≤ n →
    oneQubitThreeQuarterExploration n ≤ (blocks n : ℝ)

theorem OneQubitEventualPauliBlockGramCertificate.toExcitationCertificate
    {Omega : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 → ℝ} {axis : ℕ → Omega → Fin 3 → ℝ}
    {outcome : ℕ → Omega → QubitRLSOutcome}
    {protocol : BinaryQubitRLSReducedProbabilityPremises Omega mu theta axis outcome}
    {hTheta : blochNormSq theta ≤ 1} {start : ℕ}
    (certificate : OneQubitEventualPauliBlockGramCertificate
      protocol hTheta start) :
    OneQubitAPSEventualExcitationCertificate protocol hTheta start where
  start_ge_two := certificate.start_ge_two
  excitation := by
    intro n hn omega
    refine ⟨?_, ?_⟩
    · exact Real.rpow_pos_of_pos
        (Nat.cast_pos.mpr (lt_of_lt_of_le (by norm_num) (certificate.start_ge_two.trans hn)))
        (3 / 4)
    · intro x
      rw [certificate.gram_decomposition n omega]
      have hNorm : 0 ≤ blochNormSq x := by
        exact Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
      have hBlockScale := mul_le_mul_of_nonneg_right
        (certificate.block_lower n hn) hNorm
      have hBlockIdentity := oneQubitGramEnergy_pauliForcedExplorationGram
        (certificate.blocks n) x
      have hAdd :
          oneQubitGramEnergy (pauliForcedExplorationGram (certificate.blocks n)) x ≤
            oneQubitGramEnergy
              (pauliForcedExplorationGram (certificate.blocks n) +
                certificate.remainder n omega) x := by
        have hRem := certificate.remainder_nonnegative n omega x
        simp only [oneQubitGramEnergy, blochDot] at hRem
        simp only [oneQubitGramEnergy, blochDot, Matrix.add_mulVec, Pi.add_apply,
          mul_add, Finset.sum_add_distrib]
        linarith
      exact hBlockScale.trans (hBlockIdentity.ge.trans hAdd)

theorem OneQubitEventualPauliBlockGramCertificate.controllerConvergence
    {Omega : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 → ℝ} {axis : ℕ → Omega → Fin 3 → ℝ}
    {outcome : ℕ → Omega → QubitRLSOutcome}
    {protocol : BinaryQubitRLSReducedProbabilityPremises Omega mu theta axis outcome}
    {hTheta : blochNormSq theta ≤ 1} {start : ℕ}
    (certificate : OneQubitEventualPauliBlockGramCertificate
      protocol hTheta start) :
    AlmostSureControllerRate mu
        (oneQubitAPSRidgeController protocol hTheta 1) theta
        oneQubitThreeQuarterExploration ∧
      (∀ᵐ omega ∂mu, Filter.Tendsto
        (fun n => oneQubitAPSRidgeController protocol hTheta 1 n omega)
        Filter.atTop (nhds theta)) ∧
      TendstoInMeasure mu
        (scaledControllerNormError
          (oneQubitAPSRidgeController protocol hTheta 1) theta)
        Filter.atTop (fun _ => 0) :=
  certificate.toExcitationCertificate.controllerConvergence

end QubitOracle.Paper
