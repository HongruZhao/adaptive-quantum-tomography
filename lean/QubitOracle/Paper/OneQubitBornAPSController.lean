import QubitOracle.Paper.OneQubitBornRLSMartingaleData
import QubitOracle.Paper.OneQubitAPSConcreteControllerTheorem

namespace QubitOracle.Paper

open Filter MeasureTheory ProbabilityTheory

noncomputable section

/-- A physical Bloch vector satisfies the APS parameter-radius-one condition. -/
theorem oneQubitFiniteEuclideanNorm_le_one_of_physicalBloch
    (theta : Fin 3 → ℝ)
    (hTheta : QubitOracle.blochNormSq theta ≤ 1) :
    PopularRLSConditions.finiteEuclideanNorm theta ≤ 1 := by
  change Real.sqrt (QubitOracle.blochNormSq theta) ≤ 1
  calc
    Real.sqrt (QubitOracle.blochNormSq theta) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hTheta
    _ = 1 := Real.sqrt_one

/--
The manuscript's all-time one-qubit RLS conclusion, specialized to a physical
binary Born trajectory and the concrete polynomial confidence/exploration
schedules.  The only scientific axiom is APS (2011), Theorem 2.
-/
theorem oneQubitBornRLSController_of_aps2011_threeQuarterPolynomialSchedule
    {Omega E : Type*}
    [mOmega : MeasurableSpace Omega]
    [StandardBorelSpace Omega]
    [NormedAddCommGroup E]
    {mu : Measure Omega}
    [IsProbabilityMeasure mu]
    {theta : Fin 3 → ℝ}
    {axis : ℕ → Omega → Fin 3 → ℝ}
    {outcome : ℕ → Omega → QubitRLSOutcome}
    (protocol : BinaryQubitRLSReducedProbabilityPremises Omega mu theta axis outcome)
    (hTheta : QubitOracle.blochNormSq theta ≤ 1)
    (regularization : ℝ)
    (hRegularization : 0 < regularization)
    (controller : ℕ → Omega → E)
    (truth : E)
    (hGoodMeasurable : ∀ n,
      MeasurableSet
        (PopularRLSConditions.aps2011Theorem2GoodEvent
          (protocol.toSelfNormalizedMartingaleData hTheta)
          theta (oneQubitRLSObservation outcome) regularization 1
          (oneQubitPolynomialConfidenceLevel n)))
    (constant : ℝ)
    (hConstant : 0 ≤ constant)
    (hBound : ∀ n omega,
      omega ∈ PopularRLSConditions.aps2011Theorem2GoodEvent
        (protocol.toSelfNormalizedMartingaleData hTheta)
        theta (oneQubitRLSObservation outcome) regularization 1
        (oneQubitPolynomialConfidenceLevel n) →
      ‖controller n omega - truth‖ ≤
        constant * controllerRateScale oneQubitThreeQuarterExploration n)
    (hScaledMeasurable : ∀ n,
      AEStronglyMeasurable (scaledControllerNormError controller truth n) mu) :
    AlmostSureControllerRate mu controller truth oneQubitThreeQuarterExploration ∧
      (∀ᵐ omega ∂mu, Tendsto (fun n => controller n omega) atTop (nhds truth)) ∧
      TendstoInMeasure mu (scaledControllerNormError controller truth) atTop
        (fun _ => 0) := by
  apply oneQubitRLSController_of_aps2011_threeQuarterPolynomialSchedule
    (protocol.toSelfNormalizedMartingaleData hTheta) (by norm_num)
    theta (oneQubitRLSObservation outcome)
    (protocol.linearObservation_ae hTheta)
    regularization hRegularization 1 (by norm_num)
    (oneQubitFiniteEuclideanNorm_le_one_of_physicalBloch theta hTheta)
    controller truth hGoodMeasurable constant hConstant hBound hScaledMeasurable

end

end QubitOracle.Paper
