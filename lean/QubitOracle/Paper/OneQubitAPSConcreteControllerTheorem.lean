import QubitOracle.Paper.OneQubitAPSConcreteSchedule

namespace QubitOracle.Paper

noncomputable section

open Filter MeasureTheory

/--
Concrete one-qubit RLS controller theorem with
`delta_n = 1 / (n + 2)^2` and `E_n = n^(3/4)`.

The probability and rate conclusions are the conclusions of the manuscript's
supplementary RLS label.  The only external scientific theorem used is the
source-faithful Abbasi--Yadkori--Pal--Szepesvari (2011), Theorem 2 interface.
All remaining hypotheses are explicit quantum-protocol verification duties.
-/
theorem oneQubitRLSController_of_aps2011_threeQuarterPolynomialSchedule
    {Omega E : Type*}
    [MeasurableSpace Omega]
    [NormedAddCommGroup E]
    {mu : Measure Omega}
    [IsProbabilityMeasure mu]
    {R : ℝ}
    (data : SourceFaithfulSelfNormalized.SelfNormalizedMartingaleData Omega 3 mu R)
    (hR : 0 ≤ R)
    (thetaStar : Fin 3 → ℝ)
    (observation : ℕ → Omega → ℝ)
    (hLinearObservation : ∀ k,
      observation (k + 1) =ᵐ[mu]
        fun omega => data.regressor k omega ⬝ᵥ thetaStar + data.noise (k + 1) omega)
    (regularization : ℝ)
    (hRegularization : 0 < regularization)
    (parameterRadius : ℝ)
    (hParameterRadius : 0 ≤ parameterRadius)
    (hParameterBound :
      PopularRLSConditions.finiteEuclideanNorm thetaStar ≤ parameterRadius)
    (controller : ℕ → Omega → E)
    (truth : E)
    (hGoodMeasurable : ∀ n,
      MeasurableSet
        (PopularRLSConditions.aps2011Theorem2GoodEvent
          data thetaStar observation regularization parameterRadius
          (oneQubitPolynomialConfidenceLevel n)))
    (constant : ℝ)
    (hConstant : 0 ≤ constant)
    (hBound : ∀ n omega,
      omega ∈ PopularRLSConditions.aps2011Theorem2GoodEvent
        data thetaStar observation regularization parameterRadius
        (oneQubitPolynomialConfidenceLevel n) →
      ‖controller n omega - truth‖ ≤
        constant * controllerRateScale oneQubitThreeQuarterExploration n)
    (hScaledMeasurable : ∀ n,
      AEStronglyMeasurable (scaledControllerNormError controller truth n) mu) :
    AlmostSureControllerRate mu controller truth oneQubitThreeQuarterExploration ∧
      (∀ᵐ omega ∂mu, Tendsto (fun n => controller n omega) atTop (nhds truth)) ∧
      TendstoInMeasure mu (scaledControllerNormError controller truth) atTop
        (fun _ => 0) := by
  apply Label.thm_SI_RLS
  · exact controllerRatePrimitives_of_aps2011_threeQuarterPolynomialSchedule
      data hR thetaStar observation hLinearObservation
      regularization hRegularization parameterRadius hParameterRadius hParameterBound
      controller truth hGoodMeasurable constant hConstant hBound
  · exact oneQubitThreeQuarterExploration_terminal
  · exact hScaledMeasurable

end

end QubitOracle.Paper
