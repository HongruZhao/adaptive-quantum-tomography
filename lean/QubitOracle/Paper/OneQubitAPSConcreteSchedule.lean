import QubitOracle.Paper.OneQubitAPSToController

namespace QubitOracle.Paper

noncomputable section

open MeasureTheory

/--
The source-faithful Abbasi--Yadkori--Pal--Szepesvari confidence theorem,
specialized to the paper's concrete one-qubit choices
`delta_n = 1 / (n + 2)^2` and `E_n = n^(3/4)`.

All confidence-level and exploration-rate obligations are discharged locally.
The remaining arguments are precisely the protocol-specific martingale,
measurability, parameter-bound, and controller-error obligations.
-/
def controllerRatePrimitives_of_aps2011_threeQuarterPolynomialSchedule
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
        constant * controllerRateScale oneQubitThreeQuarterExploration n) :
    ControllerRatePrimitives mu controller truth oneQubitThreeQuarterExploration :=
  controllerRatePrimitives_of_aps2011_theorem2
    data hR thetaStar observation hLinearObservation
    regularization hRegularization parameterRadius hParameterRadius hParameterBound
    controller truth
    oneQubitThreeQuarterExploration oneQubitPolynomialConfidenceLevel
    oneQubitPolynomialConfidenceLevel_positive
    oneQubitPolynomialConfidenceLevel_lt_one
    hGoodMeasurable
    oneQubitPolynomialConfidenceLevel_tsum_ne_top
    constant hConstant hBound
    oneQubitThreeQuarterExploration_controllerRate_tendsto_zero

end

end QubitOracle.Paper
