import QubitOracle.Paper.APSGoodEventMeasurable

namespace QubitOracle.Paper

open MeasureTheory

noncomputable section

/-- Measurability of a controller estimate automatically gives measurability
of its scaled norm error. -/
theorem scaledControllerNormError_aestronglyMeasurable
    {Omega E : Type*} [MeasurableSpace Omega] [NormedAddCommGroup E]
    {mu : Measure Omega} (controller : Nat -> Omega -> E) (truth : E)
    (n : Nat) (hController : AEStronglyMeasurable (controller n) mu) :
    AEStronglyMeasurable (scaledControllerNormError controller truth n) mu := by
  unfold scaledControllerNormError
  exact (hController.sub aestronglyMeasurable_const).norm.const_mul
    (natQuarterPower n)

/-- Physical one-qubit controller convergence with both APS-event and scaled
error measurability discharged internally. -/
theorem oneQubitBornRLSController_of_aps2011_autoMeasurable
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
    (hBound : forall n omega,
      omega ∈ PopularRLSConditions.aps2011Theorem2GoodEvent
        (protocol.toSelfNormalizedMartingaleData hTheta) theta
        (oneQubitRLSObservation outcome) regularization 1
        (oneQubitPolynomialConfidenceLevel n) ->
      ‖controller n omega - truth‖ <=
        constant * controllerRateScale oneQubitThreeQuarterExploration n) :
    AlmostSureControllerRate mu controller truth oneQubitThreeQuarterExploration ∧
      (∀ᵐ omega ∂mu, Filter.Tendsto (fun n => controller n omega)
        Filter.atTop (nhds truth)) ∧
      TendstoInMeasure mu (scaledControllerNormError controller truth)
        Filter.atTop (fun _ => 0) := by
  exact oneQubitBornRLSController_of_aps2011_autoGoodEventMeasurable
    protocol hTheta regularization hRegularization controller truth
    constant hConstant hBound
    (fun n => scaledControllerNormError_aestronglyMeasurable
      controller truth n (hControllerMeasurable n))

end

end QubitOracle.Paper
