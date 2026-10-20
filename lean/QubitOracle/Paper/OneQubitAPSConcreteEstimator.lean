import QubitOracle.Paper.OneQubitAPSEventualController

namespace QubitOracle.Paper

open MeasureTheory Filter
open scoped BigOperators

noncomputable section

/-- The actual ridge least-squares estimate used as the one-qubit controller. -/
def oneQubitAPSRidgeController
    {Omega : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 -> Real}
    {axis : Nat -> Omega -> Fin 3 -> Real}
    {outcome : Nat -> Omega -> QubitRLSOutcome}
    (protocol : BinaryQubitRLSReducedProbabilityPremises
      Omega mu theta axis outcome)
    (hTheta : QubitOracle.blochNormSq theta <= 1)
    (regularization : Real) : Nat -> Omega -> Fin 3 -> Real :=
  fun n omega =>
    PopularRLSConditions.aps2011Theorem2Estimator
      (protocol.toSelfNormalizedMartingaleData hTheta)
      (oneQubitRLSObservation outcome) regularization n omega

/-- The sup norm on a finite Bloch vector is bounded by its explicit Euclidean
norm. -/
theorem piNorm_le_finiteEuclideanNorm_three (x : Fin 3 -> Real) :
    ‖x‖ <= PopularRLSConditions.finiteEuclideanNorm x := by
  apply (pi_norm_le_iff_of_nonempty x).2
  intro i
  rw [Real.norm_eq_abs]
  unfold PopularRLSConditions.finiteEuclideanNorm
  apply (Real.le_sqrt (abs_nonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg (x j))).2
  rw [sq_abs]
  exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)

/-- Every finite-time ridge estimate is strongly measurable. -/
theorem oneQubitAPSRidgeController_aestronglyMeasurable
    {Omega : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 -> Real}
    {axis : Nat -> Omega -> Fin 3 -> Real}
    {outcome : Nat -> Omega -> QubitRLSOutcome}
    (protocol : BinaryQubitRLSReducedProbabilityPremises
      Omega mu theta axis outcome)
    (hTheta : QubitOracle.blochNormSq theta <= 1)
    (regularization : Real) (n : Nat) :
    AEStronglyMeasurable
      (oneQubitAPSRidgeController protocol hTheta regularization n) mu := by
  have hMeasurable : Measurable
      (oneQubitAPSRidgeController protocol hTheta regularization n) := by
    rw [measurable_pi_iff]
    intro i
    exact PopularRLSConditions.measurable_aps2011Theorem2Estimator_coordinate
      (protocol.toSelfNormalizedMartingaleData hTheta)
      (oneQubitRLSObservation outcome) protocol.observationMeasurable_succ
      regularization n i
  exact hMeasurable.aestronglyMeasurable

/-- Concrete-estimator controller theorem. The only remaining deterministic
protocol obligation is the Euclidean confidence-to-rate estimate on APS good
events from time two onward. -/
theorem oneQubitAPSRidgeController_of_aps2011_eventualEuclideanBound
    {Omega : Type*}
    [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 -> Real}
    {axis : Nat -> Omega -> Fin 3 -> Real}
    {outcome : Nat -> Omega -> QubitRLSOutcome}
    (protocol : BinaryQubitRLSReducedProbabilityPremises
      Omega mu theta axis outcome)
    (hTheta : QubitOracle.blochNormSq theta <= 1)
    (regularization : Real) (hRegularization : 0 < regularization)
    (constant : Real) (hConstant : 0 <= constant)
    (hEuclideanBound : forall n, 2 <= n -> forall omega,
      omega ∈ PopularRLSConditions.aps2011Theorem2GoodEvent
        (protocol.toSelfNormalizedMartingaleData hTheta) theta
        (oneQubitRLSObservation outcome) regularization 1
        (oneQubitPolynomialConfidenceLevel n) ->
      PopularRLSConditions.finiteEuclideanNorm
        (oneQubitRLSError
          (oneQubitAPSRidgeController protocol hTheta regularization n omega)
          theta) <=
        constant * controllerRateScale oneQubitThreeQuarterExploration n) :
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
  apply oneQubitBornRLSController_of_aps2011_eventualBound
    protocol hTheta regularization hRegularization
    (oneQubitAPSRidgeController protocol hTheta regularization) theta
    (fun n => oneQubitAPSRidgeController_aestronglyMeasurable
      protocol hTheta regularization n)
    constant hConstant
  intro n hn omega hgood
  calc
    ‖oneQubitAPSRidgeController protocol hTheta regularization n omega - theta‖ <=
        PopularRLSConditions.finiteEuclideanNorm
          (oneQubitAPSRidgeController protocol hTheta regularization n omega - theta) :=
      piNorm_le_finiteEuclideanNorm_three _
    _ = PopularRLSConditions.finiteEuclideanNorm
          (oneQubitRLSError
            (oneQubitAPSRidgeController protocol hTheta regularization n omega)
            theta) := by rfl
    _ <= constant * controllerRateScale oneQubitThreeQuarterExploration n :=
      hEuclideanBound n hn omega hgood

end

end QubitOracle.Paper
