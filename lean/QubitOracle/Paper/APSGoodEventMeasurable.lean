import QubitOracle.Paper.OneQubitBornAPSController

namespace QubitOracle.Paper

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

noncomputable section

namespace PopularRLSConditions

open SourceFaithfulSelfNormalized

/-- Coordinatewise measurability for a finite real matrix-valued map. -/
def MatrixCoordinateMeasurable
    {Omega : Type*} [MeasurableSpace Omega] {d : Nat}
    (A : Omega -> Matrix (Fin d) (Fin d) Real) : Prop :=
  forall i j, Measurable (fun omega => A omega i j)

lemma matrixCoordinateMeasurable_vectorOuterProduct
    {Omega : Type*} [MeasurableSpace Omega] {d : Nat}
    {x : Omega -> Fin d -> Real} (hx : Measurable x) :
    MatrixCoordinateMeasurable (fun omega => vectorOuterProduct (x omega)) := by
  intro i j
  exact hx.eval.mul hx.eval

lemma matrixCoordinateMeasurable_gramProcess
    {Omega : Type*} [MeasurableSpace Omega]
    {d : Nat} {mu : Measure Omega} {R : Real}
    (data : SelfNormalizedMartingaleData Omega d mu R) (t : Nat) :
    MatrixCoordinateMeasurable (fun omega => gramProcess data t omega) := by
  intro i j
  unfold gramProcess
  simp_rw [Matrix.sum_apply]
  apply Finset.measurable_sum
  intro k hk
  exact matrixCoordinateMeasurable_vectorOuterProduct
    data.regressorAdapted.measurable i j

lemma matrixCoordinateMeasurable_aps2011Theorem2Gram
    {Omega : Type*} [MeasurableSpace Omega]
    {d : Nat} {mu : Measure Omega} {R : Real}
    (data : SelfNormalizedMartingaleData Omega d mu R)
    (regularization : Real) (t : Nat) :
    MatrixCoordinateMeasurable
      (fun omega => aps2011Theorem2Gram data regularization t omega) := by
  intro i j
  unfold aps2011Theorem2Gram regularizedGram
  exact measurable_const.add
    (matrixCoordinateMeasurable_gramProcess data t i j)

lemma measurable_matrix_det_of_coordinates
    {Omega : Type*} [MeasurableSpace Omega] {d : Nat}
    {A : Omega -> Matrix (Fin d) (Fin d) Real}
    (hA : MatrixCoordinateMeasurable A) :
    Measurable (fun omega => (A omega).det) := by
  simp_rw [Matrix.det_apply']
  apply Finset.measurable_sum
  intro sigma hsigma
  apply measurable_const.mul
  apply Finset.measurable_prod
  intro i hi
  exact hA (sigma i) i

lemma measurable_matrix_adjugate_coordinate
    {Omega : Type*} [MeasurableSpace Omega] {d : Nat}
    {A : Omega -> Matrix (Fin d) (Fin d) Real}
    (hA : MatrixCoordinateMeasurable A) (i j : Fin d) :
    Measurable (fun omega => (A omega).adjugate i j) := by
  simp_rw [Matrix.adjugate_apply]
  apply measurable_matrix_det_of_coordinates
  intro a b
  by_cases h : a = j
  · subst a
    simp
  · simp [Matrix.updateRow_apply, h]
    exact hA a b

lemma measurable_matrix_inv_coordinate
    {Omega : Type*} [MeasurableSpace Omega] {d : Nat}
    {A : Omega -> Matrix (Fin d) (Fin d) Real}
    (hA : MatrixCoordinateMeasurable A) (i j : Fin d) :
    Measurable (fun omega => (A omega)⁻¹ i j) := by
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul,
    Ring.inverse_eq_inv]
  exact (measurable_matrix_det_of_coordinates hA).inv.mul
    (measurable_matrix_adjugate_coordinate hA i j)

lemma measurable_aps2011Theorem2ResponseMoment_coordinate
    {Omega : Type*} [MeasurableSpace Omega]
    {d : Nat} {mu : Measure Omega} {R : Real}
    (data : SelfNormalizedMartingaleData Omega d mu R)
    (observation : Nat -> Omega -> Real)
    (hObservation : forall k, Measurable (observation (k + 1)))
    (t : Nat) (j : Fin d) :
    Measurable (fun omega =>
      aps2011Theorem2ResponseMoment data observation t omega j) := by
  unfold aps2011Theorem2ResponseMoment
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.measurable_sum
  intro k hk
  exact (hObservation k).mul data.regressorAdapted.measurable.eval

lemma measurable_aps2011Theorem2Estimator_coordinate
    {Omega : Type*} [MeasurableSpace Omega]
    {d : Nat} {mu : Measure Omega} {R : Real}
    (data : SelfNormalizedMartingaleData Omega d mu R)
    (observation : Nat -> Omega -> Real)
    (hObservation : forall k, Measurable (observation (k + 1)))
    (regularization : Real) (t : Nat) (i : Fin d) :
    Measurable (fun omega =>
      aps2011Theorem2Estimator data observation regularization t omega i) := by
  unfold aps2011Theorem2Estimator Matrix.mulVec dotProduct
  apply Finset.measurable_sum
  intro j hj
  exact (measurable_matrix_inv_coordinate
    (matrixCoordinateMeasurable_aps2011Theorem2Gram data regularization t) i j).mul
    (measurable_aps2011Theorem2ResponseMoment_coordinate
      data observation hObservation t j)

lemma measurable_aps2011Theorem2Error_coordinate
    {Omega : Type*} [MeasurableSpace Omega]
    {d : Nat} {mu : Measure Omega} {R : Real}
    (data : SelfNormalizedMartingaleData Omega d mu R)
    (thetaStar : Fin d -> Real) (observation : Nat -> Omega -> Real)
    (hObservation : forall k, Measurable (observation (k + 1)))
    (regularization : Real) (t : Nat) (i : Fin d) :
    Measurable (fun omega =>
      aps2011Theorem2Error data thetaStar observation regularization t omega i) := by
  unfold aps2011Theorem2Error
  exact (measurable_aps2011Theorem2Estimator_coordinate data observation
    hObservation regularization t i).sub measurable_const

lemma measurable_aps2011Theorem2Gram_mulVec_error_coordinate
    {Omega : Type*} [MeasurableSpace Omega]
    {d : Nat} {mu : Measure Omega} {R : Real}
    (data : SelfNormalizedMartingaleData Omega d mu R)
    (thetaStar : Fin d -> Real) (observation : Nat -> Omega -> Real)
    (hObservation : forall k, Measurable (observation (k + 1)))
    (regularization : Real) (t : Nat) (i : Fin d) :
    Measurable (fun omega =>
      (aps2011Theorem2Gram data regularization t omega).mulVec
        (aps2011Theorem2Error data thetaStar observation regularization t omega) i) := by
  unfold Matrix.mulVec dotProduct
  apply Finset.measurable_sum
  intro j hj
  exact (matrixCoordinateMeasurable_aps2011Theorem2Gram data regularization t i j).mul
    (measurable_aps2011Theorem2Error_coordinate data thetaStar observation
      hObservation regularization t j)

lemma measurable_aps2011Theorem2WeightedError
    {Omega : Type*} [MeasurableSpace Omega]
    {d : Nat} {mu : Measure Omega} {R : Real}
    (data : SelfNormalizedMartingaleData Omega d mu R)
    (thetaStar : Fin d -> Real) (observation : Nat -> Omega -> Real)
    (hObservation : forall k, Measurable (observation (k + 1)))
    (regularization : Real) (t : Nat) :
    Measurable (fun omega =>
      aps2011Theorem2WeightedError data thetaStar observation
        regularization t omega) := by
  unfold aps2011Theorem2WeightedError weightedNormSq
  apply Measurable.sqrt
  apply Finset.measurable_sum
  intro i hi
  exact (measurable_aps2011Theorem2Error_coordinate data thetaStar observation
    hObservation regularization t i).mul
    (measurable_aps2011Theorem2Gram_mulVec_error_coordinate data thetaStar
      observation hObservation regularization t i)

lemma measurable_aps2011Theorem2Radius
    {Omega : Type*} [MeasurableSpace Omega]
    {d : Nat} {mu : Measure Omega} {R : Real}
    (data : SelfNormalizedMartingaleData Omega d mu R)
    (regularization parameterRadius delta : Real) (t : Nat) :
    Measurable (fun omega =>
      aps2011Theorem2Radius data regularization parameterRadius delta t omega) := by
  unfold aps2011Theorem2Radius
  have hDet : Measurable (fun omega =>
      (aps2011Theorem2Gram data regularization t omega).det) :=
    measurable_matrix_det_of_coordinates
      (matrixCoordinateMeasurable_aps2011Theorem2Gram data regularization t)
  fun_prop

/-- The simultaneous APS confidence event is measurable whenever every
observation coordinate is measurable. -/
theorem measurableSet_aps2011Theorem2GoodEvent
    {Omega : Type*} [MeasurableSpace Omega]
    {d : Nat} {mu : Measure Omega} {R : Real}
    (data : SelfNormalizedMartingaleData Omega d mu R)
    (thetaStar : Fin d -> Real) (observation : Nat -> Omega -> Real)
    (hObservation : forall k, Measurable (observation (k + 1)))
    (regularization parameterRadius delta : Real) :
    MeasurableSet (aps2011Theorem2GoodEvent data thetaStar observation
      regularization parameterRadius delta) := by
  unfold aps2011Theorem2GoodEvent
  rw [show {omega | forall t : Nat,
      aps2011Theorem2WeightedError data thetaStar observation regularization t omega <=
        aps2011Theorem2Radius data regularization parameterRadius delta t omega} =
      ⋂ t : Nat, {omega |
        aps2011Theorem2WeightedError data thetaStar observation regularization t omega <=
          aps2011Theorem2Radius data regularization parameterRadius delta t omega} by
      ext omega
      simp]
  exact MeasurableSet.iInter fun t => measurableSet_le
    (measurable_aps2011Theorem2WeightedError data thetaStar observation
      hObservation regularization t)
    (measurable_aps2011Theorem2Radius data regularization parameterRadius delta t)

end PopularRLSConditions

/-- In the binary Born regression, each used response is measurable because it
is centered noise plus the predictable Bloch inner product. -/
theorem BinaryQubitRLSReducedProbabilityPremises.observationMeasurable_succ
    {Omega : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 -> Real}
    {axis : Nat -> Omega -> Fin 3 -> Real}
    {outcome : Nat -> Omega -> QubitRLSOutcome}
    (protocol : BinaryQubitRLSReducedProbabilityPremises
      Omega mu theta axis outcome) (k : Nat) :
    Measurable (oneQubitRLSObservation outcome (k + 1)) := by
  have hAxis : Measurable (axis k) := protocol.axisAdapted.measurable
  have hDot : Measurable (fun omega => QubitOracle.blochDot (axis k omega) theta) := by
    unfold QubitOracle.blochDot
    apply Finset.measurable_sum
    intro i hi
    exact hAxis.eval.mul measurable_const
  convert (protocol.noiseMeasurable (k + 1)).add hDot using 1
  funext omega
  simp [oneQubitRLSNoise, oneQubitRLSObservation, qubitRLSScalarNoise]

/-- The APS all-time confidence event is automatically measurable for every
binary Born protocol satisfying the reduced probability premises. -/
theorem BinaryQubitRLSReducedProbabilityPremises.measurableSet_apsGoodEvent
    {Omega : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 -> Real}
    {axis : Nat -> Omega -> Fin 3 -> Real}
    {outcome : Nat -> Omega -> QubitRLSOutcome}
    (protocol : BinaryQubitRLSReducedProbabilityPremises
      Omega mu theta axis outcome)
    (hTheta : QubitOracle.blochNormSq theta <= 1)
    (regularization parameterRadius delta : Real) :
    MeasurableSet
      (PopularRLSConditions.aps2011Theorem2GoodEvent
        (protocol.toSelfNormalizedMartingaleData hTheta) theta
        (oneQubitRLSObservation outcome) regularization parameterRadius delta) :=
  PopularRLSConditions.measurableSet_aps2011Theorem2GoodEvent
    (protocol.toSelfNormalizedMartingaleData hTheta) theta
    (oneQubitRLSObservation outcome)
    protocol.observationMeasurable_succ regularization parameterRadius delta

/-- Physical one-qubit APS-to-controller theorem with good-event
measurability discharged internally. -/
theorem oneQubitBornRLSController_of_aps2011_autoGoodEventMeasurable
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
    (constant : Real) (hConstant : 0 <= constant)
    (hBound : forall n omega,
      omega ∈ PopularRLSConditions.aps2011Theorem2GoodEvent
        (protocol.toSelfNormalizedMartingaleData hTheta) theta
        (oneQubitRLSObservation outcome) regularization 1
        (oneQubitPolynomialConfidenceLevel n) ->
      ‖controller n omega - truth‖ <=
        constant * controllerRateScale oneQubitThreeQuarterExploration n)
    (hScaledMeasurable : forall n,
      AEStronglyMeasurable (scaledControllerNormError controller truth n) mu) :
    AlmostSureControllerRate mu controller truth oneQubitThreeQuarterExploration ∧
      (∀ᵐ omega ∂mu, Filter.Tendsto (fun n => controller n omega)
        Filter.atTop (nhds truth)) ∧
      TendstoInMeasure mu (scaledControllerNormError controller truth)
        Filter.atTop (fun _ => 0) := by
  exact oneQubitBornRLSController_of_aps2011_threeQuarterPolynomialSchedule
    protocol hTheta regularization hRegularization controller truth
    (fun n => protocol.measurableSet_apsGoodEvent hTheta regularization 1
      (oneQubitPolynomialConfidenceLevel n))
    constant hConstant hBound hScaledMeasurable

end

end QubitOracle.Paper
