import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.ConcreteProtocolA1A3
import QubitOracle.Paper.MixedAxisFisher
import QubitOracle.Paper.MixedProbabilityFloor
import QubitOracle.Paper.OneQubitAPSRLSContract
import QubitOracle.Paper.OneQubitCyclicBornPath
import QubitOracle.Paper.OneQubitFixedDesignInformation
import QubitOracle.Paper.OneQubitGeneralScheduleAdaptiveBornProtocol
import QubitOracle.Paper.OneQubitGeneralScheduleAdaptiveScoreCondExp
/-! Supporting definitions and proved lemmas used by the manuscript. -/

namespace QubitOracle.Paper

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Matrix

noncomputable section

/-- Axis label together with its signed projective outcome. -/
abbrev LabeledBinaryOutcome := Fin 3 × BinaryOutcome

local instance labeledBinaryOutcomeMeasurableSpace :
    MeasurableSpace LabeledBinaryOutcome := ⊤

/-- Three norm-bounded axes defining one labeled randomized measurement. -/
structure QubitThreeAxisFrame where
  axis : Fin 3 -> MixedMeasurementAxis

/-- A deterministic Pauli pilot action or a uniformly randomized labeled
three-axis frame action. -/
inductive QubitLabeledMeasurementAction where
  | pilot (j : Fin 3)
  | frame (frame : QubitThreeAxisFrame)

instance qubitLabeledMeasurementActionMeasurableSpace :
    MeasurableSpace QubitLabeledMeasurementAction := ⊤

/-- Cartesian Pauli axis packaged with its physical norm certificate. -/
def qubitPauliMixedMeasurementAxis (j : Fin 3) : MixedMeasurementAxis :=
  ⟨qubitPauliCoordinateAxis j,
    (qubitPauliCoordinateAxis_normSq j).le⟩

/-- Axis associated with a possible label under an action.  Labels outside a
pilot action's support are assigned their corresponding Pauli axes. -/
def qubitLabeledActionAxis
    (action : QubitLabeledMeasurementAction) (j : Fin 3) :
    MixedMeasurementAxis :=
  match action with
  | .pilot _ => qubitPauliMixedMeasurementAxis j
  | .frame frame => frame.axis j

/-- Classical label probability: a point mass for a pilot and uniform for a
frame observation. -/
def qubitLabeledActionWeight
    (action : QubitLabeledMeasurementAction) (j : Fin 3) : Real :=
  match action with
  | .pilot j0 => if j = j0 then 1 else 0
  | .frame _ => 1 / 3

theorem qubitLabeledActionWeight_nonnegative
    (action : QubitLabeledMeasurementAction) (j : Fin 3) :
    0 <= qubitLabeledActionWeight action j := by
  cases action with
  | pilot j0 =>
      by_cases h : j = j0 <;>
        simp [qubitLabeledActionWeight, h]
  | frame frame =>
      norm_num [qubitLabeledActionWeight]

theorem qubitLabeledActionWeight_sum
    (action : QubitLabeledMeasurementAction) :
    (∑ j : Fin 3, qubitLabeledActionWeight action j) = 1 := by
  cases action with
  | pilot j0 =>
      simp [qubitLabeledActionWeight]
  | frame frame =>
      norm_num [qubitLabeledActionWeight, Fin.sum_univ_succ]

/-- Exact joint Born probability of a label and signed outcome. -/
def qubitLabeledBornProbability
    (theta : OneQubitPhysicalParameter)
    (action : QubitLabeledMeasurementAction)
    (z : LabeledBinaryOutcome) : Real :=
  qubitLabeledActionWeight action z.1 *
    binaryBornProbability
      (generalAxisBornProjection theta
        (qubitLabeledActionAxis action z.1)) z.2

theorem qubitLabeledBornProbability_nonnegative
    (theta : OneQubitPhysicalParameter)
    (action : QubitLabeledMeasurementAction)
    (z : LabeledBinaryOutcome) :
    0 <= qubitLabeledBornProbability theta action z := by
  exact mul_nonneg
    (qubitLabeledActionWeight_nonnegative action z.1)
    (generalAxisBornProbability_nonnegative theta
      (qubitLabeledActionAxis action z.1) z.2)

/-- The six joint masses sum to one for every physical state and action. -/
theorem qubitLabeledBornProbability_sum
    (theta : OneQubitPhysicalParameter)
    (action : QubitLabeledMeasurementAction) :
    (∑ z : LabeledBinaryOutcome,
      qubitLabeledBornProbability theta action z) = 1 := by
  rw [Fintype.sum_prod_type]
  calc
    (∑ j : Fin 3, ∑ y : BinaryOutcome,
        qubitLabeledBornProbability theta action (j, y)) =
        ∑ j : Fin 3, qubitLabeledActionWeight action j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [sum_binaryOutcome]
      simp only [qubitLabeledBornProbability]
      rw [← mul_add]
      rw [binaryBornProbability_plus_add_minus]
      ring
    _ = 1 := qubitLabeledActionWeight_sum action

/-- Finite exact Born measure of the labeled action. -/
def qubitLabeledBornMeasure
    (theta : OneQubitPhysicalParameter)
    (action : QubitLabeledMeasurementAction) :
    Measure LabeledBinaryOutcome :=
  ∑ z : LabeledBinaryOutcome,
    ENNReal.ofReal (qubitLabeledBornProbability theta action z) •
      Measure.dirac z

theorem qubitLabeledBornMeasure_univ
    (theta : OneQubitPhysicalParameter)
    (action : QubitLabeledMeasurementAction) :
    qubitLabeledBornMeasure theta action Set.univ = 1 := by
  simp only [qubitLabeledBornMeasure, Measure.finset_sum_apply,
    Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · rw [qubitLabeledBornProbability_sum, ENNReal.ofReal_one]
  · intro z hz
    exact qubitLabeledBornProbability_nonnegative theta action z

instance qubitLabeledBornMeasure_isProbability
    (theta : OneQubitPhysicalParameter)
    (action : QubitLabeledMeasurementAction) :
    IsProbabilityMeasure (qubitLabeledBornMeasure theta action) where
  measure_univ := qubitLabeledBornMeasure_univ theta action

/-- Markov response kernel for the labeled pilot/frame action. -/
def qubitLabeledBornResponseKernel
    (theta : OneQubitPhysicalParameter) :
    Kernel QubitLabeledMeasurementAction LabeledBinaryOutcome where
  toFun := qubitLabeledBornMeasure theta
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    intro t ht
    trivial

instance qubitLabeledBornResponseKernel_isMarkov
    (theta : OneQubitPhysicalParameter) :
    IsMarkovKernel (qubitLabeledBornResponseKernel theta) := by
  refine ⟨?_⟩
  intro action
  exact qubitLabeledBornMeasure_isProbability theta action

/-- Exact singleton mass of the labeled response kernel. -/
theorem qubitLabeledBornResponseKernel_singleton
    (theta : OneQubitPhysicalParameter)
    (action : QubitLabeledMeasurementAction)
    (z : LabeledBinaryOutcome) :
    qubitLabeledBornResponseKernel theta action {z} =
      ENNReal.ofReal (qubitLabeledBornProbability theta action z) := by
  change qubitLabeledBornMeasure theta action {z} = _
  classical
  rw [qubitLabeledBornMeasure, Measure.finset_sum_apply]
  rw [Finset.sum_eq_single z]
  · simp [Measure.smul_apply]
  · intro w hw hwz
    simp [Measure.smul_apply, hwz]
  · simp


/-- Predictable Fisher matrix of one labeled action. -/
def qubitLabeledActionFisher
    (theta : RLSVector 3)
    (action : QubitLabeledMeasurementAction) :
    Matrix (Fin 3) (Fin 3) Real :=
  ∑ j : Fin 3, qubitLabeledActionWeight action j •
    QubitOracle.mixedAxisFisher theta
      (qubitLabeledActionAxis action j).1



/-- A pilot action has exactly the Fisher matrix of its selected Pauli
coordinate. -/
theorem qubitLabeledActionFisher_pilot
    (theta : RLSVector 3) (j : Fin 3) :
    qubitLabeledActionFisher theta (.pilot j) =
      QubitOracle.mixedAxisFisher theta (qubitPauliCoordinateAxis j) := by
  ext i ell
  simp [qubitLabeledActionFisher, qubitLabeledActionWeight,
    qubitLabeledActionAxis, qubitPauliMixedMeasurementAxis]


end

end QubitOracle.Paper
