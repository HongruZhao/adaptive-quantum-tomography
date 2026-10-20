import QubitOracle.Paper.OneQubitGeneralScheduleAdaptiveDesign
import QubitOracle.Paper.OneQubitCyclicBornPath

/-!
# Exact nested Born protocol for arbitrary predetermined qubit batches

This module supplies the exact binary Born response kernel for every physical
Bloch parameter and combines it with the concrete history-only arbitrary-batch
design.  Mathlib's Ionescu--Tulcea construction then gives one literal nested
infinite observation stream with its natural finite prefixes.
-/

namespace QubitOracle.Paper

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

local instance : MeasurableSpace BinaryOutcome := ⊤

/-- Bloch projection used by the general unit-axis Born response. -/
def generalAxisBornProjection
    (theta : OneQubitPhysicalParameter) (axis : MixedMeasurementAxis) : Real :=
  QubitOracle.blochDot axis.1 theta.1

theorem generalAxisBornProjection_abs_le_one
    (theta : OneQubitPhysicalParameter) (axis : MixedMeasurementAxis) :
    |generalAxisBornProjection theta axis| <= 1 := by
  have hnorm : blochNorm theta.1 <= 1 := by
    simpa [blochNorm] using (Real.sqrt_le_one.mpr theta.2)
  have hdot := abs_blochDot_le_blochNorm theta.1 axis.1 axis.2
  have hdot' : |QubitOracle.blochDot axis.1 theta.1| <= blochNorm theta.1 := by
    simpa [QubitOracle.blochDot, mul_comm] using hdot
  exact hdot'.trans hnorm

theorem generalAxisBornProbability_nonnegative
    (theta : OneQubitPhysicalParameter) (axis : MixedMeasurementAxis)
    (y : BinaryOutcome) :
    0 <= binaryBornProbability (generalAxisBornProjection theta axis) y := by
  have h := binaryBornProbability_lower_bound
    (generalAxisBornProjection theta axis) 1
    (generalAxisBornProjection_abs_le_one theta axis) y
  norm_num at h ⊢
  exact h

theorem binaryBornProbability_plus_add_minus (z : Real) :
    binaryBornProbability z BinaryOutcome.plus +
      binaryBornProbability z BinaryOutcome.minus = 1 := by
  simp [binaryBornProbability, BinaryOutcome.sign]
  ring

/-- Exact two-point Born measure for a physical state and a norm-bounded axis. -/
def generalAxisBornMeasure
    (theta : OneQubitPhysicalParameter) (axis : MixedMeasurementAxis) :
    Measure BinaryOutcome :=
  ENNReal.ofReal
      (binaryBornProbability (generalAxisBornProjection theta axis)
        BinaryOutcome.plus) • Measure.dirac BinaryOutcome.plus +
    ENNReal.ofReal
      (binaryBornProbability (generalAxisBornProjection theta axis)
        BinaryOutcome.minus) • Measure.dirac BinaryOutcome.minus

theorem generalAxisBornMeasure_univ
    (theta : OneQubitPhysicalParameter) (axis : MixedMeasurementAxis) :
    generalAxisBornMeasure theta axis Set.univ = 1 := by
  rw [generalAxisBornMeasure, Measure.add_apply,
    Measure.smul_apply, Measure.smul_apply]
  simp only [measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add
    (generalAxisBornProbability_nonnegative theta axis BinaryOutcome.plus)]
  rw [binaryBornProbability_plus_add_minus, ENNReal.ofReal_one]
  exact generalAxisBornProbability_nonnegative theta axis BinaryOutcome.minus

instance generalAxisBornMeasure_isProbability
    (theta : OneQubitPhysicalParameter) (axis : MixedMeasurementAxis) :
    IsProbabilityMeasure (generalAxisBornMeasure theta axis) where
  measure_univ := generalAxisBornMeasure_univ theta axis

private theorem generalAxisBornMass_measurable
    (theta : OneQubitPhysicalParameter) (y : BinaryOutcome) :
    Measurable (fun axis : MixedMeasurementAxis =>
      ENNReal.ofReal
        (binaryBornProbability (generalAxisBornProjection theta axis) y)) := by
  apply Measurable.ennreal_ofReal
  unfold binaryBornProbability generalAxisBornProjection QubitOracle.blochDot
  apply Measurable.div_const
  apply Measurable.add measurable_const
  apply Measurable.mul
  · exact measurable_const
  · apply Finset.measurable_sum
    intro i hi
    exact ((measurable_pi_apply i).comp measurable_subtype_coe).mul
      measurable_const

/-- Markov kernel whose conditional masses are the exact binary Born rule. -/
def generalAxisBornResponseKernel
    (theta : OneQubitPhysicalParameter) :
    Kernel MixedMeasurementAxis BinaryOutcome where
  toFun := generalAxisBornMeasure theta
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    by_cases hp : BinaryOutcome.plus ∈ s
    · by_cases hm : BinaryOutcome.minus ∈ s
      · have hsuniv : s = Set.univ := by
          ext y
          cases y <;> simp [hp, hm]
        subst s
        simp only [generalAxisBornMeasure_univ]
        exact measurable_const
      · have hsplus : s = {BinaryOutcome.plus} := by
          ext y
          cases y <;> simp [hp, hm]
        subst s
        simpa [generalAxisBornMeasure, Measure.add_apply,
          Measure.smul_apply] using
          (generalAxisBornMass_measurable theta BinaryOutcome.plus)
    · by_cases hm : BinaryOutcome.minus ∈ s
      · have hsminus : s = {BinaryOutcome.minus} := by
          ext y
          cases y <;> simp [hp, hm]
        subst s
        simpa [generalAxisBornMeasure, Measure.add_apply,
          Measure.smul_apply] using
          (generalAxisBornMass_measurable theta BinaryOutcome.minus)
      · have hsempty : s = (∅ : Set BinaryOutcome) := by
          ext y
          cases y <;> simp [hp, hm]
        subst s
        have hzero :
            (fun axis : MixedMeasurementAxis =>
              generalAxisBornMeasure theta axis (∅ : Set BinaryOutcome)) =
              fun _ => (0 : ENNReal) := by
          funext axis
          exact measure_empty
        rw [hzero]
        exact measurable_const

instance generalAxisBornResponseKernel_isMarkov
    (theta : OneQubitPhysicalParameter) :
    IsMarkovKernel (generalAxisBornResponseKernel theta) := by
  refine ⟨?_⟩
  intro axis
  exact generalAxisBornMeasure_isProbability theta axis

theorem generalAxisBornResponseKernel_singleton
    (theta : OneQubitPhysicalParameter) (axis : MixedMeasurementAxis)
    (y : BinaryOutcome) :
    generalAxisBornResponseKernel theta axis {y} =
      ENNReal.ofReal
        (binaryBornProbability (generalAxisBornProjection theta axis) y) := by
  change generalAxisBornMeasure theta axis {y} = _
  cases y <;>
    simp [generalAxisBornMeasure, Measure.add_apply, Measure.smul_apply]

/-- Exact predictable adaptive protocol for any admissible predetermined
batch schedule and deterministic frame seed. -/
def generalScheduleAdaptiveBornProtocol
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 -> Real) :
    PredictableAdaptiveProtocol OneQubitPhysicalParameter
      MixedMeasurementAxis BinaryOutcome where
  response := generalAxisBornResponseKernel
  response_isMarkov := generalAxisBornResponseKernel_isMarkov
  design := generalScheduleHistoryMeasurementAxis schedule b
  design_measurable := generalScheduleHistoryMeasurementAxis_measurable schedule b

/-- Its next-outcome conditional law is exactly the Born law at the concrete
history-selected axis. -/
theorem generalScheduleAdaptiveBornProtocol_conditional_mass
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 -> Real)
    (theta : OneQubitPhysicalParameter) (n : Nat)
    (history : AdaptiveTrajectory BinaryOutcome) (y : BinaryOutcome) :
    adaptiveStepKernel (generalScheduleAdaptiveBornProtocol schedule b)
        theta n history {y} =
      ENNReal.ofReal
        (binaryBornProbability
          (QubitOracle.blochDot
            (generalScheduleHistoryAxis schedule b n history) theta.1) y) := by
  rw [adaptiveStepKernel_apply]
  exact generalAxisBornResponseKernel_singleton theta
    (generalScheduleHistoryMeasurementAxis schedule b n history) y

/-- One literal nested infinite observation law for the arbitrary schedule. -/
def generalScheduleAdaptiveBornPathMeasure
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 -> Real)
    (theta : OneQubitPhysicalParameter) :
    Measure (AdaptiveInfinitePath BinaryOutcome) :=
  adaptiveInfiniteTrajectoryMeasure
    (generalScheduleAdaptiveBornProtocol schedule b) theta

instance generalScheduleAdaptiveBornPathMeasure_isProbability
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 -> Real)
    (theta : OneQubitPhysicalParameter) :
    IsProbabilityMeasure
      (generalScheduleAdaptiveBornPathMeasure schedule b theta) := by
  unfold generalScheduleAdaptiveBornPathMeasure
  infer_instance

/-- The first `n` observations are literally the natural prefix of the same
infinite Born path. -/
def generalScheduleAdaptiveBornPrefix
    (n : Nat) : AdaptiveInfinitePath BinaryOutcome ->
      AdaptiveTrajectory BinaryOutcome :=
  adaptiveInfinitePathPrefix n

theorem generalScheduleAdaptiveBornPrefix_measurable (n : Nat) :
    Measurable (generalScheduleAdaptiveBornPrefix n) :=
  measurable_adaptiveInfinitePathPrefix n

end

end QubitOracle.Paper
