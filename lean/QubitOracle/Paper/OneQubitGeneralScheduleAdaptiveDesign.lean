import QubitOracle.Paper.OneQubitGeneralScheduleTrajectoryIndexing
import QubitOracle.Paper.ConcreteProtocolA1A3

/-!
# Concrete history-only design for arbitrary predetermined qubit batches

The controller below is computed from the pilot outcomes in completed earlier
batches of one literal chronological history.  The next measurement axis is a
Cartesian Pauli axis on exploration shots and an axis of the safeguarded Bures
frame on exploitation shots.  The construction is total on malformed finite
histories by a fixed `plus` fallback, while the actual trajectory prefixes
always contain every index used by the controller.
-/

namespace QubitOracle.Paper

open scoped BigOperators
open PureMultilevelSequentialBatchAdaptive

noncomputable section

local instance : MeasurableSpace BinaryOutcome := ⊤

/-- Total lookup from a finite history, with a fixed fallback used only for
malformed histories shorter than their nominal protocol time. -/
def generalScheduleHistoryOutcomeAt
    (history : AdaptiveTrajectory BinaryOutcome) (n : Nat) : BinaryOutcome :=
  history.outcomes.getD n BinaryOutcome.plus

/-- Sum of all signed Pauli outcomes in coordinate `j` from pilot blocks in
completed batches `0, ..., k-1`. -/
def generalScheduleHistoryPilotCoordinateSum
    (schedule : CumulativePauliPilotBatchSchedule) (k : Nat)
    (history : AdaptiveTrajectory BinaryOutcome) (j : Fin 3) : Real :=
  ∑ r ∈ Finset.range k,
    ∑ q : Fin (schedule.pilotBlocks r),
      (generalScheduleHistoryOutcomeAt history
        (generalSchedulePilotShotRank schedule ⟨r, q⟩ j)).sign

/-- Literal pooled past-only Pauli controller on one chronological history. -/
def generalScheduleHistoryController
    (schedule : CumulativePauliPilotBatchSchedule) (k : Nat)
    (history : AdaptiveTrajectory BinaryOutcome) : Fin 3 -> Real :=
  if schedule.pastPilotBlockCount k = 0 then 0
  else fun j =>
    (schedule.pastPilotBlockCount k : Real)⁻¹ *
      generalScheduleHistoryPilotCoordinateSum schedule k history j

theorem generalScheduleHistoryController_zero
    (schedule : CumulativePauliPilotBatchSchedule) (k : Nat)
    (history : AdaptiveTrajectory BinaryOutcome)
    (hk : schedule.pastPilotBlockCount k = 0) :
    generalScheduleHistoryController schedule k history = 0 := by
  simp [generalScheduleHistoryController, hk]

theorem generalScheduleHistoryController_positive
    (schedule : CumulativePauliPilotBatchSchedule) (k : Nat)
    (history : AdaptiveTrajectory BinaryOutcome)
    (hk : 0 < schedule.pastPilotBlockCount k) (j : Fin 3) :
    generalScheduleHistoryController schedule k history j =
      (schedule.pastPilotBlockCount k : Real)⁻¹ *
        generalScheduleHistoryPilotCoordinateSum schedule k history j := by
  simp [generalScheduleHistoryController, Nat.ne_of_gt hk]

/-- Every pilot observation used for batch `k` occurs strictly before the
start of that batch in the literal global order. -/
theorem generalSchedulePilotShotRank_lt_batchStart
    (schedule : CumulativePauliPilotBatchSchedule)
    {r k : Nat} (hrk : r < k)
    (q : Fin (schedule.pilotBlocks r)) (j : Fin 3) :
    generalSchedulePilotShotRank schedule ⟨r, q⟩ j <
      cumulativeCount schedule.budget.batchSize k := by
  let shot := generalSchedulePilotShot schedule
    (⟨r, q⟩ : GeneralSchedulePilotBlockIndex schedule) j
  have hinside : generalScheduleGlobalShotRank schedule shot <
      cumulativeCount schedule.budget.batchSize (r + 1) := by
    unfold generalScheduleGlobalShotRank
    rw [cumulativeCount_succ_general]
    exact Nat.add_lt_add_left shot.2.isLt _
  have hmono :=
    (cumulativeCount_strictMono_of_pos_general
      schedule.budget.batchSize schedule.budget.batchSize_pos).monotone
      (show r + 1 <= k by omega)
  exact hinside.trans_le hmono

/-- Hence every pilot observation used by the controller at global time `n`
has rank strictly below `n`. -/
theorem generalSchedulePilotShotRank_lt_current
    (schedule : CumulativePauliPilotBatchSchedule) (n : Nat)
    {r : Nat} (hr : r < generalScheduleGlobalBatch schedule n)
    (q : Fin (schedule.pilotBlocks r)) (j : Fin 3) :
    generalSchedulePilotShotRank schedule ⟨r, q⟩ j < n := by
  exact (generalSchedulePilotShotRank_lt_batchStart schedule hr q j).trans_le
    (generalScheduleGlobalBatch_lower schedule n)

/-- Three-cycle slot of a global shot within its decoded batch. -/
def generalScheduleGlobalAxisSlot
    (schedule : CumulativePauliPilotBatchSchedule) (n : Nat) : Fin 3 :=
  ⟨generalScheduleGlobalWithin schedule n % 3,
    Nat.mod_lt _ (by norm_num)⟩

/-- Whether global shot `n` belongs to the scheduled cyclic-Pauli exploration
prefix of its batch. -/
def generalScheduleIsExplorationShot
    (schedule : CumulativePauliPilotBatchSchedule) (n : Nat) : Prop :=
  generalScheduleGlobalWithin schedule n <
    schedule.budget.explorationSize (generalScheduleGlobalBatch schedule n)

instance generalScheduleIsExplorationShot_decidable
    (schedule : CumulativePauliPilotBatchSchedule) (n : Nat) :
    Decidable (generalScheduleIsExplorationShot schedule n) := by
  unfold generalScheduleIsExplorationShot
  infer_instance

/-- The concrete next axis selected from the observed history only. -/
def generalScheduleHistoryAxis
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 -> Real)
    (n : Nat) (history : AdaptiveTrajectory BinaryOutcome) : Fin 3 -> Real :=
  if generalScheduleIsExplorationShot schedule n then
    qubitPauliCoordinateAxis (generalScheduleGlobalAxisSlot schedule n)
  else
    mixedTwoStageFrameAxis
      (mixedPilotSelectedLocalFrame b
        (generalScheduleHistoryController schedule
          (generalScheduleGlobalBatch schedule n) history))
      (generalScheduleGlobalAxisSlot schedule n)

theorem generalScheduleHistoryAxis_normSq
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 -> Real)
    (n : Nat) (history : AdaptiveTrajectory BinaryOutcome) :
    QubitOracle.blochNormSq
      (generalScheduleHistoryAxis schedule b n history) = 1 := by
  by_cases h : generalScheduleIsExplorationShot schedule n
  · rw [generalScheduleHistoryAxis, if_pos h]
    exact qubitPauliCoordinateAxis_normSq _
  · rw [generalScheduleHistoryAxis, if_neg h]
    change QubitOracle.blochNormSq
      (qubitFrameAxis
        (mixedPilotSelectedLocalFrame b
          (generalScheduleHistoryController schedule
            (generalScheduleGlobalBatch schedule n) history))
        (generalScheduleGlobalAxisSlot schedule n)) = 1
    exact mixedPilotSelectedLocalFrame_axis_unit _ _ _

/-- The selected history-only axis packaged with its physical norm bound. -/
def generalScheduleHistoryMeasurementAxis
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 -> Real)
    (n : Nat) (history : AdaptiveTrajectory BinaryOutcome) :
    MixedMeasurementAxis :=
  ⟨generalScheduleHistoryAxis schedule b n history,
    by rw [generalScheduleHistoryAxis_normSq]⟩

/-- Predictability/measurability of the concrete arbitrary-batch design. -/
theorem generalScheduleHistoryMeasurementAxis_measurable
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 -> Real)
    (n : Nat) :
    Measurable (generalScheduleHistoryMeasurementAxis schedule b n) :=
  measurable_of_countable _

theorem generalScheduleHistoryAxis_exploration
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 -> Real)
    (n : Nat) (history : AdaptiveTrajectory BinaryOutcome)
    (h : generalScheduleIsExplorationShot schedule n) :
    generalScheduleHistoryAxis schedule b n history =
      qubitPauliCoordinateAxis (generalScheduleGlobalAxisSlot schedule n) := by
  simp [generalScheduleHistoryAxis, h]

theorem generalScheduleHistoryAxis_exploitation
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 -> Real)
    (n : Nat) (history : AdaptiveTrajectory BinaryOutcome)
    (h : Not (generalScheduleIsExplorationShot schedule n)) :
    generalScheduleHistoryAxis schedule b n history =
      mixedTwoStageFrameAxis
        (mixedPilotSelectedLocalFrame b
          (generalScheduleHistoryController schedule
            (generalScheduleGlobalBatch schedule n) history))
        (generalScheduleGlobalAxisSlot schedule n) := by
  simp [generalScheduleHistoryAxis, h]

end

end QubitOracle.Paper
