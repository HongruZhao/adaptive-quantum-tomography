import QubitOracle.Paper.OneQubitGeneralScheduleCumulativePilotInformation

/-!
# Global trajectory indexing for arbitrary predetermined qubit batches

This module converts the arbitrary positive batch schedule into a literal
global observation order.  It proves that every global shot has a unique
batch/within-batch coordinate and that every scheduled three-Pauli pilot block
has three explicit ranks in that order.  All statements are deterministic and
introduce no probabilistic or literature assumption.
-/

namespace QubitOracle.Paper

open Filter
open scoped Topology
open PureMultilevelSequentialBatchAdaptive

noncomputable section

theorem cumulativeCount_succ_general (count : Nat -> Nat) (k : Nat) :
    cumulativeCount count (k + 1) = cumulativeCount count k + count k := by
  simp [cumulativeCount, Finset.sum_range_succ]

theorem cumulativeCount_strictMono_of_pos_general
    (count : Nat -> Nat) (hpos : forall k, 0 < count k) :
    StrictMono (cumulativeCount count) := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [cumulativeCount_succ_general]
  have hk := hpos k
  omega

theorem CumulativePauliPilotBatchSchedule.exists_batch_for_global_shot
    (schedule : CumulativePauliPilotBatchSchedule) (n : Nat) :
    exists K : Nat,
      n < cumulativeCount schedule.budget.batchSize (K + 1) := by
  have hevent : ∀ᶠ K in atTop,
      (n + 1 : Real) <=
        (cumulativeCount schedule.budget.batchSize K : Real) :=
    (tendsto_atTop.1 schedule.budget.totalSamples_tendsto_atTop) (n + 1)
  obtain ⟨K, hK⟩ := eventually_atTop.1 hevent
  refine ⟨K, ?_⟩
  have hreal := hK (K + 1) (Nat.le_add_right K 1)
  exact_mod_cast hreal

/-- Batch containing global observation number `n`. -/
def generalScheduleGlobalBatch
    (schedule : CumulativePauliPilotBatchSchedule) (n : Nat) : Nat :=
  Nat.find (schedule.exists_batch_for_global_shot n)

theorem generalScheduleGlobalBatch_upper
    (schedule : CumulativePauliPilotBatchSchedule) (n : Nat) :
    n < cumulativeCount schedule.budget.batchSize
      (generalScheduleGlobalBatch schedule n + 1) :=
  Nat.find_spec (schedule.exists_batch_for_global_shot n)

theorem generalScheduleGlobalBatch_lower
    (schedule : CumulativePauliPilotBatchSchedule) (n : Nat) :
    cumulativeCount schedule.budget.batchSize
      (generalScheduleGlobalBatch schedule n) <= n := by
  by_cases hzero : generalScheduleGlobalBatch schedule n = 0
  · simp [hzero, cumulativeCount]
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    have hminimal := Nat.find_min
      (schedule.exists_batch_for_global_shot n)
      (show j < generalScheduleGlobalBatch schedule n by omega)
    rw [hj]
    simpa only [Nat.succ_eq_add_one, not_lt] using hminimal

/-- Coordinate of global observation `n` inside its decoded batch. -/
def generalScheduleGlobalWithin
    (schedule : CumulativePauliPilotBatchSchedule) (n : Nat) : Nat :=
  n - cumulativeCount schedule.budget.batchSize
    (generalScheduleGlobalBatch schedule n)

theorem generalScheduleGlobalWithin_lt_batchSize
    (schedule : CumulativePauliPilotBatchSchedule) (n : Nat) :
    generalScheduleGlobalWithin schedule n <
      schedule.budget.batchSize (generalScheduleGlobalBatch schedule n) := by
  have hu := generalScheduleGlobalBatch_upper schedule n
  have hl := generalScheduleGlobalBatch_lower schedule n
  rw [cumulativeCount_succ_general] at hu
  unfold generalScheduleGlobalWithin
  omega

/-- Batch-major index type for every observation in the infinite schedule. -/
abbrev GeneralScheduleShotIndex
    (schedule : CumulativePauliPilotBatchSchedule) : Type :=
  Sigma fun k : Nat => Fin (schedule.budget.batchSize k)

/-- Decode a global natural number into its batch-major shot. -/
def generalScheduleGlobalShot
    (schedule : CumulativePauliPilotBatchSchedule) (n : Nat) :
    GeneralScheduleShotIndex schedule :=
  ⟨generalScheduleGlobalBatch schedule n,
    ⟨generalScheduleGlobalWithin schedule n,
      generalScheduleGlobalWithin_lt_batchSize schedule n⟩⟩

/-- Encode a batch-major shot into the global observation order. -/
def generalScheduleGlobalShotRank
    (schedule : CumulativePauliPilotBatchSchedule)
    (shot : GeneralScheduleShotIndex schedule) : Nat :=
  cumulativeCount schedule.budget.batchSize shot.1 + shot.2.val

@[simp] theorem generalScheduleGlobalShotRank_globalShot
    (schedule : CumulativePauliPilotBatchSchedule) (n : Nat) :
    generalScheduleGlobalShotRank schedule
      (generalScheduleGlobalShot schedule n) = n := by
  unfold generalScheduleGlobalShotRank generalScheduleGlobalShot
    generalScheduleGlobalWithin
  exact Nat.add_sub_of_le (generalScheduleGlobalBatch_lower schedule n)

theorem generalScheduleGlobalBatch_globalShotRank
    (schedule : CumulativePauliPilotBatchSchedule)
    (shot : GeneralScheduleShotIndex schedule) :
    generalScheduleGlobalBatch schedule
      (generalScheduleGlobalShotRank schedule shot) = shot.1 := by
  apply Nat.le_antisymm
  · apply Nat.find_min'
    unfold generalScheduleGlobalShotRank
    rw [cumulativeCount_succ_general]
    omega
  · by_contra hnot
    have hlt : generalScheduleGlobalBatch schedule
        (generalScheduleGlobalShotRank schedule shot) < shot.1 :=
      Nat.lt_of_not_ge hnot
    have hu := generalScheduleGlobalBatch_upper schedule
      (generalScheduleGlobalShotRank schedule shot)
    have hmono :=
      (cumulativeCount_strictMono_of_pos_general
        schedule.budget.batchSize schedule.budget.batchSize_pos).monotone
        (show generalScheduleGlobalBatch schedule
          (generalScheduleGlobalShotRank schedule shot) + 1 <= shot.1 by omega)
    unfold generalScheduleGlobalShotRank at hu hmono
    omega

@[simp] theorem generalScheduleGlobalWithin_globalShotRank
    (schedule : CumulativePauliPilotBatchSchedule)
    (shot : GeneralScheduleShotIndex schedule) :
    generalScheduleGlobalWithin schedule
      (generalScheduleGlobalShotRank schedule shot) = shot.2.val := by
  unfold generalScheduleGlobalWithin
  rw [generalScheduleGlobalBatch_globalShotRank]
  unfold generalScheduleGlobalShotRank
  omega

/-- The scheduled pilot blocks, indexed first by batch and then within batch. -/
abbrev GeneralSchedulePilotBlockIndex
    (schedule : CumulativePauliPilotBatchSchedule) : Type :=
  Sigma fun k : Nat => Fin (schedule.pilotBlocks k)

/-- A pilot block/Pauli coordinate as a valid shot in its batch. -/
def generalSchedulePilotShot
    (schedule : CumulativePauliPilotBatchSchedule)
    (block : GeneralSchedulePilotBlockIndex schedule) (axis : Fin 3) :
    GeneralScheduleShotIndex schedule := by
  refine ⟨block.1, ⟨3 * block.2.val + axis.val, ?_⟩⟩
  have hblock := block.2.isLt
  have haxis := axis.isLt
  have hexplore := schedule.explorationSize_eq_three_mul block.1
  have hle := schedule.budget.exploration_le_batch block.1
  omega

/-- Exact global trajectory rank of one scheduled Pauli pilot outcome. -/
def generalSchedulePilotShotRank
    (schedule : CumulativePauliPilotBatchSchedule)
    (block : GeneralSchedulePilotBlockIndex schedule) (axis : Fin 3) : Nat :=
  generalScheduleGlobalShotRank schedule
    (generalSchedulePilotShot schedule block axis)

@[simp] theorem generalSchedulePilotShotRank_batch
    (schedule : CumulativePauliPilotBatchSchedule)
    (block : GeneralSchedulePilotBlockIndex schedule) (axis : Fin 3) :
    generalScheduleGlobalBatch schedule
      (generalSchedulePilotShotRank schedule block axis) = block.1 := by
  exact generalScheduleGlobalBatch_globalShotRank schedule
    (generalSchedulePilotShot schedule block axis)

@[simp] theorem generalSchedulePilotShotRank_within
    (schedule : CumulativePauliPilotBatchSchedule)
    (block : GeneralSchedulePilotBlockIndex schedule) (axis : Fin 3) :
    generalScheduleGlobalWithin schedule
      (generalSchedulePilotShotRank schedule block axis) =
        3 * block.2.val + axis.val := by
  exact generalScheduleGlobalWithin_globalShotRank schedule
    (generalSchedulePilotShot schedule block axis)

end

end QubitOracle.Paper
