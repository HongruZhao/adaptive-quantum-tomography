import QubitOracle.Paper.OneQubitGeneralSchedulePilotBlockEnumeration
import QubitOracle.Paper.OneQubitGeneralScheduleAdaptiveDesign

/-!
# Chronological ordering of globally enumerated pilot shots

The cumulative pilot count may be flat across batches containing no pilot
blocks.  Nevertheless, decoding global pilot-block ranks and then taking any
fixed Pauli coordinate gives a strictly increasing sequence of literal shot
ranks.  This module also proves that those shots are exploration shots and
select exactly the intended Cartesian Pauli axis.
-/

namespace QubitOracle.Paper

open PureMultilevelSequentialBatchAdaptive

noncomputable section

/-- Cumulative counts are monotone even when some increments vanish. -/
theorem cumulativeCount_monotone_general (count : Nat -> Nat) :
    Monotone (cumulativeCount count) := by
  intro k l hkl
  unfold cumulativeCount
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hkl)

/-- The least containing batch is monotone in the global pilot-block rank. -/
theorem generalSchedulePilotBatchOfRank_monotone
    (schedule : CumulativePauliPilotBatchSchedule) :
    Monotone (generalSchedulePilotBatchOfRank schedule) := by
  intro r s hrs
  by_contra hnot
  have hsr : s < r := by
    have hsUpper := generalSchedulePilotBatchOfRank_upper schedule s
    have hmono := cumulativeCount_monotone_general schedule.pilotBlocks
      (show generalSchedulePilotBatchOfRank schedule s + 1 <=
          generalSchedulePilotBatchOfRank schedule r by omega)
    have hrLower := generalSchedulePilotBatchOfRank_lower schedule r
    omega
  exact (Nat.not_lt_of_ge hrs) hsr

/-- Within one batch, later decoded pilot ranks have later within-batch
coordinates. -/
theorem generalSchedulePilotWithinOfRank_lt_of_same_batch
    (schedule : CumulativePauliPilotBatchSchedule) {r s : Nat}
    (hrs : r < s)
    (hbatch : generalSchedulePilotBatchOfRank schedule r =
      generalSchedulePilotBatchOfRank schedule s) :
    generalSchedulePilotWithinOfRank schedule r <
      generalSchedulePilotWithinOfRank schedule s := by
  unfold generalSchedulePilotWithinOfRank
  rw [hbatch]
  have hrLower := generalSchedulePilotBatchOfRank_lower schedule r
  rw [hbatch] at hrLower
  omega

/-- For any fixed Pauli coordinate, global pilot-block enumeration is in the
literal chronological order of the adaptive path. -/
theorem generalSchedulePilotShotRank_blockOfRank_strictMono
    (schedule : CumulativePauliPilotBatchSchedule) (j : Fin 3) :
    StrictMono (fun r => generalSchedulePilotShotRank schedule
      (generalSchedulePilotBlockOfRank schedule r) j) := by
  intro r s hrs
  have hbatch := generalSchedulePilotBatchOfRank_monotone schedule hrs.le
  rcases hbatch.eq_or_lt with hsame | hlt
  · have hwithin := generalSchedulePilotWithinOfRank_lt_of_same_batch
      schedule hrs hsame
    unfold generalSchedulePilotShotRank generalScheduleGlobalShotRank
      generalSchedulePilotShot
    dsimp
    simp only [generalSchedulePilotBlockOfRank_batch,
      generalSchedulePilotBlockOfRank_within]
    rw [hsame]
    omega
  · have hbefore := generalSchedulePilotShotRank_lt_batchStart schedule hlt
      (generalSchedulePilotBlockOfRank schedule r).2 j
    unfold generalSchedulePilotShotRank generalScheduleGlobalShotRank
      generalSchedulePilotShot at hbefore ⊢
    dsimp at hbefore ⊢
    simp only [generalSchedulePilotBlockOfRank_batch,
      generalSchedulePilotBlockOfRank_within] at hbefore ⊢
    exact hbefore.trans_le (Nat.le_add_right _ _)

/-- Every pilot shot after the first decoded block has positive global rank. -/
theorem generalSchedulePilotShotRank_blockOfRank_succ_pos
    (schedule : CumulativePauliPilotBatchSchedule) (r : Nat) (j : Fin 3) :
    0 < generalSchedulePilotShotRank schedule
      (generalSchedulePilotBlockOfRank schedule (r + 1)) j := by
  exact (Nat.zero_le _).trans_lt
    (generalSchedulePilotShotRank_blockOfRank_strictMono schedule j
      (Nat.lt_succ_self r))

/-- Every scheduled pilot coordinate lies in the exploration prefix of its
batch. -/
theorem generalSchedulePilotShot_isExploration
    (schedule : CumulativePauliPilotBatchSchedule)
    (block : GeneralSchedulePilotBlockIndex schedule) (j : Fin 3) :
    generalScheduleIsExplorationShot schedule
      (generalSchedulePilotShotRank schedule block j) := by
  unfold generalScheduleIsExplorationShot
  rw [generalSchedulePilotShotRank_batch,
    generalSchedulePilotShotRank_within,
    schedule.explorationSize_eq_three_mul]
  have hblock := block.2.isLt
  have hj := j.isLt
  omega

/-- The three-cycle slot decoded at a pilot shot is its intended Pauli
coordinate. -/
theorem generalScheduleGlobalAxisSlot_pilotShot
    (schedule : CumulativePauliPilotBatchSchedule)
    (block : GeneralSchedulePilotBlockIndex schedule) (j : Fin 3) :
    generalScheduleGlobalAxisSlot schedule
      (generalSchedulePilotShotRank schedule block j) = j := by
  apply Fin.ext
  unfold generalScheduleGlobalAxisSlot
  simp only [generalSchedulePilotShotRank_within]
  omega

/-- On a scheduled pilot shot, the concrete history-dependent design selects
exactly the corresponding Cartesian Pauli axis, independently of history. -/
theorem generalScheduleHistoryAxis_pilotShot
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 -> Real)
    (block : GeneralSchedulePilotBlockIndex schedule) (j : Fin 3)
    (history : AdaptiveTrajectory BinaryOutcome) :
    generalScheduleHistoryAxis schedule b
      (generalSchedulePilotShotRank schedule block j) history =
        qubitPauliCoordinateAxis j := by
  rw [generalScheduleHistoryAxis_exploration schedule b _ history
    (generalSchedulePilotShot_isExploration schedule block j)]
  rw [generalScheduleGlobalAxisSlot_pilotShot]

end

end QubitOracle.Paper
