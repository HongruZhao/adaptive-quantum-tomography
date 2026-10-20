import QubitOracle.Paper.OneQubitGeneralScheduleTrajectoryIndexing

/-!
# Global enumeration of pilot blocks for arbitrary predetermined schedules

Pilot counts may vanish in individual batches.  The only asymptotic premise is
that their cumulative count tends to infinity.  This module constructs the
least containing batch for every global pilot-block rank and proves exact
decode/encode identities.
-/

namespace QubitOracle.Paper

open Filter
open PureMultilevelSequentialBatchAdaptive

noncomputable section

theorem CumulativePauliPilotBatchSchedule.exists_batch_for_pilot_rank
    (schedule : CumulativePauliPilotBatchSchedule) (r : Nat) :
    ∃ k, r < cumulativeCount schedule.pilotBlocks (k + 1) := by
  have hEventually :=
    (tendsto_atTop.1 schedule.cumulativePilotBlocks_tendsto_atTop) (r + 1)
  rcases eventually_atTop.1 hEventually with ⟨N, hN⟩
  have hAtN : r + 1 ≤ cumulativeCount schedule.pilotBlocks N :=
    hN N le_rfl
  have hNne : N ≠ 0 := by
    intro hzero
    subst N
    simp [cumulativeCount] at hAtN
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hNne
  have hStrict : r < cumulativeCount schedule.pilotBlocks k.succ := by
    omega
  exact ⟨k, by simpa [Nat.succ_eq_add_one] using hStrict⟩

/-- Least batch containing global pilot-block rank `r`. -/
def generalSchedulePilotBatchOfRank
    (schedule : CumulativePauliPilotBatchSchedule) (r : Nat) : Nat :=
  Nat.find (schedule.exists_batch_for_pilot_rank r)

theorem generalSchedulePilotBatchOfRank_upper
    (schedule : CumulativePauliPilotBatchSchedule) (r : Nat) :
    r < cumulativeCount schedule.pilotBlocks
      (generalSchedulePilotBatchOfRank schedule r + 1) := by
  exact Nat.find_spec (schedule.exists_batch_for_pilot_rank r)

theorem generalSchedulePilotBatchOfRank_lower
    (schedule : CumulativePauliPilotBatchSchedule) (r : Nat) :
    cumulativeCount schedule.pilotBlocks
      (generalSchedulePilotBatchOfRank schedule r) ≤ r := by
  let hExists := schedule.exists_batch_for_pilot_rank r
  change cumulativeCount schedule.pilotBlocks (Nat.find hExists) ≤ r
  cases hFind : Nat.find hExists with
  | zero => simp [cumulativeCount]
  | succ k =>
      by_contra hNot
      have hEarlier :
          r < cumulativeCount schedule.pilotBlocks (k + 1) :=
        Nat.lt_of_not_ge hNot
      have hMinimal := Nat.find_min hExists (show k < Nat.find hExists by omega)
      exact hMinimal hEarlier

/-- Within-batch pilot-block coordinate of global pilot rank `r`. -/
def generalSchedulePilotWithinOfRank
    (schedule : CumulativePauliPilotBatchSchedule) (r : Nat) : Nat :=
  r - cumulativeCount schedule.pilotBlocks
    (generalSchedulePilotBatchOfRank schedule r)

theorem generalSchedulePilotWithinOfRank_lt
    (schedule : CumulativePauliPilotBatchSchedule) (r : Nat) :
    generalSchedulePilotWithinOfRank schedule r <
      schedule.pilotBlocks (generalSchedulePilotBatchOfRank schedule r) := by
  have hLower := generalSchedulePilotBatchOfRank_lower schedule r
  have hUpper := generalSchedulePilotBatchOfRank_upper schedule r
  rw [cumulativeCount_succ_general] at hUpper
  unfold generalSchedulePilotWithinOfRank
  omega

/-- The concrete batch/within-batch pilot block of global rank `r`. -/
def generalSchedulePilotBlockOfRank
    (schedule : CumulativePauliPilotBatchSchedule) (r : Nat) :
    GeneralSchedulePilotBlockIndex schedule :=
  ⟨generalSchedulePilotBatchOfRank schedule r,
    ⟨generalSchedulePilotWithinOfRank schedule r,
      generalSchedulePilotWithinOfRank_lt schedule r⟩⟩

/-- Global rank of a concrete pilot block. -/
def generalSchedulePilotBlockRank
    (schedule : CumulativePauliPilotBatchSchedule)
    (block : GeneralSchedulePilotBlockIndex schedule) : Nat :=
  cumulativeCount schedule.pilotBlocks block.1 + block.2.1

/-- Decoding and then encoding a global pilot rank is exact. -/
theorem generalSchedulePilotBlockRank_blockOfRank
    (schedule : CumulativePauliPilotBatchSchedule) (r : Nat) :
    generalSchedulePilotBlockRank schedule
      (generalSchedulePilotBlockOfRank schedule r) = r := by
  unfold generalSchedulePilotBlockRank generalSchedulePilotBlockOfRank
  simp only
  exact Nat.add_sub_of_le
    (generalSchedulePilotBatchOfRank_lower schedule r)

/-- The decoded block has the expected batch coordinate. -/
@[simp] theorem generalSchedulePilotBlockOfRank_batch
    (schedule : CumulativePauliPilotBatchSchedule) (r : Nat) :
    (generalSchedulePilotBlockOfRank schedule r).1 =
      generalSchedulePilotBatchOfRank schedule r := by
  rfl

/-- The decoded block has the expected within-batch coordinate. -/
@[simp] theorem generalSchedulePilotBlockOfRank_within
    (schedule : CumulativePauliPilotBatchSchedule) (r : Nat) :
    (generalSchedulePilotBlockOfRank schedule r).2.1 =
      generalSchedulePilotWithinOfRank schedule r := by
  rfl

end

end QubitOracle.Paper
