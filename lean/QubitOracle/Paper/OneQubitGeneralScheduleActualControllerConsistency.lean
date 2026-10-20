import QubitOracle.Paper.OneQubitGeneralSchedulePilotAverageStrongLaw

/-!
# Consistency of the implemented controller on the literal adaptive path

This module identifies the history sum used at every batch boundary with the
chronologically enumerated pilot sum on the same Ionescu--Tulcea path.  Empty
pilot batches are allowed.  The compressed pilot strong law therefore gives
almost-sure consistency of the controller that the protocol actually uses.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory
open scoped BigOperators Topology
open PureMultilevelSequentialBatchAdaptive

noncomputable section

/-- A pilot rank formed from the cumulative count before batch `k` and a
valid within-batch coordinate decodes back to batch `k`, including across
arbitrarily long runs of empty pilot batches. -/
theorem generalSchedulePilotBatchOfRank_cumulative_add
    (schedule : CumulativePauliPilotBatchSchedule) (k : Nat)
    (q : Fin (schedule.pilotBlocks k)) :
    generalSchedulePilotBatchOfRank schedule
        (cumulativeCount schedule.pilotBlocks k + q.1) = k := by
  apply Nat.le_antisymm
  · let hExists := schedule.exists_batch_for_pilot_rank
      (cumulativeCount schedule.pilotBlocks k + q.1)
    change Nat.find hExists <= k
    apply Nat.find_min'
    rw [cumulativeCount_succ_general]
    exact Nat.add_lt_add_left q.2 _
  · by_contra hnot
    have hbatch : generalSchedulePilotBatchOfRank schedule
        (cumulativeCount schedule.pilotBlocks k + q.1) < k := by omega
    have hupper := generalSchedulePilotBatchOfRank_upper schedule
      (cumulativeCount schedule.pilotBlocks k + q.1)
    have hmono := cumulativeCount_monotone_general schedule.pilotBlocks
      (show generalSchedulePilotBatchOfRank schedule
        (cumulativeCount schedule.pilotBlocks k + q.1) + 1 <= k by omega)
    omega

/-- The corresponding decoded within-batch coordinate is exactly `q`. -/
theorem generalSchedulePilotWithinOfRank_cumulative_add
    (schedule : CumulativePauliPilotBatchSchedule) (k : Nat)
    (q : Fin (schedule.pilotBlocks k)) :
    generalSchedulePilotWithinOfRank schedule
        (cumulativeCount schedule.pilotBlocks k + q.1) = q.1 := by
  unfold generalSchedulePilotWithinOfRank
  rw [generalSchedulePilotBatchOfRank_cumulative_add schedule k q]
  exact Nat.add_sub_cancel_left _ q.1

/-- The global chronological shot at the encoded pilot rank is literally the
shot indexed by `(k,q,j)` in the scheduled pilot block. -/
theorem generalSchedulePilotShotTime_cumulative_add
    (schedule : CumulativePauliPilotBatchSchedule) (k : Nat)
    (q : Fin (schedule.pilotBlocks k)) (j : Fin 3) :
    generalSchedulePilotShotTime schedule j
        (cumulativeCount schedule.pilotBlocks k + q.1) =
      generalSchedulePilotShotRank schedule ⟨k, q⟩ j := by
  unfold generalSchedulePilotShotTime generalSchedulePilotShotRank
    generalScheduleGlobalShotRank generalSchedulePilotShot
  dsimp
  simp only [generalSchedulePilotBlockOfRank_batch,
    generalSchedulePilotBlockOfRank_within]
  rw [generalSchedulePilotBatchOfRank_cumulative_add schedule k q,
    generalSchedulePilotWithinOfRank_cumulative_add schedule k q]

/-- A valid coordinate of an actual finite prefix is exactly the same
coordinate of the underlying infinite path. -/
theorem generalScheduleHistoryOutcomeAt_adaptiveInfinitePathPrefix
    (path : AdaptiveInfinitePath BinaryOutcome) {n t : Nat} (ht : t < n) :
    generalScheduleHistoryOutcomeAt
        (adaptiveInfinitePathPrefix n path) t = path t := by
  cases n with
  | zero => omega
  | succ n =>
      cases t with
      | zero =>
          simp [generalScheduleHistoryOutcomeAt, adaptiveInfinitePathPrefix,
            iicToAdaptiveTrajectory]
      | succ t =>
          have ht' : t < n := by omega
          simp [generalScheduleHistoryOutcomeAt, adaptiveInfinitePathPrefix,
            iicToAdaptiveTrajectory, ht']

/-- Chronological sum of the first `N` signed pilot outcomes in coordinate
`j` on the literal adaptive path. -/
def generalSchedulePilotSignedSum
    (schedule : CumulativePauliPilotBatchSchedule)
    (path : AdaptiveInfinitePath BinaryOutcome) (j : Fin 3) (N : Nat) : Real :=
  ∑ r ∈ Finset.range N,
    (path (generalSchedulePilotShotTime schedule j r)).sign

/-- The same sum grouped by completed prescribed batches. -/
def generalSchedulePilotPathCoordinateSum
    (schedule : CumulativePauliPilotBatchSchedule) (k : Nat)
    (path : AdaptiveInfinitePath BinaryOutcome) (j : Fin 3) : Real :=
  ∑ r ∈ Finset.range k,
    ∑ q : Fin (schedule.pilotBlocks r),
      (path (generalSchedulePilotShotRank schedule ⟨r, q⟩ j)).sign

/-- Every lookup made by the implemented batch-start controller lies in its
literal finite prefix, so its grouped sum equals the grouped path sum. -/
theorem generalScheduleHistoryPilotCoordinateSum_batchStart_eq_pathSum
    (schedule : CumulativePauliPilotBatchSchedule) (k : Nat)
    (path : AdaptiveInfinitePath BinaryOutcome) (j : Fin 3) :
    generalScheduleHistoryPilotCoordinateSum schedule k
        (adaptiveInfinitePathPrefix
          (cumulativeCount schedule.budget.batchSize k) path) j =
      generalSchedulePilotPathCoordinateSum schedule k path j := by
  unfold generalScheduleHistoryPilotCoordinateSum
    generalSchedulePilotPathCoordinateSum
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro q hq
  rw [generalScheduleHistoryOutcomeAt_adaptiveInfinitePathPrefix path
    (generalSchedulePilotShotRank_lt_batchStart schedule
      (Finset.mem_range.mp hr) q j)]

/-- Grouping pilot observations by batches does not change their exact
chronological sum. -/
theorem generalSchedulePilotPathCoordinateSum_eq_signedSum
    (schedule : CumulativePauliPilotBatchSchedule) (k : Nat)
    (path : AdaptiveInfinitePath BinaryOutcome) (j : Fin 3) :
    generalSchedulePilotPathCoordinateSum schedule k path j =
      generalSchedulePilotSignedSum schedule path j
        (cumulativeCount schedule.pilotBlocks k) := by
  induction k with
  | zero =>
      simp [generalSchedulePilotPathCoordinateSum,
        generalSchedulePilotSignedSum, cumulativeCount]
  | succ k ih =>
      rw [generalSchedulePilotPathCoordinateSum]
      rw [Finset.sum_range_succ]
      change generalSchedulePilotPathCoordinateSum schedule k path j + _ = _
      rw [ih, cumulativeCount_succ_general]
      unfold generalSchedulePilotSignedSum
      rw [Finset.sum_range_add]
      congr 1
      calc
        (∑ q : Fin (schedule.pilotBlocks k),
            (path (generalSchedulePilotShotRank schedule ⟨k, q⟩ j)).sign) =
            ∑ q : Fin (schedule.pilotBlocks k),
              (path (generalSchedulePilotShotTime schedule j
                (cumulativeCount schedule.pilotBlocks k + q.1))).sign := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [generalSchedulePilotShotTime_cumulative_add schedule k q j]
        _ = ∑ q ∈ Finset.range (schedule.pilotBlocks k),
              (path (generalSchedulePilotShotTime schedule j
                (cumulativeCount schedule.pilotBlocks k + q))).sign := by
          let f : Nat -> Real := fun q =>
            (path (generalSchedulePilotShotTime schedule j
              (cumulativeCount schedule.pilotBlocks k + q))).sign
          change (∑ q : Fin (schedule.pilotBlocks k), f q.1) =
            ∑ q ∈ Finset.range (schedule.pilotBlocks k), f q
          exact Fin.sum_univ_eq_sum_range f (schedule.pilotBlocks k)

/-- Exact bridge from the controller's finite history to the chronological
pilot sum on the same path. -/
theorem generalScheduleHistoryPilotCoordinateSum_batchStart_eq_signedSum
    (schedule : CumulativePauliPilotBatchSchedule) (k : Nat)
    (path : AdaptiveInfinitePath BinaryOutcome) (j : Fin 3) :
    generalScheduleHistoryPilotCoordinateSum schedule k
        (adaptiveInfinitePathPrefix
          (cumulativeCount schedule.budget.batchSize k) path) j =
      generalSchedulePilotSignedSum schedule path j
        (schedule.pastPilotBlockCount k) := by
  rw [generalScheduleHistoryPilotCoordinateSum_batchStart_eq_pathSum]
  exact generalSchedulePilotPathCoordinateSum_eq_signedSum
    schedule k path j

/-- The controller used at the start of batch `k`, evaluated on the actual
prefix of one infinite adaptive trajectory. -/
def generalScheduleActualBatchStartController
    (schedule : CumulativePauliPilotBatchSchedule) (k : Nat)
    (path : AdaptiveInfinitePath BinaryOutcome) : Fin 3 -> Real :=
  generalScheduleHistoryController schedule k
    (adaptiveInfinitePathPrefix
      (cumulativeCount schedule.budget.batchSize k) path)

/-- Centering the chronological signed pilot sum gives exactly the sum of the
previously verified pilot martingale differences. -/
theorem generalSchedulePilotSignedSum_sub_truth_eq_noiseSum
    (schedule : CumulativePauliPilotBatchSchedule)
    (theta : OneQubitPhysicalParameter)
    (path : AdaptiveInfinitePath BinaryOutcome) (j : Fin 3) (N : Nat) :
    generalSchedulePilotSignedSum schedule path j N -
        (N : Real) * theta.1 j =
      ∑ r ∈ Finset.range N,
        generalSchedulePilotNoise schedule theta r j path := by
  simp [generalSchedulePilotSignedSum, generalSchedulePilotNoise,
    generalSchedulePilotShotTime, Finset.sum_sub_distrib]

/-- Whenever at least one past pilot block exists, the implemented
controller error is exactly the ordinary pilot-noise average. -/
theorem generalScheduleActualBatchStartController_sub_truth_eq_noiseAverage
    (schedule : CumulativePauliPilotBatchSchedule)
    (theta : OneQubitPhysicalParameter) (k : Nat)
    (path : AdaptiveInfinitePath BinaryOutcome) (j : Fin 3)
    (hk : 0 < schedule.pastPilotBlockCount k) :
    generalScheduleActualBatchStartController schedule k path j - theta.1 j =
      generalSchedulePilotNoiseAverage schedule theta j path
        (schedule.pastPilotBlockCount k) := by
  rw [generalScheduleActualBatchStartController,
    generalScheduleHistoryController_positive schedule k _ hk j,
    generalScheduleHistoryPilotCoordinateSum_batchStart_eq_signedSum]
  unfold generalSchedulePilotNoiseAverage
  rw [← generalSchedulePilotSignedSum_sub_truth_eq_noiseSum]
  have hN : (schedule.pastPilotBlockCount k : Real) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hk
  field_simp [hN] <;> ring

/-- The concrete history-only controller used by the arbitrary predetermined
batch protocol is almost surely coordinatewise consistent on its own literal
adaptive Born trajectory. -/
theorem generalScheduleActualBatchStartController_tendsto_ae
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 -> Real)
    (theta : OneQubitPhysicalParameter)
    (hInterior : QubitOracle.blochNormSq theta.1 < 1) :
    ∀ᵐ path ∂generalScheduleAdaptiveBornPathMeasure schedule b theta,
      ∀ j : Fin 3,
        Tendsto
          (fun k => generalScheduleActualBatchStartController
            schedule k path j)
          atTop (nhds (theta.1 j)) := by
  have hall :
      ∀ᵐ path ∂generalScheduleAdaptiveBornPathMeasure schedule b theta,
        ∀ j : Fin 3,
          Tendsto
            (generalSchedulePilotNoiseAverage schedule theta j path)
            atTop (nhds 0) := by
    exact ae_all_iff.2 fun j =>
      generalSchedulePilotNoiseAverage_ae_tendsto_zero
        schedule b theta hInterior j
  filter_upwards [hall] with path hpath
  intro j
  have hsubsequence :=
    (hpath j).comp schedule.cumulativePilotBlocks_tendsto_atTop
  have heq :
      (fun k => generalScheduleActualBatchStartController
        schedule k path j - theta.1 j) =ᶠ[atTop]
      (fun k => generalSchedulePilotNoiseAverage schedule theta j path
        (schedule.pastPilotBlockCount k)) := by
    filter_upwards [schedule.pastPilotBlockCount_eventually_pos] with k hk
    exact generalScheduleActualBatchStartController_sub_truth_eq_noiseAverage
      schedule theta k path j hk
  have hcentered : Tendsto
      (fun k => generalScheduleActualBatchStartController
        schedule k path j - theta.1 j)
      atTop (nhds 0) := by
    exact hsubsequence.congr' heq.symm
  have htranslated := hcentered.add
    (tendsto_const_nhds : Tendsto (fun _ : Nat => theta.1 j)
      atTop (nhds (theta.1 j)))
  simpa using htranslated

end

end QubitOracle.Paper
