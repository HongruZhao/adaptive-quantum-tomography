import QubitOracle.Paper.OneQubitExactConcretePredeterminedBatchProtocol

/-!
# Exact cumulative schedule for the prespecified mixed-qubit batches

The finite protocol fixes the exploration and exploitation sizes before data
are observed.  This file records the cumulative exploitation count and proves
that it is exactly the total count minus the exploration count.  These are
deterministic schedule facts; no statistical or LAN premise occurs here.
-/

open Filter
open scoped BigOperators Topology

namespace QubitOracle.Paper

noncomputable section

open PureMultilevelSequentialBatchAdaptive

/-- Number of adaptive final-stage observations in batch `k`. -/
def exactConcreteBatchExploitationSize (k : Nat) : Nat :=
  3 * exactConcreteBatchFinalBlocks k

/-- Number of adaptive final-stage observations through the first `K`
prespecified batches. -/
def exactConcreteCumulativeExploitation (K : Nat) : Nat :=
  cumulativeCount exactConcreteBatchExploitationSize K

theorem exactConcreteBatchSize_eq_exploration_add_exploitation (k : Nat) :
    exactConcreteBatchSize k =
      exactConcreteBatchExplorationSize k +
        exactConcreteBatchExploitationSize k := by
  exact exactConcreteBatchSize_decompose k

theorem exactConcreteBatchExploitationSize_pos (k : Nat) :
    0 < exactConcreteBatchExploitationSize k := by
  unfold exactConcreteBatchExploitationSize
  exact Nat.mul_pos (by norm_num) (exactConcreteBatchFinalBlocks_pos k)

theorem exactConcreteCumulative_decomposition (K : Nat) :
    cumulativeCount exactConcreteBatchSize K =
      cumulativeCount exactConcreteBatchExplorationSize K +
        exactConcreteCumulativeExploitation K := by
  change (∑ k ∈ Finset.range K, exactConcreteBatchSize k) =
    (∑ k ∈ Finset.range K, exactConcreteBatchExplorationSize k) +
      ∑ k ∈ Finset.range K, exactConcreteBatchExploitationSize k
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  exact exactConcreteBatchSize_eq_exploration_add_exploitation k

/-- Exact cumulative final-stage count:
`N_K-Q_K=(3K)^6-(3K)^4`. -/
theorem exactConcreteCumulativeExploitation_eq (K : Nat) :
    exactConcreteCumulativeExploitation K =
      (3 * K) ^ 6 - (3 * K) ^ 4 := by
  have hdecomp := exactConcreteCumulative_decomposition K
  rw [exactConcreteBatchSize_cumulative,
    exactConcreteBatchExploration_cumulative] at hdecomp
  omega

theorem index_le_exactConcreteCumulativeExploitation (K : Nat) :
    K <= exactConcreteCumulativeExploitation K := by
  unfold exactConcreteCumulativeExploitation cumulativeCount
  calc
    K = ∑ _k ∈ Finset.range K, 1 := by simp
    _ <= ∑ k ∈ Finset.range K, exactConcreteBatchExploitationSize k := by
      apply Finset.sum_le_sum
      intro k _hk
      exact exactConcreteBatchExploitationSize_pos k

/-- The cumulative exploitation horizon diverges. -/
theorem exactConcreteCumulativeExploitation_tendsto_atTop :
    Tendsto exactConcreteCumulativeExploitation atTop atTop := by
  apply tendsto_atTop.2
  intro M
  filter_upwards [eventually_ge_atTop M] with K hK
  exact hK.trans (index_le_exactConcreteCumulativeExploitation K)

/-- The exploitation count is asymptotically the entire observation count. -/
theorem exactConcreteCumulativeExploitationFraction_tendsto_one :
    Tendsto
      (fun K =>
        (exactConcreteCumulativeExploitation K : Real) /
          (cumulativeCount exactConcreteBatchSize K : Real))
      atTop (nhds 1) := by
  have hzero := exactConcreteBatch_explorationFraction_tendsto_zero
  have hid :
      (fun K =>
        (exactConcreteCumulativeExploitation K : Real) /
          (cumulativeCount exactConcreteBatchSize K : Real)) =ᶠ[atTop]
      (fun K =>
        1 -
          (cumulativeCount exactConcreteBatchSize K : Real)⁻¹ *
            (cumulativeCount exactConcreteBatchExplorationSize K : Real)) := by
    filter_upwards [eventually_ge_atTop (1 : Nat)] with K hK
    have htotalNat : 0 < cumulativeCount exactConcreteBatchSize K := by
      rw [exactConcreteBatchSize_cumulative]
      positivity
    have htotal :
        (cumulativeCount exactConcreteBatchSize K : Real) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt htotalNat)
    have hdecompNat := exactConcreteCumulative_decomposition K
    have hdecompReal :
        (cumulativeCount exactConcreteBatchSize K : Real) =
          (cumulativeCount exactConcreteBatchExplorationSize K : Real) +
            (exactConcreteCumulativeExploitation K : Real) := by
      exact_mod_cast hdecompNat
    rw [show (exactConcreteCumulativeExploitation K : Real) =
        (cumulativeCount exactConcreteBatchSize K : Real) -
          (cumulativeCount exactConcreteBatchExplorationSize K : Real) by
        linarith [hdecompReal]]
    field_simp [htotal]
  have hone : Tendsto (fun _ : Nat => (1 : Real)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hsub : Tendsto
      (fun K =>
        1 -
          (cumulativeCount exactConcreteBatchSize K : Real)⁻¹ *
            (cumulativeCount exactConcreteBatchExplorationSize K : Real))
      atTop (nhds 1) := by
    simpa using hone.sub hzero
  exact hsub.congr' hid.symm

/-- The exploration contribution is negligible on the square-root total
sample scale in precisely the deterministic form used by the pilot remainder. -/
theorem exactConcreteBatch_quarterRateExploration_closed :
    Tendsto
      (fun K =>
        Real.sqrt (cumulativeCount exactConcreteBatchSize K : Real) *
            Real.log
              ((cumulativeCount exactConcreteBatchSize K : Real) + 2) /
          (cumulativeCount exactConcreteBatchExplorationSize K : Real))
      atTop (nhds 0) :=
  exactConcreteBatch_quarterRateExploration

/-- One bundled schedule endpoint used by the cumulative LAN construction. -/
theorem exactConcretePrespecifiedBatch_cumulativeSchedule_closed :
    (forall K,
      exactConcreteCumulativeExploitation K =
        (3 * K) ^ 6 - (3 * K) ^ 4) /\
    Tendsto exactConcreteCumulativeExploitation atTop atTop /\
    Tendsto
      (fun K =>
        (exactConcreteCumulativeExploitation K : Real) /
          (cumulativeCount exactConcreteBatchSize K : Real))
      atTop (nhds 1) := by
  exact ⟨exactConcreteCumulativeExploitation_eq,
    exactConcreteCumulativeExploitation_tendsto_atTop,
    exactConcreteCumulativeExploitationFraction_tendsto_one⟩

end

end QubitOracle.Paper
