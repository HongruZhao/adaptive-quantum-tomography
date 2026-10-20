import QubitOracle.Paper.OneQubitPredeterminedBatchHeadline
import QubitOracle.Paper.OneQubitPauliPilotConsistency
import QubitOracle.Paper.OneQubitMixedTwoStageFinalEstimatorLaw
import QubitOracle.Paper.MathlibHoeffding1963Bridge

/-!
# Exact concrete predetermined-batch qubit protocol

This module fixes one completely explicit batch schedule.  At completed batch
`K`, the cumulative number of global exploration labels is `(3*K)^4` and the
cumulative number of observations is `(3*K)^6`.  Consequently the latter is
exactly the requested three-halves exploration position of the former.

Every batch contains a positive integer number of complete cyclic-Pauli pilot
blocks.  Its exploitation part is a positive integer number of complete
three-axis cycles in the total, truth-independent frame selected from that
batch's pilot.  The finite pilot/final Born law is therefore the literal law
already constructed in `OneQubitMixedTwoStageFinalEstimatorLaw`.

The pilot controller is the actual three-Pauli sample-mean estimator.  Its
convergence in probability follows from the Mathlib Hoeffding bridge after
composition with the explicit diverging batch-pilot index.  No protocol-level
or convergence axiom is introduced here.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
open OneQubitPredeterminedBatchHeadline
open PureMultilevelSequentialBatchAdaptive

noncomputable section

/-! ## Explicit polynomial batches -/

/-- Complete cyclic-Pauli pilot blocks in batch `k`. -/
def exactConcreteBatchPilotBlocks (k : Nat) : Nat :=
  27 * (4 * k ^ 3 + 6 * k ^ 2 + 4 * k + 1)

/-- Exploration observations in batch `k`: three observations per block. -/
def exactConcreteBatchExplorationSize (k : Nat) : Nat :=
  3 * exactConcreteBatchPilotBlocks k

/-- Complete equal-allocation exploitation cycles in batch `k`. -/
def exactConcreteBatchFinalBlocks (k : Nat) : Nat :=
  1458 * k ^ 5 + 3645 * k ^ 4 + 4752 * k ^ 3 +
    3483 * k ^ 2 + 1350 * k + 216

/-- Total observations in batch `k`. -/
def exactConcreteBatchSize (k : Nat) : Nat :=
  729 * (6 * k ^ 5 + 15 * k ^ 4 + 20 * k ^ 3 +
    15 * k ^ 2 + 6 * k + 1)

theorem exactConcreteBatchSize_decompose (k : Nat) :
    exactConcreteBatchSize k =
      exactConcreteBatchExplorationSize k +
        3 * exactConcreteBatchFinalBlocks k := by
  unfold exactConcreteBatchSize exactConcreteBatchExplorationSize
    exactConcreteBatchPilotBlocks exactConcreteBatchFinalBlocks
  ring

theorem exactConcreteBatchPilotBlocks_pos (k : Nat) :
    0 < exactConcreteBatchPilotBlocks k := by
  unfold exactConcreteBatchPilotBlocks
  positivity

theorem exactConcreteBatchExplorationSize_pos (k : Nat) :
    0 < exactConcreteBatchExplorationSize k := by
  unfold exactConcreteBatchExplorationSize
  positivity [exactConcreteBatchPilotBlocks_pos k]

theorem exactConcreteBatchFinalBlocks_pos (k : Nat) :
    0 < exactConcreteBatchFinalBlocks k := by
  unfold exactConcreteBatchFinalBlocks
  omega

theorem exactConcreteBatchSize_pos (k : Nat) :
    0 < exactConcreteBatchSize k := by
  have hpilot := exactConcreteBatchExplorationSize_pos k
  rw [exactConcreteBatchSize_decompose]
  omega

theorem exactConcreteBatchExplorationSize_le (k : Nat) :
    exactConcreteBatchExplorationSize k <= exactConcreteBatchSize k := by
  rw [exactConcreteBatchSize_decompose]
  omega

/-- The cumulative exploration count is exactly `(3*K)^4`. -/
theorem exactConcreteBatchExploration_cumulative (K : Nat) :
    cumulativeCount exactConcreteBatchExplorationSize K = (3 * K) ^ 4 := by
  induction K with
  | zero => simp [cumulativeCount]
  | succ K ih =>
      rw [cumulativeCount, Finset.sum_range_succ]
      change cumulativeCount exactConcreteBatchExplorationSize K +
          exactConcreteBatchExplorationSize K = _
      rw [ih]
      unfold exactConcreteBatchExplorationSize exactConcreteBatchPilotBlocks
      ring

/-- The cumulative observation count is exactly `(3*K)^6`. -/
theorem exactConcreteBatchSize_cumulative (K : Nat) :
    cumulativeCount exactConcreteBatchSize K = (3 * K) ^ 6 := by
  induction K with
  | zero => simp [cumulativeCount]
  | succ K ih =>
      rw [cumulativeCount, Finset.sum_range_succ]
      change cumulativeCount exactConcreteBatchSize K +
          exactConcreteBatchSize K = _
      rw [ih]
      unfold exactConcreteBatchSize
      ring

/-! ## Exact three-halves global locations -/

private theorem threeHalvesRealPosition_succ_gap (n : Nat) :
    (n : Real) * Real.sqrt (n : Real) + 1 <=
      (n + 1 : Nat) * Real.sqrt (n + 1 : Nat) := by
  cases n with
  | zero => norm_num
  | succ n =>
      have hone : (1 : Real) <= Real.sqrt (Nat.succ n : Real) := by
        rw [Real.one_le_sqrt]
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      have hsqrt : Real.sqrt (Nat.succ n : Real) <=
          Real.sqrt (Nat.succ n + 1 : Nat) := by
        exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ (Nat.succ n))
      calc
        (Nat.succ n : Real) * Real.sqrt (Nat.succ n : Real) + 1 <=
            (Nat.succ n : Real) * Real.sqrt (Nat.succ n : Real) +
              Real.sqrt (Nat.succ n : Real) := by nlinarith
        _ = ((Nat.succ n : Real) + 1) * Real.sqrt (Nat.succ n : Real) := by
          ring
        _ <= ((Nat.succ n : Real) + 1) *
            Real.sqrt (Nat.succ n + 1 : Nat) :=
          mul_le_mul_of_nonneg_left hsqrt (by positivity)
        _ = (Nat.succ n + 1 : Nat) *
            Real.sqrt (Nat.succ n + 1 : Nat) := by norm_num

/-- The ceiling schedule `ell |-> ceil(ell*sqrt ell)` is strictly increasing. -/
theorem threeHalvesExplorationPosition_strictMono :
    StrictMono threeHalvesExplorationPosition := by
  apply strictMono_nat_of_lt_succ
  intro n
  apply Nat.add_one_le_iff.mp
  unfold threeHalvesExplorationPosition
  rw [Nat.add_one_le_ceil_iff]
  exact (Nat.ceil_lt_add_one
      (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))).trans_le
    (threeHalvesRealPosition_succ_gap n)

theorem index_le_threeHalvesExplorationPosition (n : Nat) :
    n <= threeHalvesExplorationPosition n := by
  induction n with
  | zero => simp [threeHalvesExplorationPosition]
  | succ n ih =>
      have hstep := threeHalvesExplorationPosition_strictMono
        (Nat.lt_succ_self n)
      change threeHalvesExplorationPosition n <
        threeHalvesExplorationPosition n.succ at hstep
      exact (Nat.succ_le_succ ih).trans hstep

/-- At a fourth power, the three-halves location is the corresponding sixth
power, with no asymptotic rounding error. -/
theorem threeHalvesExplorationPosition_fourthPower (x : Nat) :
    threeHalvesExplorationPosition (x ^ 4) = x ^ 6 := by
  have hsqrt : Real.sqrt ((x ^ 4 : Nat) : Real) = (x : Real) ^ 2 := by
    rw [Nat.cast_pow]
    have hpow : (x : Real) ^ 4 = ((x : Real) ^ 2) ^ 2 := by ring
    rw [hpow, Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg _)]
  unfold threeHalvesExplorationPosition
  rw [hsqrt]
  have hcast : (((x ^ 4 : Nat) : Real) * (x : Real) ^ 2) =
      ((x ^ 6 : Nat) : Real) := by
    push_cast
    ring
  rw [hcast, Nat.ceil_natCast]

/-- Strict monotonicity identifies the number of exploration labels before
the `L`-th exploration position exactly. -/
theorem threeHalvesExplorationCountBefore_at_position (L : Nat) :
    threeHalvesExplorationCountBefore
      (threeHalvesExplorationPosition L) = L := by
  unfold threeHalvesExplorationCountBefore
  have hset :
      (Finset.range (threeHalvesExplorationPosition L)).filter
          (fun ell => threeHalvesExplorationPosition ell <
            threeHalvesExplorationPosition L) =
        Finset.range L := by
    ext ell
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨_, hpos⟩
      exact threeHalvesExplorationPosition_strictMono.lt_iff_lt.mp hpos
    · intro hell
      exact ⟨lt_of_lt_of_le hell (index_le_threeHalvesExplorationPosition L),
        threeHalvesExplorationPosition_strictMono hell⟩
  rw [hset, Finset.card_range]

theorem exactConcreteBatch_exactThreeHalvesCount (K : Nat) :
    cumulativeCount exactConcreteBatchExplorationSize K =
      threeHalvesExplorationCountBefore
        (cumulativeCount exactConcreteBatchSize K) := by
  rw [exactConcreteBatchExploration_cumulative,
    exactConcreteBatchSize_cumulative]
  calc
    (3 * K) ^ 4 =
        threeHalvesExplorationCountBefore
          (threeHalvesExplorationPosition ((3 * K) ^ 4)) :=
      (threeHalvesExplorationCountBefore_at_position ((3 * K) ^ 4)).symm
    _ = threeHalvesExplorationCountBefore ((3 * K) ^ 6) := by
      rw [threeHalvesExplorationPosition_fourthPower]

/-! ## Scalar asymptotics for the budget -/

private theorem natCastSquare_tendsto_atTop :
    Tendsto (fun K : Nat => (K : Real) ^ 2) atTop atTop := by
  have h := (tendsto_natCast_atTop_atTop :
    Tendsto (fun K : Nat => (K : Real)) atTop atTop)
  simpa [pow_two] using h.atTop_mul_atTop₀ h

private theorem natCastCube_tendsto_atTop :
    Tendsto (fun K : Nat => (K : Real) ^ 3) atTop atTop := by
  have h := (tendsto_natCast_atTop_atTop :
    Tendsto (fun K : Nat => (K : Real)) atTop atTop)
  have h2 : Tendsto (fun K : Nat => (K : Real) * (K : Real)) atTop atTop :=
    h.atTop_mul_atTop₀ h
  simpa [pow_succ] using h2.atTop_mul_atTop₀ h

private theorem natCastSixth_tendsto_atTop :
    Tendsto (fun K : Nat => (K : Real) ^ 6) atTop atTop := by
  have h3 := natCastCube_tendsto_atTop
  convert h3.atTop_mul_atTop₀ h3 using 1 <;> ring

theorem exactConcreteBatch_totalSamples_tendsto_atTop :
    Tendsto
      (fun K => (cumulativeCount exactConcreteBatchSize K : Real))
      atTop atTop := by
  simpa [exactConcreteBatchSize_cumulative, Nat.cast_pow, mul_pow] using
    natCastSixth_tendsto_atTop.const_mul_atTop
      (by norm_num : (0 : Real) < 729)

theorem exactConcreteBatch_explorationFraction_tendsto_zero :
    Tendsto
      (fun K =>
        (cumulativeCount exactConcreteBatchSize K : Real)⁻¹ *
          (cumulativeCount exactConcreteBatchExplorationSize K : Real))
      atTop (nhds 0) := by
  have hinv : Tendsto (fun K : Nat => ((K : Real) ^ 2)⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp natCastSquare_tendsto_atTop
  have hmain : Tendsto (fun K : Nat => (1 / 9 : Real) * ((K : Real) ^ 2)⁻¹)
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hinv
  apply hmain.congr'
  filter_upwards [eventually_gt_atTop (0 : Nat)] with K hK
  rw [exactConcreteBatchSize_cumulative,
    exactConcreteBatchExploration_cumulative]
  push_cast
  field_simp [show (K : Real) ≠ 0 by exact_mod_cast Nat.ne_of_gt hK]
  ring

theorem exactConcreteBatchSize_monotone : Monotone exactConcreteBatchSize := by
  intro a b hab
  unfold exactConcreteBatchSize
  gcongr

private theorem exactConcreteBatchSize_le_lastScale
    (k K : Nat) (hk : k < K) :
    exactConcreteBatchSize k <= 45927 * K ^ 5 := by
  have hK : 1 <= K := by omega
  have hbase : k <= K := hk.le
  have hp1 : k <= K ^ 5 := by
    have hpow : K ^ 1 <= K ^ 5 := pow_le_pow_right' hK (by omega)
    exact hbase.trans (by simpa using hpow)
  have hp2 : k ^ 2 <= K ^ 5 :=
    (Nat.pow_le_pow_left hbase 2).trans (pow_le_pow_right' hK (by omega))
  have hp3 : k ^ 3 <= K ^ 5 :=
    (Nat.pow_le_pow_left hbase 3).trans (pow_le_pow_right' hK (by omega))
  have hp4 : k ^ 4 <= K ^ 5 :=
    (Nat.pow_le_pow_left hbase 4).trans (pow_le_pow_right' hK (by omega))
  have hp5 : k ^ 5 <= K ^ 5 := Nat.pow_le_pow_left hbase 5
  have hone : 1 <= K ^ 5 := one_le_pow₀ hK
  unfold exactConcreteBatchSize
  omega

theorem exactConcreteBatch_largestBatch_le (K : Nat) :
    largestBatchBefore exactConcreteBatchSize K <= 45927 * K ^ 5 := by
  unfold largestBatchBefore
  apply Finset.sup_le
  intro k hk
  exact exactConcreteBatchSize_le_lastScale k K (Finset.mem_range.mp hk)

theorem exactConcreteBatch_largestBatchFraction_tendsto_zero :
    Tendsto
      (fun K =>
        (largestBatchBefore exactConcreteBatchSize K : Real) /
          (cumulativeCount exactConcreteBatchSize K : Real))
      atTop (nhds 0) := by
  have hinv : Tendsto (fun K : Nat => ((K : Real))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun K : Nat => (63 : Real) * ((K : Real))⁻¹)
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hinv
  apply squeeze_zero'
  · filter_upwards with K
    positivity
  · filter_upwards [eventually_gt_atTop (0 : Nat)] with K hK
    have hden : (0 : Real) <
        (cumulativeCount exactConcreteBatchSize K : Real) := by
      rw [exactConcreteBatchSize_cumulative]
      positivity
    calc
      (largestBatchBefore exactConcreteBatchSize K : Real) /
          (cumulativeCount exactConcreteBatchSize K : Real) <=
        ((45927 * K ^ 5 : Nat) : Real) /
          (cumulativeCount exactConcreteBatchSize K : Real) := by
            exact div_le_div_of_nonneg_right
              (by exact_mod_cast exactConcreteBatch_largestBatch_le K)
              hden.le
      _ = (63 : Real) * ((K : Real))⁻¹ := by
        rw [exactConcreteBatchSize_cumulative]
        push_cast
        field_simp [show (K : Real) ≠ 0 by exact_mod_cast Nat.ne_of_gt hK]
        ring
  · exact hupper

private theorem natLog_div_natCast_tendsto_zero :
    Tendsto (fun K : Nat => Real.log (K : Real) / (K : Real))
      atTop (nhds 0) := by
  have h := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  simpa [Function.comp_def] using h.comp
    (tendsto_natCast_atTop_atTop :
      Tendsto (fun K : Nat => (K : Real)) atTop atTop)

theorem exactConcreteBatch_quarterRateExploration :
    Tendsto
      (fun K =>
        Real.sqrt (cumulativeCount exactConcreteBatchSize K : Real) *
            Real.log ((cumulativeCount exactConcreteBatchSize K : Real) + 2) /
          (cumulativeCount exactConcreteBatchExplorationSize K : Real))
      atTop (nhds 0) := by
  have hinv : Tendsto (fun K : Nat => ((K : Real))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hconst : Tendsto (fun K : Nat => Real.log 731 / (K : Real))
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hinv
  have hlog := natLog_div_natCast_tendsto_zero
  have hupper : Tendsto
      (fun K : Nat => (1 / 3 : Real) *
        (Real.log 731 / (K : Real) +
          6 * (Real.log (K : Real) / (K : Real))))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul
      (hconst.add (tendsto_const_nhds.mul hlog))
  apply squeeze_zero'
    (g := fun K : Nat => (1 / 3 : Real) *
      (Real.log 731 / (K : Real) +
        6 * (Real.log (K : Real) / (K : Real))))
  · filter_upwards [eventually_ge_atTop (1 : Nat)] with K hK
    have hlog0 : 0 <= Real.log
        ((cumulativeCount exactConcreteBatchSize K : Real) + 2) := by
      apply Real.log_nonneg
      have : (1 : Real) <=
          (cumulativeCount exactConcreteBatchSize K : Real) := by
        rw [exactConcreteBatchSize_cumulative]
        exact_mod_cast
          (one_le_pow₀ (show 1 <= 3 * K by omega) : 1 <= (3 * K) ^ 6)
      linarith
    positivity
  · filter_upwards [eventually_ge_atTop (1 : Nat)] with K hK
    have hK0 : (K : Real) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
    have hKreal : (1 : Real) <= K := by exact_mod_cast hK
    have hsqrt : Real.sqrt (((3 * K) ^ 6 : Nat) : Real) =
        27 * (K : Real) ^ 3 := by
      have hnonneg : (0 : Real) <= 27 * (K : Real) ^ 3 := by positivity
      rw [show (((3 * K) ^ 6 : Nat) : Real) =
          (27 * (K : Real) ^ 3) ^ 2 by push_cast; ring]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg]
    have hinside :
        (((3 * K) ^ 6 : Nat) : Real) + 2 <=
          731 * (K : Real) ^ 6 := by
      push_cast
      have hkpow : (1 : Real) <= (K : Real) ^ 6 := one_le_pow₀ hKreal
      nlinarith
    have hlogBound :
        Real.log ((((3 * K) ^ 6 : Nat) : Real) + 2) <=
          Real.log 731 + 6 * Real.log (K : Real) := by
      calc
        Real.log ((((3 * K) ^ 6 : Nat) : Real) + 2) <=
            Real.log (731 * (K : Real) ^ 6) :=
          Real.strictMonoOn_log.monotoneOn
            (by change 0 < (((3 * K) ^ 6 : Nat) : Real) + 2; positivity)
            (by change 0 < 731 * (K : Real) ^ 6; positivity) hinside
        _ = Real.log 731 + 6 * Real.log (K : Real) := by
          rw [Real.log_mul (by norm_num) (pow_ne_zero 6 hK0), Real.log_pow]
          norm_num
    rw [exactConcreteBatchSize_cumulative,
      exactConcreteBatchExploration_cumulative, hsqrt]
    have hleft :
        27 * (K : Real) ^ 3 *
            Real.log ((((3 * K) ^ 6 : Nat) : Real) + 2) <=
          27 * (K : Real) ^ 3 *
            (Real.log 731 + 6 * Real.log (K : Real)) :=
      mul_le_mul_of_nonneg_left hlogBound (by positivity)
    calc
      27 * (K : Real) ^ 3 *
          Real.log ((((3 * K) ^ 6 : Nat) : Real) + 2) /
            (((3 * K) ^ 4 : Nat) : Real) <=
        (27 * (K : Real) ^ 3 *
          (Real.log 731 + 6 * Real.log (K : Real))) /
            (((3 * K) ^ 4 : Nat) : Real) :=
        div_le_div_of_nonneg_right hleft (by positivity)
      _ = (1 / 3 : Real) *
            (Real.log 731 / (K : Real) +
              6 * (Real.log (K : Real) / (K : Real))) := by
        push_cast
        field_simp [hK0]
        ring
  · exact hupper

/-- A fully inhabited budget for the exact concrete schedule. -/
noncomputable def exactConcreteThreeHalvesBatchBudget :
    PredeterminedThreeHalvesBatchBudget where
  batchSize := exactConcreteBatchSize
  explorationSize := exactConcreteBatchExplorationSize
  batchSize_pos := exactConcreteBatchSize_pos
  exploration_le_batch := exactConcreteBatchExplorationSize_le
  totalSamples_tendsto_atTop := exactConcreteBatch_totalSamples_tendsto_atTop
  exactThreeHalvesCount := exactConcreteBatch_exactThreeHalvesCount
  cumulativeExplorationFraction_tendsto_zero :=
    exactConcreteBatch_explorationFraction_tendsto_zero
  largestBatchFraction_tendsto_zero :=
    exactConcreteBatch_largestBatchFraction_tendsto_zero
  quarterRateExploration := exactConcreteBatch_quarterRateExploration

/-! ## Actual pilot controller and exact finite Born batches -/

/-- The common-space coordinate used for batch `k`; coordinate `n` contains
exactly `n+1` complete Pauli pilot blocks. -/
def exactConcreteBatchPilotIndex (k : Nat) : Nat :=
  exactConcreteBatchPilotBlocks k - 1

theorem exactConcreteBatchPilotIndex_succ (k : Nat) :
    exactConcreteBatchPilotIndex k + 1 = exactConcreteBatchPilotBlocks k := by
  have hpos := exactConcreteBatchPilotBlocks_pos k
  unfold exactConcreteBatchPilotIndex
  omega

theorem exactConcreteBatchPilotIndex_ge (k : Nat) :
    k <= exactConcreteBatchPilotIndex k := by
  unfold exactConcreteBatchPilotIndex exactConcreteBatchPilotBlocks
  omega

theorem exactConcreteBatchPilotIndex_tendsto_atTop :
    Tendsto exactConcreteBatchPilotIndex atTop atTop := by
  apply tendsto_atTop.2
  intro N
  filter_upwards [eventually_ge_atTop N] with k hk
  exact hk.trans (exactConcreteBatchPilotIndex_ge k)

/-- The concrete batch controller is the literal cyclic-Pauli sample mean
computed from that batch's exploration outcomes. -/
noncomputable def exactConcreteBatchPilotController
    (k : Nat) (omega : PauliPilotConsistencySampleSpace) : RLSVector 3 :=
  pauliPilotConsistencyEstimator (exactConcreteBatchPilotIndex k) omega

/-- The actual pilot controller converges in all three coordinates in
probability under its explicit Born product law. -/
theorem exactConcreteBatchPilotController_convergesInProbability
    (theta : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta) :
    forall epsilon : Real, 0 < epsilon ->
      Tendsto
        (fun k =>
          pauliPilotConsistencyMeasure theta
            (QubitOracle.coordinateDeltaBadEvent
              exactConcreteBatchPilotController theta k epsilon))
        atTop (nhds 0) := by
  intro epsilon hepsilon
  have hbase := pauliPilotConsistency_finiteDimensional_convergesInProbability
    theta hphysical
      (pauliPilotConsistencyHoeffdingContracts_mathlib theta hphysical)
      epsilon hepsilon
  change Tendsto
    (fun k =>
      pauliPilotConsistencyMeasure theta
        (QubitOracle.coordinateDeltaBadEvent
          pauliPilotConsistencyEstimator theta
            (exactConcreteBatchPilotIndex k) epsilon))
    atTop (nhds 0)
  exact hbase.comp exactConcreteBatchPilotIndex_tendsto_atTop

/-- The total truth-independent frame used by batch `k`. -/
noncomputable def exactConcreteBatchSelectedFrame
    (k : Nat) (b : RLSVector 3) :
    PilotSelectedFinalFrame (exactConcreteBatchPilotBlocks k) :=
  mixedPilotLocalSelectedFinalFrame (exactConcreteBatchPilotBlocks k) b

theorem exactConcreteBatchSelectedFrame_unit
    (k : Nat) (b : RLSVector 3)
    (pilot : PauliPilotPath (exactConcreteBatchPilotBlocks k)) (j : Fin 3) :
    blochNormSq
      (mixedTwoStageFrameAxis
        ((exactConcreteBatchSelectedFrame k b).frame pilot) j) = 1 :=
  (exactConcreteBatchSelectedFrame k b).axis_unit pilot j

/-- Every batch is an exact normalized finite Born pilot-plus-exploitation
experiment with the implemented pilot estimator and identity fallback frame. -/
theorem exactConcreteBatchFiniteBornJointLaw
    (k : Nat) (theta b : RLSVector 3) :
    MixedPilotFiniteRowFinalJointLaw
      (exactConcreteBatchFinalBlocks k) theta
      (exactConcreteBatchSelectedFrame k b) := by
  exact mixedPilotLocalFiniteRowFinalJointLaw
    (exactConcreteBatchPilotBlocks k) (exactConcreteBatchFinalBlocks k)
      theta b

/-- The finite row contains exactly the prescribed number of observations. -/
theorem exactConcreteBatch_observation_count (k : Nat) :
    3 * exactConcreteBatchPilotBlocks k +
        3 * exactConcreteBatchFinalBlocks k = exactConcreteBatchSize k := by
  rw [exactConcreteBatchSize_decompose]
  unfold exactConcreteBatchExplorationSize
  omega

/-- Kernel-checked closure package for the exact schedule, actual pilot
controller, total frame, and every finite Born batch.  This statement does not
rename an unproved aggregate LAN or minimax bridge as protocol closure. -/
theorem exactConcretePredeterminedBatch_finiteProtocol_closed
    (theta b : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta) :
    (forall K,
      cumulativeCount exactConcreteBatchExplorationSize K =
        threeHalvesExplorationCountBefore
          (cumulativeCount exactConcreteBatchSize K)) /\
    (forall epsilon : Real, 0 < epsilon ->
      Tendsto
        (fun k =>
          pauliPilotConsistencyMeasure theta
            (QubitOracle.coordinateDeltaBadEvent
              exactConcreteBatchPilotController theta k epsilon))
        atTop (nhds 0)) /\
    (forall k,
      MixedPilotFiniteRowFinalJointLaw
        (exactConcreteBatchFinalBlocks k) theta
        (exactConcreteBatchSelectedFrame k b)) := by
  exact ⟨exactConcreteBatch_exactThreeHalvesCount,
    exactConcreteBatchPilotController_convergesInProbability theta hphysical,
    fun k => exactConcreteBatchFiniteBornJointLaw k theta b⟩

end

end QubitOracle.Paper
