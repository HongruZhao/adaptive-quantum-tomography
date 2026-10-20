import QubitOracle.Paper.OneQubitPrespecifiedBatchControllerSharpRate
import QubitOracle.Paper.MixedInformationMartingale
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Cumulative-past Pauli controller for general predetermined batches

This file removes the fixed polynomial schedule from the controller and
information-convergence layer.  A schedule specifies an arbitrary positive
batch budget together with the number of complete three-Pauli pilot blocks in
each batch.  Before batch `k`, the controller uses the cumulative number of
pilot blocks in batches `0, ..., k - 1`; when that number is zero it uses the
fixed zero fallback.

The common-space coupling is distributional: its coordinate of size `q` has
exactly the `q`-block Born product law.  First Borel--Cantelli upgrades the
Mathlib Hoeffding bounds to almost-sure consistency of all these coordinates.
Consequently every schedule whose cumulative past pilot count diverges has an
almost-surely consistent past-only controller.  Toeplitz averaging then gives
almost-sure convergence of the cumulative Bures exploitation information.

No protocol-specific convergence axiom is introduced.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory Set Matrix
open scoped BigOperators ENNReal Topology Matrix
open OneQubitPredeterminedBatchHeadline
open PureMultilevelSequentialBatchAdaptive

noncomputable section

attribute [local instance] pauliPilotBornPathMeasurableSpace

/-! ## Closed Hoeffding contracts and almost-sure pilot consistency -/

/-- The finite Pauli contracts are discharged by the Mathlib Hoeffding
bridge, uniformly in the block count and coordinate. -/
def pauliPilotConsistencyHoeffdingContracts_closed
    (theta : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta) :
    PauliPilotConsistencyHoeffdingContracts theta hphysical := by
  intro n j
  exact
    ⟨hoeffding1963UniversalTheorem2_of_mathlib _ _ _ _,
      hoeffding1963UniversalTheorem2_of_mathlib _ _ _ _⟩

/-- A real geometric envelope written in the form needed by the summability
lemma. -/
noncomputable def generalSchedulePilotGeometricEnvelope
    (delta : Real) (n : Nat) : ENNReal :=
  ENNReal.ofReal
    (2 * Real.exp (-(delta ^ 2 / 2) * ((n : Real) + 1)))

theorem generalSchedulePilotGeometricEnvelope_tsum_ne_top
    (delta : Real) (hdelta : 0 < delta) :
    (∑' n : Nat, generalSchedulePilotGeometricEnvelope delta n) ≠ ∞ := by
  have hc : -(delta ^ 2 / 2) < 0 := by
    nlinarith [sq_pos_of_pos hdelta]
  have hreal : Summable
      (fun n : Nat =>
        2 * Real.exp (-(delta ^ 2 / 2) * ((n : Real) + 1))) := by
    exact (Real.summable_exp_nat_mul_of_ge
      (c := -(delta ^ 2 / 2)) hc (fun n => by norm_num)).mul_left 2
  exact hreal.tsum_ofReal_ne_top

theorem pauliPilotConsistencyCoordinateBadEvent_tsum_ne_top_closed
    (theta : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (j : Fin 3) (delta : Real) (hdelta : 0 < delta) :
    (∑' n : Nat,
      pauliPilotConsistencyMeasure theta
        {omega |
          delta ≤
            |pauliPilotConsistencyEstimator n omega j - theta j|}) ≠ ∞ := by
  apply ne_top_of_le_ne_top
    (generalSchedulePilotGeometricEnvelope_tsum_ne_top delta hdelta)
  apply ENNReal.tsum_le_tsum
  intro n
  calc
    pauliPilotConsistencyMeasure theta
        {omega |
          delta ≤
            |pauliPilotConsistencyEstimator n omega j - theta j|} ≤
      pauliPilotCoordinateHoeffdingEnvelope n delta :=
        pauliPilotConsistency_coordinate_tail theta hphysical
          (pauliPilotConsistencyHoeffdingContracts_closed theta hphysical)
          n j delta hdelta
    _ = generalSchedulePilotGeometricEnvelope delta n := by
      unfold pauliPilotCoordinateHoeffdingEnvelope
        generalSchedulePilotGeometricEnvelope
      rw [ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 2)]
      norm_num
      congr 2
      push_cast
      ring

/-- The common family containing the exact `q`-block Born law for every
positive `q` is almost surely coordinatewise consistent. -/
theorem pauliPilotConsistencyEstimator_tendsto_ae_closed
    (theta : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta) :
    ∀ᵐ omega ∂pauliPilotConsistencyMeasure theta,
      ∀ j : Fin 3,
        Tendsto
          (fun n => pauliPilotConsistencyEstimator n omega j)
          atTop (nhds (theta j)) := by
  have hcoordinate : ∀ j : Fin 3,
      ∀ᵐ omega ∂pauliPilotConsistencyMeasure theta,
        Tendsto
          (fun n => pauliPilotConsistencyEstimator n omega j)
          atTop (nhds (theta j)) := by
    intro j
    have hBC : ∀ delta : Real, 0 < delta →
        ∀ᵐ omega ∂pauliPilotConsistencyMeasure theta,
          ∀ᶠ n in atTop,
            omega ∉
              {omega |
                delta ≤
                  |pauliPilotConsistencyEstimator n omega j - theta j|} := by
      intro delta hdelta
      exact ae_eventually_notMem
        (pauliPilotConsistencyCoordinateBadEvent_tsum_ne_top_closed
          theta hphysical j delta hdelta)
    obtain ⟨v, -, hvpos, hvlim⟩ :
        ∃ v : Nat → Real, StrictAnti v ∧ (∀ n, 0 < v n) ∧
          Tendsto v atTop (nhds 0) :=
      exists_seq_strictAnti_tendsto (0 : Real)
    have hall : ∀ᵐ omega ∂pauliPilotConsistencyMeasure theta,
        ∀ i, ∀ᶠ n in atTop,
          omega ∉
            {omega |
              v i ≤
                |pauliPilotConsistencyEstimator n omega j - theta j|} :=
      ae_all_iff.2 (fun i => hBC (v i) (hvpos i))
    filter_upwards [hall] with omega homega
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨i, hi⟩ : ∃ i, v i < epsilon :=
      ((tendsto_order.1 hvlim).2 epsilon hepsilon).exists
    obtain ⟨N, hN⟩ := eventually_atTop.1 (homega i)
    refine ⟨N, fun n hn => ?_⟩
    have habs :
        |pauliPilotConsistencyEstimator n omega j - theta j| < v i := by
      simpa only [Set.mem_setOf_eq, not_le] using hN n hn
    simpa [Real.dist_eq] using habs.trans hi
  filter_upwards [hcoordinate 0, hcoordinate 1, hcoordinate 2] with
      omega h0 h1 h2
  intro j
  fin_cases j <;> assumption

/-! ## Arbitrary predetermined schedule and past-only controller -/

/-- A general predetermined batch schedule whose exploration consists of
complete three-Pauli blocks and whose cumulative past pilot count diverges. -/
structure CumulativePauliPilotBatchSchedule where
  budget : PredeterminedThreeHalvesBatchBudget
  pilotBlocks : Nat → Nat
  explorationSize_eq_three_mul : ∀ k,
    budget.explorationSize k = 3 * pilotBlocks k
  cumulativePilotBlocks_tendsto_atTop :
    Tendsto (cumulativeCount pilotBlocks) atTop atTop

def CumulativePauliPilotBatchSchedule.pastPilotBlockCount
    (schedule : CumulativePauliPilotBatchSchedule) (k : Nat) : Nat :=
  cumulativeCount schedule.pilotBlocks k

def CumulativePauliPilotBatchSchedule.pastPilotIndex
    (schedule : CumulativePauliPilotBatchSchedule) (k : Nat) : Nat :=
  (schedule.pastPilotBlockCount k).pred

theorem CumulativePauliPilotBatchSchedule.pastPilotIndex_tendsto_atTop
    (schedule : CumulativePauliPilotBatchSchedule) :
    Tendsto schedule.pastPilotIndex atTop atTop := by
  rw [tendsto_atTop]
  intro N
  filter_upwards
    [(tendsto_atTop.1 schedule.cumulativePilotBlocks_tendsto_atTop)
      (N + 1)] with k hk
  unfold pastPilotIndex pastPilotBlockCount
  simpa using Nat.pred_le_pred hk

theorem CumulativePauliPilotBatchSchedule.pastPilotBlockCount_eventually_pos
    (schedule : CumulativePauliPilotBatchSchedule) :
    ∀ᶠ k in atTop, 0 < schedule.pastPilotBlockCount k := by
  filter_upwards
    [(tendsto_atTop.1 schedule.cumulativePilotBlocks_tendsto_atTop) 1]
      with k hk
  unfold pastPilotBlockCount
  exact lt_of_lt_of_le Nat.zero_lt_one hk

theorem CumulativePauliPilotBatchSchedule.pastPilotIndex_succ_eq_count
    (schedule : CumulativePauliPilotBatchSchedule) (k : Nat)
    (hk : 0 < schedule.pastPilotBlockCount k) :
    Nat.succ (schedule.pastPilotIndex k) =
      schedule.pastPilotBlockCount k := by
  exact Nat.succ_pred_eq_of_pos hk

/-- Before batch `k`, use all pilot blocks assigned to earlier batches.  The
zero fallback is used only while no pilot block has yet been observed. -/
noncomputable def cumulativePauliPastController
    (schedule : CumulativePauliPilotBatchSchedule) (k : Nat)
    (omega : PauliPilotConsistencySampleSpace) : RLSVector 3 :=
  if schedule.pastPilotBlockCount k = 0 then 0
  else pauliPilotConsistencyEstimator (schedule.pastPilotIndex k) omega

/-- Exact finite Born marginal of the implemented past controller whenever
at least one past pilot block is available.  Together with
`pastPilotIndex_succ_eq_count`, the finite law has exactly the cumulative
number of past blocks. -/
theorem cumulativePauliPastController_map_eq_exactBornMarginal
    (schedule : CumulativePauliPilotBatchSchedule)
    (theta : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (k : Nat) (hk : 0 < schedule.pastPilotBlockCount k) :
    (pauliPilotConsistencyMeasure theta).map
        (cumulativePauliPastController schedule k) =
      (pauliPilotBornProductMeasure
        (q := Nat.succ (schedule.pastPilotIndex k)) theta).map
          pauliPilotEstimate := by
  have hk0 : schedule.pastPilotBlockCount k ≠ 0 := Nat.ne_of_gt hk
  have hcontroller : cumulativePauliPastController schedule k =
      fun omega => pauliPilotConsistencyEstimator
        (schedule.pastPilotIndex k) omega := by
    funext omega
    simp [cumulativePauliPastController, hk0]
  rw [hcontroller]
  unfold pauliPilotConsistencyEstimator
  calc
    (pauliPilotConsistencyMeasure theta).map
        (fun omega => pauliPilotEstimate
          (omega (schedule.pastPilotIndex k))) =
      ((pauliPilotConsistencyMeasure theta).map
        (Function.eval (schedule.pastPilotIndex k))).map
          pauliPilotEstimate := by
            rw [Measure.map_map]
            · rfl
            · exact Measurable.of_discrete
            · exact measurable_pi_apply _
    _ = (pauliPilotBornProductMeasure
          (q := Nat.succ (schedule.pastPilotIndex k)) theta).map
            pauliPilotEstimate := by
      rw [pauliPilotConsistencyMeasure_map_eval theta hphysical]

/-- Every admissible schedule turns the exact Born pilot family into an
almost-surely consistent controller that uses only pre-batch pilot counts. -/
theorem cumulativePauliPastController_tendsto_ae_closed
    (schedule : CumulativePauliPilotBatchSchedule)
    (theta : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta) :
    ∀ᵐ omega ∂pauliPilotConsistencyMeasure theta,
      ∀ j : Fin 3,
        Tendsto
          (fun k => cumulativePauliPastController schedule k omega j)
          atTop (nhds (theta j)) := by
  filter_upwards
      [pauliPilotConsistencyEstimator_tendsto_ae_closed theta hphysical]
      with omega hfull
  intro j
  have hsubsequence :=
    (hfull j).comp schedule.pastPilotIndex_tendsto_atTop
  have heq :
      (fun k => cumulativePauliPastController schedule k omega j) =ᶠ[atTop]
        (fun k => pauliPilotConsistencyEstimator
          (schedule.pastPilotIndex k) omega j) := by
    filter_upwards [schedule.pastPilotBlockCount_eventually_pos] with k hk
    simp [cumulativePauliPastController, Nat.ne_of_gt hk]
  exact hsubsequence.congr' heq.symm

/-! ## Almost-sure cumulative Bures information convergence -/

/-- Equal allocation over any three supplied measurement axes. -/
def generalScheduleEqualAxisInformation
    (theta : RLSVector 3) (axis : Fin 3 → RLSVector 3) :
    Matrix (Fin 3) (Fin 3) Real :=
  (1 / 3 : Real) • ∑ k : Fin 3,
    QubitOracle.mixedAxisFisher theta (axis k)

/-- Every equal three-axis design is uniformly entrywise bounded at an
interior truth when all three axes are unit vectors. -/
theorem generalScheduleEqualAxisInformation_entry_norm_le
    (theta : RLSVector 3) (axis : Fin 3 → RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (haxis : ∀ k, QubitOracle.blochNormSq (axis k) = 1)
    (i j : Fin 3) :
    ‖generalScheduleEqualAxisInformation theta axis i j‖ ≤
      (1 - QubitOracle.blochNormSq theta)⁻¹ := by
  rw [Real.norm_eq_abs]
  unfold generalScheduleEqualAxisInformation
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  calc
    |(1 / 3 : Real) *
        ∑ k : Fin 3, QubitOracle.mixedAxisFisher theta (axis k) i j| =
      (1 / 3 : Real) *
        |∑ k : Fin 3, QubitOracle.mixedAxisFisher theta (axis k) i j| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 1 / 3)]
    _ ≤ (1 / 3 : Real) *
        ∑ k : Fin 3,
          |QubitOracle.mixedAxisFisher theta (axis k) i j| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ ≤ (1 / 3 : Real) *
        ∑ _k : Fin 3, (1 - QubitOracle.blochNormSq theta)⁻¹ := by
      gcongr with k
      rw [← Real.norm_eq_abs]
      exact mixedAxisInformation_entry_norm_le
        theta (axis k) hInterior (haxis k) i j
    _ = (1 - QubitOracle.blochNormSq theta)⁻¹ := by
      simp [Fin.sum_univ_succ]

/-- Equal-cycle Bures exploitation information as a deterministic function of
the current controller value. -/
def generalScheduleBuresControllerInformation
    (theta b x : RLSVector 3) : Matrix (Fin 3) (Fin 3) Real :=
  generalScheduleEqualAxisInformation theta
    (fun k => mixedTwoStageFrameAxis
      (mixedPilotSelectedLocalFrame b x) k)

theorem generalScheduleBuresControllerInformation_entry_norm_le
    (theta b x : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (i j : Fin 3) :
    ‖generalScheduleBuresControllerInformation theta b x i j‖ ≤
      (1 - QubitOracle.blochNormSq theta)⁻¹ := by
  apply generalScheduleEqualAxisInformation_entry_norm_le
    theta
    (fun k => mixedTwoStageFrameAxis
      (mixedPilotSelectedLocalFrame b x) k)
    hTruth.2
  intro k
  change QubitOracle.blochNormSq
    (qubitFrameAxis (mixedPilotSelectedLocalFrame b x) k) = 1
  exact mixedPilotSelectedLocalFrame_axis_unit b x k

/-- Per-observation Fisher matrix of one complete cyclic-Pauli exploration
block. -/
def generalSchedulePauliExplorationInformation
    (theta : RLSVector 3) : Matrix (Fin 3) (Fin 3) Real :=
  generalScheduleEqualAxisInformation theta qubitPauliCoordinateAxis

theorem generalSchedulePauliExplorationInformation_entry_norm_le
    (theta : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (i j : Fin 3) :
    ‖generalSchedulePauliExplorationInformation theta i j‖ ≤
      (1 - QubitOracle.blochNormSq theta)⁻¹ := by
  exact generalScheduleEqualAxisInformation_entry_norm_le
    theta qubitPauliCoordinateAxis hTruth.2
      qubitPauliCoordinateAxis_normSq i j

/-- Uniform finite algebraic bound comparing cyclic-Pauli exploration with
the safeguarded adaptive Bures frame. -/
theorem generalSchedulePauliExploration_sub_controller_entry_norm_le
    (theta b x : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (i j : Fin 3) :
    ‖generalSchedulePauliExplorationInformation theta i j -
      generalScheduleBuresControllerInformation theta b x i j‖ ≤
        2 * (1 - QubitOracle.blochNormSq theta)⁻¹ := by
  calc
    ‖generalSchedulePauliExplorationInformation theta i j -
        generalScheduleBuresControllerInformation theta b x i j‖ ≤
      ‖generalSchedulePauliExplorationInformation theta i j‖ +
        ‖generalScheduleBuresControllerInformation theta b x i j‖ :=
      norm_sub_le _ _
    _ ≤ (1 - QubitOracle.blochNormSq theta)⁻¹ +
        (1 - QubitOracle.blochNormSq theta)⁻¹ :=
      add_le_add
        (generalSchedulePauliExplorationInformation_entry_norm_le
          theta hTruth i j)
        (generalScheduleBuresControllerInformation_entry_norm_le
          theta b x hTruth i j)
    _ = 2 * (1 - QubitOracle.blochNormSq theta)⁻¹ := by ring

/-- Entrywise continuity of the concrete safeguarded frame-information map at
every nonzero interior truth with a nonparallel deterministic seed. -/
theorem generalScheduleBuresControllerInformation_entry_tendsto
    (theta b : RLSVector 3) (x : Nat → RLSVector 3)
    (hx : ∀ j, Tendsto (fun n => x n j) atTop (nhds (theta j)))
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) (i j : Fin 3) :
    Tendsto
      (fun n => generalScheduleBuresControllerInformation theta b (x n) i j)
      atTop
      (nhds (mixedPolynomialTruthFrameInformationMatrix theta b i j)) := by
  have hDomain : LocalContinuousFrameDomain b theta :=
    ⟨hTruth.1, hSeed⟩
  have hterm : ∀ k : Fin 3,
      Tendsto
        (fun n =>
          mixedTwoStageFrameAxis (mixedPilotSelectedLocalFrame b (x n)) k i *
              mixedTwoStageFrameAxis
                (mixedPilotSelectedLocalFrame b (x n)) k j /
            (1 - (QubitOracle.blochDot theta
              (mixedTwoStageFrameAxis
                (mixedPilotSelectedLocalFrame b (x n)) k)) ^ 2))
        atTop
        (nhds
          (mixedTwoStageFrameAxis (localContinuousQubitFrame b theta) k i *
              mixedTwoStageFrameAxis
                (localContinuousQubitFrame b theta) k j /
            (1 - (QubitOracle.blochDot theta
              (mixedTwoStageFrameAxis
                (localContinuousQubitFrame b theta) k)) ^ 2))) := by
    intro k
    have hi := mixedPilotSelectedLocalFrame_entry_tendsto_of_coordinatewise
      b x theta hx hTruth.1 hSeed i k
    have hj := mixedPilotSelectedLocalFrame_entry_tendsto_of_coordinatewise
      b x theta hx hTruth.1 hSeed j k
    have htheta' : Tendsto
        (fun n => QubitOracle.blochDot theta
          (mixedTwoStageFrameAxis
            (mixedPilotSelectedLocalFrame b (x n)) k))
        atTop
        (nhds (QubitOracle.blochDot theta
          (mixedTwoStageFrameAxis
            (localContinuousQubitFrame b theta) k))) := by
      unfold QubitOracle.blochDot mixedTwoStageFrameAxis
      apply tendsto_finset_sum
      intro ell hell
      exact tendsto_const_nhds.mul
        (mixedPilotSelectedLocalFrame_entry_tendsto_of_coordinatewise
          b x theta hx hTruth.1 hSeed ell k)
    have hunit : QubitOracle.blochNormSq
        (mixedTwoStageFrameAxis
          (localContinuousQubitFrame b theta) k) = 1 := by
      change QubitOracle.blochNormSq
        (qubitFrameAxis (localContinuousQubitFrame b theta) k) = 1
      exact localContinuousQubitFrame_axis_unit hDomain k
    have hden_pos : 0 < 1 - (QubitOracle.blochDot theta
        (mixedTwoStageFrameAxis
          (localContinuousQubitFrame b theta) k)) ^ 2 :=
      mixedTwoStageAxisFisherDenominator_pos theta
        (mixedTwoStageFrameAxis
          (localContinuousQubitFrame b theta) k) hTruth.2 hunit
    exact (hi.mul hj).div
      (tendsto_const_nhds.sub (htheta'.pow 2)) (ne_of_gt hden_pos)
  unfold generalScheduleBuresControllerInformation
    generalScheduleEqualAxisInformation
    mixedPolynomialTruthFrameInformationMatrix
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    QubitOracle.mixedAxisFisher, QubitOracle.blochOuter,
    inv_mul_eq_div]
  apply tendsto_const_nhds.mul
  apply tendsto_finset_sum
  intro k hk
  exact hterm k

/-- Batch-size-weighted Bures exploitation information generated by the
literal past-only controller. -/
def cumulativePauliPastBuresExploitationInformation
    (schedule : CumulativePauliPilotBatchSchedule)
    (theta b : RLSVector 3)
    (omega : PauliPilotConsistencySampleSpace) :
    Nat → Matrix (Fin 3) (Fin 3) Real :=
  batchWeightedMatrixAverage schedule.budget.batchSize
    (fun k => generalScheduleBuresControllerInformation theta b
      (cumulativePauliPastController schedule k omega))

/-- For arbitrary deterministic batches satisfying the schedule conditions,
the cumulative exploitation Fisher matrix converges almost surely to the exact
Bures target. -/
theorem cumulativePauliPastBuresExploitationInformation_tendsto_ae_closed
    (schedule : CumulativePauliPilotBatchSchedule)
    (theta b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    ∀ᵐ omega ∂pauliPilotConsistencyMeasure theta,
      BatchMatrixEntrywiseTendsto
        (cumulativePauliPastBuresExploitationInformation
          schedule theta b omega)
        (mixedBuresTarget theta) := by
  let hphysical := mixedNonzeroInterior_pauliPilotPhysical theta hTruth
  filter_upwards
      [cumulativePauliPastController_tendsto_ae_closed
        schedule theta hphysical]
      with omega hcontroller
  have htotal : Tendsto
      (fun K => ∑ k ∈ Finset.range K,
        (schedule.budget.batchSize k : Real)) atTop atTop := by
    simpa [cumulativeCount] using
      schedule.budget.totalSamples_tendsto_atTop
  have hexploitation : BatchMatrixEntrywiseTendsto
      (fun k => generalScheduleBuresControllerInformation theta b
        (cumulativePauliPastController schedule k omega))
      (mixedPolynomialTruthFrameInformationMatrix theta b) := by
    intro i j
    exact generalScheduleBuresControllerInformation_entry_tendsto
      theta b
      (fun k => cumulativePauliPastController schedule k omega)
      hcontroller hTruth hSeed i j
  have hweighted := batchWeightedMatrixAverage_tendsto
    schedule.budget.batchSize
    (fun k => generalScheduleBuresControllerInformation theta b
      (cumulativePauliPastController schedule k omega))
    (mixedPolynomialTruthFrameInformationMatrix theta b)
    htotal hexploitation
  rw [mixedPolynomialTruthFrameInformationMatrix_eq_mixedBuresTarget
    theta b hTruth hSeed] at hweighted
  exact hweighted

/-- Adding any uniformly entrywise-bounded exploration information preserves
the same Bures limit because the schedule's cumulative exploration fraction
vanishes.  This theorem isolates the remaining finite algebraic certificate
for a chosen exploration Fisher matrix. -/
theorem cumulativePauliPastPredictableBuresInformation_tendsto_ae
    (schedule : CumulativePauliPilotBatchSchedule)
    (theta b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (explorationInformation : Nat → Matrix (Fin 3) (Fin 3) Real)
    (bound : Fin 3 → Fin 3 → Real)
    (hbound : ∀ i j, 0 ≤ bound i j)
    (hdifference : ∀ omega k i j,
      ‖explorationInformation k i j -
        generalScheduleBuresControllerInformation theta b
          (cumulativePauliPastController schedule k omega) i j‖ ≤
        bound i j) :
    ∀ᵐ omega ∂pauliPilotConsistencyMeasure theta,
      BatchMatrixEntrywiseTendsto
        (batchedPredictableMatrixAverage schedule.budget.batchSize
          schedule.budget.explorationSize
          (fun k => generalScheduleBuresControllerInformation theta b
            (cumulativePauliPastController schedule k omega))
          explorationInformation)
        (mixedBuresTarget theta) := by
  let hphysical := mixedNonzeroInterior_pauliPilotPhysical theta hTruth
  filter_upwards
      [cumulativePauliPastController_tendsto_ae_closed
        schedule theta hphysical]
      with omega hcontroller
  have htotal : Tendsto
      (fun K => ∑ k ∈ Finset.range K,
        (schedule.budget.batchSize k : Real)) atTop atTop := by
    simpa [cumulativeCount] using
      schedule.budget.totalSamples_tendsto_atTop
  have hexploitation : BatchMatrixEntrywiseTendsto
      (fun k => generalScheduleBuresControllerInformation theta b
        (cumulativePauliPastController schedule k omega))
      (mixedPolynomialTruthFrameInformationMatrix theta b) := by
    intro i j
    exact generalScheduleBuresControllerInformation_entry_tendsto
      theta b
      (fun k => cumulativePauliPastController schedule k omega)
      hcontroller hTruth hSeed i j
  have hfull := batchedPredictableMatrixAverage_tendsto
    schedule.budget.batchSize schedule.budget.explorationSize
    (fun k => generalScheduleBuresControllerInformation theta b
      (cumulativePauliPastController schedule k omega))
    explorationInformation
    (mixedPolynomialTruthFrameInformationMatrix theta b) bound
    htotal hexploitation hbound (hdifference omega)
    (by simpa [cumulativeCount] using
      schedule.budget.cumulativeExplorationFraction_tendsto_zero)
  rw [mixedPolynomialTruthFrameInformationMatrix_eq_mixedBuresTarget
    theta b hTruth hSeed] at hfull
  exact hfull

/-- The literal total predictable Fisher matrix: cyclic-Pauli exploration
plus the past-controller Bures exploitation frame. -/
def cumulativePauliPastFullBuresInformation
    (schedule : CumulativePauliPilotBatchSchedule)
    (theta b : RLSVector 3)
    (omega : PauliPilotConsistencySampleSpace) :
    Nat → Matrix (Fin 3) (Fin 3) Real :=
  batchedPredictableMatrixAverage schedule.budget.batchSize
    schedule.budget.explorationSize
    (fun k => generalScheduleBuresControllerInformation theta b
      (cumulativePauliPastController schedule k omega))
    (fun _ => generalSchedulePauliExplorationInformation theta)

/-- Closed full predictable-information theorem for arbitrary predetermined
batches, the literal cyclic-Pauli exploration, and the past-only safeguarded
Bures controller. -/
theorem cumulativePauliPastFullBuresInformation_tendsto_ae_closed
    (schedule : CumulativePauliPilotBatchSchedule)
    (theta b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    ∀ᵐ omega ∂pauliPilotConsistencyMeasure theta,
      BatchMatrixEntrywiseTendsto
        (cumulativePauliPastFullBuresInformation schedule theta b omega)
        (mixedBuresTarget theta) := by
  simpa [cumulativePauliPastFullBuresInformation] using
    cumulativePauliPastPredictableBuresInformation_tendsto_ae
      schedule theta b hTruth hSeed
      (fun _ => generalSchedulePauliExplorationInformation theta)
      (fun _ _ => 2 * (1 - QubitOracle.blochNormSq theta)⁻¹)
      (fun _ _ => mul_nonneg (by norm_num)
        (inv_nonneg.mpr (sub_nonneg.mpr hTruth.2.le)))
      (fun omega k i j =>
        generalSchedulePauliExploration_sub_controller_entry_norm_le
          theta b (cumulativePauliPastController schedule k omega)
          hTruth i j)

/-- Bundled kernel endpoint for the general-schedule cumulative-pilot
information layer. -/
theorem cumulativePauliPastBuresInformation_core_closed
    (schedule : CumulativePauliPilotBatchSchedule)
    (theta b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    (∀ᵐ omega ∂pauliPilotConsistencyMeasure theta,
      ∀ j : Fin 3,
        Tendsto
          (fun k => cumulativePauliPastController schedule k omega j)
          atTop (nhds (theta j))) ∧
    (∀ᵐ omega ∂pauliPilotConsistencyMeasure theta,
      BatchMatrixEntrywiseTendsto
        (cumulativePauliPastFullBuresInformation schedule theta b omega)
        (mixedBuresTarget theta)) := by
  exact
    ⟨cumulativePauliPastController_tendsto_ae_closed schedule theta
        (mixedNonzeroInterior_pauliPilotPhysical theta hTruth),
      cumulativePauliPastFullBuresInformation_tendsto_ae_closed
        schedule theta b hTruth hSeed⟩

end

end QubitOracle.Paper
