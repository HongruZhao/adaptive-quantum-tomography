import QubitOracle.Paper.OneQubitGeneralScheduleActualBuresInformation
import QubitOracle.Paper.OneQubitGeneralScheduleFrobeniusTraceInformation

/-!
# Safe pilot-coupled information limits on the literal adaptive path

The raw implemented pilot controller is radially clipped and shrunk by the
same deterministic vanishing ridge used in the manuscript.  This produces a
strictly interior controller on every finite path while preserving almost-sure
consistency.  Canonical Bures and Frobenius/squared-trace information limits
then follow on the same pilot path.

These are information-functional statements.  They do not assert that the
current binary, reset-at-each-batch axis cycle realizes every functional
exactly for arbitrary integer batch sizes.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory
open scoped BigOperators Topology Matrix
open OneQubitPredeterminedBatchHeadline
open PureMultilevelSequentialBatchAdaptive

noncomputable section

private theorem generalScheduleActual_blochNormSq_mul_vector
    (c : Real) (x : RLSVector 3) :
    QubitOracle.blochNormSq (fun i => c * x i) =
      c ^ 2 * QubitOracle.blochNormSq x := by
  unfold QubitOracle.blochNormSq
  simp_rw [mul_pow]
  rw [Finset.mul_sum]

/-- Radially clipped and deterministically ridge-shrunk version of the actual
batch-start controller. -/
noncomputable def generalScheduleActualSafeInteriorController
    (schedule : CumulativePauliPilotBatchSchedule) (k : Nat)
    (path : AdaptiveInfinitePath BinaryOutcome) : RLSVector 3 :=
  fun i => (1 - prespecifiedBatchRidge k ^ 2) *
    oneQubitBlochBallRadialClip
      (generalScheduleActualBatchStartController schedule k path) i

/-- The safe actual controller lies strictly inside the Bloch ball for every
finite path and every batch, including before the first pilot block. -/
theorem generalScheduleActualSafeInteriorController_strictInterior
    (schedule : CumulativePauliPilotBatchSchedule) (k : Nat)
    (path : AdaptiveInfinitePath BinaryOutcome) :
    QubitOracle.blochNormSq
      (generalScheduleActualSafeInteriorController schedule k path) < 1 := by
  rw [show generalScheduleActualSafeInteriorController schedule k path =
      fun i => (1 - prespecifiedBatchRidge k ^ 2) *
        oneQubitBlochBallRadialClip
          (generalScheduleActualBatchStartController schedule k path) i by rfl,
    generalScheduleActual_blochNormSq_mul_vector]
  have hridgePos := prespecifiedBatchRidge_pos k
  have hridgeLe := prespecifiedBatchRidge_le_one k
  have hridgeSqPos : 0 < prespecifiedBatchRidge k ^ 2 :=
    sq_pos_of_pos hridgePos
  have hridgeSqLe : prespecifiedBatchRidge k ^ 2 <= 1 := by
    nlinarith [sq_nonneg (prespecifiedBatchRidge k - 1)]
  have hfactorSq : (1 - prespecifiedBatchRidge k ^ 2) ^ 2 < 1 := by
    nlinarith
  have hclip := oneQubitBlochBallRadialClip_physical
    (generalScheduleActualBatchStartController schedule k path)
  calc
    (1 - prespecifiedBatchRidge k ^ 2) ^ 2 *
        QubitOracle.blochNormSq
          (oneQubitBlochBallRadialClip
            (generalScheduleActualBatchStartController schedule k path)) <=
        (1 - prespecifiedBatchRidge k ^ 2) ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hclip (sq_nonneg _)
    _ < 1 := by simpa using hfactorSq

/-- Coordinatewise consistency is preserved by radial clipping and the
vanishing interior ridge. -/
theorem generalScheduleActualSafeInteriorController_tendsto_of_coordinatewise
    (schedule : CumulativePauliPilotBatchSchedule)
    (theta : RLSVector 3) (path : AdaptiveInfinitePath BinaryOutcome)
    (hcontroller : forall j : Fin 3,
      Tendsto
        (fun k => generalScheduleActualBatchStartController schedule k path j)
        atTop (nhds (theta j)))
    (hInterior : QubitOracle.blochNormSq theta < 1) :
    forall j : Fin 3,
      Tendsto
        (fun k => generalScheduleActualSafeInteriorController
          schedule k path j)
        atTop (nhds (theta j)) := by
  have hnorm := blochNormSq_tendsto_of_coordinatewise
    (fun k => generalScheduleActualBatchStartController schedule k path)
    theta hcontroller
  have heventuallyInterior : ∀ᶠ k in atTop,
      QubitOracle.blochNormSq
        (generalScheduleActualBatchStartController schedule k path) < 1 :=
    (tendsto_order.1 hnorm).2 1 hInterior
  have hfactor : Tendsto
      (fun k => 1 - prespecifiedBatchRidge k ^ 2)
      atTop (nhds 1) := by
    convert tendsto_const_nhds.sub
      (prespecifiedBatchRidge_tendsto_zero.pow 2) using 1 <;> norm_num
  intro j
  have hclip : Tendsto
      (fun k => oneQubitBlochBallRadialClip
        (generalScheduleActualBatchStartController schedule k path) j)
      atTop (nhds (theta j)) := by
    apply (hcontroller j).congr'
    filter_upwards [heventuallyInterior] with k hk
    rw [oneQubitBlochBallRadialClip_eq_self _ hk.le]
  simpa [generalScheduleActualSafeInteriorController] using hfactor.mul hclip

/-- Almost-sure consistency of the safe controller under the literal adaptive
Born path law. -/
theorem generalScheduleActualSafeInteriorController_tendsto_ae
    (schedule : CumulativePauliPilotBatchSchedule) (b : RLSVector 3)
    (theta : OneQubitPhysicalParameter)
    (hInterior : QubitOracle.blochNormSq theta.1 < 1) :
    ∀ᵐ path ∂generalScheduleAdaptiveBornPathMeasure schedule b theta,
      forall j : Fin 3,
        Tendsto
          (fun k => generalScheduleActualSafeInteriorController
            schedule k path j)
          atTop (nhds (theta.1 j)) := by
  filter_upwards
      [generalScheduleActualBatchStartController_tendsto_ae
        schedule b theta hInterior]
      with path hcontroller
  exact generalScheduleActualSafeInteriorController_tendsto_of_coordinatewise
    schedule theta.1 path hcontroller hInterior

/-- Canonical Bures information functional driven by the safe controller on
the literal pilot path. -/
noncomputable def generalSchedulePilotCoupledFullCanonicalBuresInformation
    (schedule : CumulativePauliPilotBatchSchedule)
    (theta : RLSVector 3) (path : AdaptiveInfinitePath BinaryOutcome) :
    Nat -> Matrix (Fin 3) (Fin 3) Real :=
  batchedPredictableMatrixAverage schedule.budget.batchSize
    schedule.budget.explorationSize
    (fun k => generalScheduleCanonicalBuresControllerInformation theta
      (generalScheduleActualSafeInteriorController schedule k path))
    (fun _ => generalSchedulePauliExplorationInformation theta)

/-- Frobenius/squared-trace information functional driven by the same safe
controller and literal pilot path. -/
noncomputable def generalSchedulePilotCoupledFullFrobeniusTraceInformation
    (schedule : CumulativePauliPilotBatchSchedule)
    (theta : RLSVector 3) (path : AdaptiveInfinitePath BinaryOutcome) :
    Nat -> Matrix (Fin 3) (Fin 3) Real :=
  batchedPredictableMatrixAverage schedule.budget.batchSize
    schedule.budget.explorationSize
    (fun k => generalScheduleFrobeniusTraceControllerInformation theta
      (generalScheduleActualSafeInteriorController schedule k path))
    (fun _ => generalSchedulePauliExplorationInformation theta)

/-- Almost-sure canonical Bures information convergence, including the
maximally mixed truth. -/
theorem generalSchedulePilotCoupledFullCanonicalBuresInformation_tendsto_ae
    (schedule : CumulativePauliPilotBatchSchedule) (b : RLSVector 3)
    (theta : OneQubitPhysicalParameter)
    (hInterior : QubitOracle.blochNormSq theta.1 < 1) :
    ∀ᵐ path ∂generalScheduleAdaptiveBornPathMeasure schedule b theta,
      BatchMatrixEntrywiseTendsto
        (generalSchedulePilotCoupledFullCanonicalBuresInformation
          schedule theta.1 path)
        (mixedBuresTarget theta.1) := by
  filter_upwards
      [generalScheduleActualSafeInteriorController_tendsto_ae
        schedule b theta hInterior]
      with path hcontrollerCoordinates
  have hcontroller : Tendsto
      (fun k => generalScheduleActualSafeInteriorController schedule k path)
      atTop (nhds theta.1) :=
    tendsto_pi_nhds.2 hcontrollerCoordinates
  have hexploitMatrix := mixedBuresStage_tendsto
    theta.1 hInterior
    (fun k => generalScheduleActualSafeInteriorController schedule k path)
    hcontroller
    (fun k => generalScheduleActualSafeInteriorController_strictInterior
      schedule k path)
    (fun k => mixedCanonicalRadialTangentFrame
      (generalScheduleActualSafeInteriorController schedule k path))
  have hexploitation : BatchMatrixEntrywiseTendsto
      (fun k => generalScheduleCanonicalBuresControllerInformation theta.1
        (generalScheduleActualSafeInteriorController schedule k path))
      (mixedBuresTarget theta.1) := by
    intro i j
    exact tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hexploitMatrix i) j
  have htotal : Tendsto
      (fun K => ∑ k ∈ Finset.range K,
        (schedule.budget.batchSize k : Real)) atTop atTop := by
    simpa [cumulativeCount] using
      schedule.budget.totalSamples_tendsto_atTop
  apply batchedPredictableMatrixAverage_tendsto
    schedule.budget.batchSize schedule.budget.explorationSize
    (fun k => generalScheduleCanonicalBuresControllerInformation theta.1
      (generalScheduleActualSafeInteriorController schedule k path))
    (fun _ => generalSchedulePauliExplorationInformation theta.1)
    (mixedBuresTarget theta.1)
    (fun _ _ => 2 * (1 - QubitOracle.blochNormSq theta.1)⁻¹)
    htotal hexploitation
  · intro i j
    exact mul_nonneg (by norm_num)
      (inv_nonneg.mpr (sub_nonneg.mpr hInterior.le))
  · intro k i j
    exact generalSchedulePauliExploration_sub_canonicalBures_entry_norm_le
      theta.1 (generalScheduleActualSafeInteriorController schedule k path)
      hInterior i j
  · simpa [cumulativeCount] using
      schedule.budget.cumulativeExplorationFraction_tendsto_zero

/-- Almost-sure Frobenius and squared-trace optimal information convergence
for the same safe pilot controller. -/
theorem generalSchedulePilotCoupledFullFrobeniusTraceInformation_tendsto_ae
    (schedule : CumulativePauliPilotBatchSchedule) (b : RLSVector 3)
    (theta : OneQubitPhysicalParameter)
    (hInterior : QubitOracle.blochNormSq theta.1 < 1) :
    ∀ᵐ path ∂generalScheduleAdaptiveBornPathMeasure schedule b theta,
      BatchMatrixEntrywiseTendsto
        (generalSchedulePilotCoupledFullFrobeniusTraceInformation
          schedule theta.1 path)
        (mixedFrobeniusTraceTarget theta.1) := by
  filter_upwards
      [generalScheduleActualSafeInteriorController_tendsto_ae
        schedule b theta hInterior]
      with path hcontrollerCoordinates
  have hcontroller : Tendsto
      (fun k => generalScheduleActualSafeInteriorController schedule k path)
      atTop (nhds theta.1) :=
    tendsto_pi_nhds.2 hcontrollerCoordinates
  have hexploitMatrix := mixedFrobeniusTraceStage_tendsto
    theta.1 hInterior
    (fun k => generalScheduleActualSafeInteriorController schedule k path)
    hcontroller
    (fun k => generalScheduleActualSafeInteriorController_strictInterior
      schedule k path)
    (fun k => mixedCanonicalRadialTangentFrame
      (generalScheduleActualSafeInteriorController schedule k path))
  have hexploitation : BatchMatrixEntrywiseTendsto
      (fun k => generalScheduleFrobeniusTraceControllerInformation theta.1
        (generalScheduleActualSafeInteriorController schedule k path))
      (mixedFrobeniusTraceTarget theta.1) := by
    intro i j
    exact tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hexploitMatrix i) j
  have htotal : Tendsto
      (fun K => ∑ k ∈ Finset.range K,
        (schedule.budget.batchSize k : Real)) atTop atTop := by
    simpa [cumulativeCount] using
      schedule.budget.totalSamples_tendsto_atTop
  apply batchedPredictableMatrixAverage_tendsto
    schedule.budget.batchSize schedule.budget.explorationSize
    (fun k => generalScheduleFrobeniusTraceControllerInformation theta.1
      (generalScheduleActualSafeInteriorController schedule k path))
    (fun _ => generalSchedulePauliExplorationInformation theta.1)
    (mixedFrobeniusTraceTarget theta.1)
    (fun _ _ => 2 * (1 - QubitOracle.blochNormSq theta.1)⁻¹)
    htotal hexploitation
  · intro i j
    exact mul_nonneg (by norm_num)
      (inv_nonneg.mpr (sub_nonneg.mpr hInterior.le))
  · intro k i j
    exact generalSchedulePauliExploration_sub_frobeniusTrace_entry_norm_le
      theta.1 (generalScheduleActualSafeInteriorController schedule k path)
      hInterior
      (generalScheduleActualSafeInteriorController_strictInterior
        schedule k path) i j
  · simpa [cumulativeCount] using
      schedule.budget.cumulativeExplorationFraction_tendsto_zero

/-- Joint safe-controller information endpoint for all three mixed-qubit
losses used in the manuscript. -/
theorem generalSchedulePilotCoupledMixedQubitInformation_core_closed
    (schedule : CumulativePauliPilotBatchSchedule) (b : RLSVector 3)
    (theta : OneQubitPhysicalParameter)
    (hInterior : QubitOracle.blochNormSq theta.1 < 1) :
    (∀ k path, QubitOracle.blochNormSq
      (generalScheduleActualSafeInteriorController schedule k path) < 1) /\
    (∀ᵐ path ∂generalScheduleAdaptiveBornPathMeasure schedule b theta,
      forall j : Fin 3,
        Tendsto
          (fun k => generalScheduleActualSafeInteriorController
            schedule k path j)
          atTop (nhds (theta.1 j))) /\
    (∀ᵐ path ∂generalScheduleAdaptiveBornPathMeasure schedule b theta,
      BatchMatrixEntrywiseTendsto
        (generalSchedulePilotCoupledFullCanonicalBuresInformation
          schedule theta.1 path)
        (mixedBuresTarget theta.1)) /\
    (∀ᵐ path ∂generalScheduleAdaptiveBornPathMeasure schedule b theta,
      BatchMatrixEntrywiseTendsto
        (generalSchedulePilotCoupledFullFrobeniusTraceInformation
          schedule theta.1 path)
        (mixedFrobeniusTraceTarget theta.1)) := by
  exact
    ⟨fun k path =>
        generalScheduleActualSafeInteriorController_strictInterior
          schedule k path,
      generalScheduleActualSafeInteriorController_tendsto_ae
        schedule b theta hInterior,
      generalSchedulePilotCoupledFullCanonicalBuresInformation_tendsto_ae
        schedule b theta hInterior,
      generalSchedulePilotCoupledFullFrobeniusTraceInformation_tendsto_ae
        schedule b theta hInterior⟩

end

end QubitOracle.Paper
