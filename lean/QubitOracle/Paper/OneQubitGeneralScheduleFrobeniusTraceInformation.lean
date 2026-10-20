import QubitOracle.Paper.OneQubitGeneralScheduleCumulativePilotInformation
import QubitOracle.Paper.OneQubitPrespecifiedBatchSafeguardedEstimatorAsymptotics
import QubitOracle.Paper.MixedRadialTangentStage

/-!
# Concrete arbitrary-batch Frobenius/trace information convergence

This file closes the loss-specific information layer for the literal
cumulative Pauli pilot on an arbitrary predetermined batch schedule.  The
controller is radially clipped and then shrunk strictly inside the Bloch ball.
At every controller value, including the center, a deterministic total
Householder frame supplies one radial and two tangent axes.  The existing
rotation-free stage theorem then gives convergence to the exact
Frobenius/squared-trace optimal information target.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory Set Matrix
open scoped BigOperators Topology Matrix
open OneQubitPredeterminedBatchHeadline
open PureMultilevelSequentialBatchAdaptive

noncomputable section

private theorem generalSchedule_blochNormSq_mul_vector
    (c : Real) (x : RLSVector 3) :
    QubitOracle.blochNormSq (fun i => c * x i) =
      c ^ 2 * QubitOracle.blochNormSq x := by
  unfold QubitOracle.blochNormSq
  simp_rw [mul_pow]
  rw [Finset.mul_sum]

/-- The cumulative past-only Pauli controller, clipped to the Bloch ball and
shrunk by a deterministic vanishing ridge.  It is strictly interior on every
finite sample path. -/
noncomputable def cumulativePauliPastSafeInteriorController
    (schedule : CumulativePauliPilotBatchSchedule) (k : Nat)
    (omega : PauliPilotConsistencySampleSpace) : RLSVector 3 :=
  fun i => (1 - prespecifiedBatchRidge k ^ 2) *
    oneQubitBlochBallRadialClip
      (cumulativePauliPastController schedule k omega) i

theorem cumulativePauliPastSafeInteriorController_strictInterior
    (schedule : CumulativePauliPilotBatchSchedule) (k : Nat)
    (omega : PauliPilotConsistencySampleSpace) :
    QubitOracle.blochNormSq
      (cumulativePauliPastSafeInteriorController schedule k omega) < 1 := by
  rw [show cumulativePauliPastSafeInteriorController schedule k omega =
      fun i => (1 - prespecifiedBatchRidge k ^ 2) *
        oneQubitBlochBallRadialClip
          (cumulativePauliPastController schedule k omega) i by rfl,
    generalSchedule_blochNormSq_mul_vector]
  have hridgePos := prespecifiedBatchRidge_pos k
  have hridgeLe := prespecifiedBatchRidge_le_one k
  have hridgeSqPos : 0 < prespecifiedBatchRidge k ^ 2 :=
    sq_pos_of_pos hridgePos
  have hridgeSqLe : prespecifiedBatchRidge k ^ 2 <= 1 := by
    nlinarith [sq_nonneg (prespecifiedBatchRidge k - 1)]
  have hfactorSq : (1 - prespecifiedBatchRidge k ^ 2) ^ 2 < 1 := by
    nlinarith
  have hclip := oneQubitBlochBallRadialClip_physical
    (cumulativePauliPastController schedule k omega)
  calc
    (1 - prespecifiedBatchRidge k ^ 2) ^ 2 *
        QubitOracle.blochNormSq
          (oneQubitBlochBallRadialClip
            (cumulativePauliPastController schedule k omega)) <=
        (1 - prespecifiedBatchRidge k ^ 2) ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hclip (sq_nonneg _)
    _ < 1 := by simpa using hfactorSq

/-- Coordinatewise convergence survives clipping and the vanishing interior
shrinkage. -/
theorem cumulativePauliPastSafeInteriorController_tendsto_of_coordinatewise
    (schedule : CumulativePauliPilotBatchSchedule)
    (theta : RLSVector 3) (omega : PauliPilotConsistencySampleSpace)
    (hcontroller : forall j : Fin 3,
      Tendsto
        (fun k => cumulativePauliPastController schedule k omega j)
        atTop (nhds (theta j)))
    (hInterior : QubitOracle.blochNormSq theta < 1) :
    forall j : Fin 3,
      Tendsto
        (fun k => cumulativePauliPastSafeInteriorController
          schedule k omega j)
        atTop (nhds (theta j)) := by
  have hnorm := blochNormSq_tendsto_of_coordinatewise
    (fun k => cumulativePauliPastController schedule k omega) theta hcontroller
  have heventuallyInterior : ∀ᶠ k in atTop,
      QubitOracle.blochNormSq
        (cumulativePauliPastController schedule k omega) < 1 :=
    (tendsto_order.1 hnorm).2 1 hInterior
  have hfactor : Tendsto
      (fun k => 1 - prespecifiedBatchRidge k ^ 2)
      atTop (nhds 1) := by
    convert tendsto_const_nhds.sub
      (prespecifiedBatchRidge_tendsto_zero.pow 2) using 1 <;> norm_num
  intro j
  have hclip : Tendsto
      (fun k => oneQubitBlochBallRadialClip
        (cumulativePauliPastController schedule k omega) j)
      atTop (nhds (theta j)) := by
    apply (hcontroller j).congr'
    filter_upwards [heventuallyInterior] with k hk
    rw [oneQubitBlochBallRadialClip_eq_self _ hk.le]
  simpa [cumulativePauliPastSafeInteriorController] using hfactor.mul hclip

/-- The exact Born pilot therefore drives the safeguarded interior controller
to every interior qubit truth almost surely. -/
theorem cumulativePauliPastSafeInteriorController_tendsto_ae_closed
    (schedule : CumulativePauliPilotBatchSchedule)
    (theta : RLSVector 3) (hInterior : QubitOracle.blochNormSq theta < 1) :
    ∀ᵐ omega ∂pauliPilotConsistencyMeasure theta,
      forall j : Fin 3,
        Tendsto
          (fun k => cumulativePauliPastSafeInteriorController
            schedule k omega j)
          atTop (nhds (theta j)) := by
  filter_upwards
      [cumulativePauliPastController_tendsto_ae_closed
        schedule theta hInterior.le]
      with omega hcontroller
  exact cumulativePauliPastSafeInteriorController_tendsto_of_coordinatewise
    schedule theta omega hcontroller hInterior

/-! ## A total deterministic radial/tangent frame -/

/-- A radial/tangent frame at every Bloch vector.  At the center it is the
ordered Pauli frame.  Away from the center it is the Householder frame aligned
with the normalized Bloch direction. -/
noncomputable def mixedCanonicalRadialTangentFrame
    (r : RLSVector 3) : MixedRadialTangentFrame r := by
  classical
  by_cases hzero : QubitOracle.blochNormSq r = 0
  · have hrzero : r = 0 := (blochNormSq_eq_zero_iff r).1 hzero
    exact
      { radial := qubitPauliCoordinateAxis 2
        tangentFirst := qubitPauliCoordinateAxis 0
        tangentSecond := qubitPauliCoordinateAxis 1
        radial_unit := qubitPauliCoordinateAxis_normSq 2
        tangentFirst_unit := qubitPauliCoordinateAxis_normSq 0
        tangentSecond_unit := qubitPauliCoordinateAxis_normSq 1
        tangentFirst_orthogonal := by simp [hrzero, QubitOracle.blochDot]
        tangentSecond_orthogonal := by simp [hrzero, QubitOracle.blochDot]
        radial_dot_sq := by
          simp [hrzero, QubitOracle.blochDot, QubitOracle.blochNormSq]
        resolution := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [qubitPauliCoordinateAxis, QubitOracle.blochOuter,
              Matrix.one_apply]
        radial_outer_of_nonzero := by
          intro hnonzero
          exact (hnonzero hzero).elim }
  · have hrpos : 0 < QubitOracle.blochNormSq r :=
      lt_of_le_of_ne (blochNormSq_nonneg r) (Ne.symm hzero)
    let u : RLSVector 3 := localNormalizedBlochDirection r
    let R : Matrix (Fin 3) (Fin 3) Real :=
      qubitTruthAlignedHouseholderFrame u
    have hu : QubitOracle.blochNormSq u = 1 := by
      exact localNormalizedBlochDirection_normSq hrpos
    have hradial : qubitFrameAxis R 2 = u := by
      exact qubitTruthAlignedHouseholderFrame_radial_axis hu
    have hsqrt : Real.sqrt (QubitOracle.blochNormSq r) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hrpos)
    have hdotRadial : QubitOracle.blochDot r u =
        Real.sqrt (QubitOracle.blochNormSq r) := by
      have hsquare := Real.sq_sqrt hrpos.le
      have hsqrtExpanded :
          Real.sqrt (r 0 ^ 2 + (r 1 ^ 2 + r 2 ^ 2)) ≠ 0 := by
        simpa [QubitOracle.blochNormSq, Fin.sum_univ_succ] using hsqrt
      simp [QubitOracle.blochNormSq, Fin.sum_univ_succ] at hsquare
      simp [u, localNormalizedBlochDirection, QubitOracle.blochDot,
        QubitOracle.blochNormSq, Fin.sum_univ_succ]
      calc
        r 0 * (r 0 / Real.sqrt (r 0 ^ 2 + (r 1 ^ 2 + r 2 ^ 2))) +
              (r 1 * (r 1 / Real.sqrt (r 0 ^ 2 + (r 1 ^ 2 + r 2 ^ 2))) +
                r 2 * (r 2 / Real.sqrt (r 0 ^ 2 + (r 1 ^ 2 + r 2 ^ 2)))) =
            (r 0 ^ 2 + (r 1 ^ 2 + r 2 ^ 2)) /
              Real.sqrt (r 0 ^ 2 + (r 1 ^ 2 + r 2 ^ 2)) := by
                field_simp [hsqrtExpanded]
        _ = Real.sqrt (r 0 ^ 2 + (r 1 ^ 2 + r 2 ^ 2)) := by
          rw [div_eq_iff hsqrtExpanded]
          nlinarith [hsquare]
    exact
      { radial := qubitFrameAxis R 2
        tangentFirst := qubitFrameAxis R 0
        tangentSecond := qubitFrameAxis R 1
        radial_unit := qubitTruthAlignedHouseholderFrame_axis_normSq u 2
        tangentFirst_unit :=
          qubitTruthAlignedHouseholderFrame_axis_normSq u 0
        tangentSecond_unit :=
          qubitTruthAlignedHouseholderFrame_axis_normSq u 1
        tangentFirst_orthogonal := by
          have horth := qubitTruthAlignedHouseholderFrame_axes_orthogonal
            u (2 : Fin 3) (0 : Fin 3)
          rw [if_neg (by decide), hradial] at horth
          change QubitOracle.blochDot r (qubitFrameAxis R 0) = 0
          simp [u, localNormalizedBlochDirection, QubitOracle.blochDot,
            Fin.sum_univ_succ] at horth ⊢
          field_simp [hsqrt] at horth
          simpa [mul_comm, mul_left_comm, mul_assoc] using horth
        tangentSecond_orthogonal := by
          have horth := qubitTruthAlignedHouseholderFrame_axes_orthogonal
            u (2 : Fin 3) (1 : Fin 3)
          rw [if_neg (by decide), hradial] at horth
          change QubitOracle.blochDot r (qubitFrameAxis R 1) = 0
          simp [u, localNormalizedBlochDirection, QubitOracle.blochDot,
            Fin.sum_univ_succ] at horth ⊢
          field_simp [hsqrt] at horth
          simpa [mul_comm, mul_left_comm, mul_assoc] using horth
        radial_dot_sq := by
          rw [hradial, hdotRadial, Real.sq_sqrt hrpos.le]
        resolution := by
          have hmatrix : R * R.transpose = 1 :=
            mul_eq_one_comm.mp
              (qubitTruthAlignedHouseholderFrame_transpose_mul_self u)
          ext i j
          simpa [R, QubitOracle.blochOuter, qubitFrameAxis,
            Matrix.mul_apply, Fin.sum_univ_succ, add_assoc] using
              congrFun (congrFun hmatrix i) j
        radial_outer_of_nonzero := by
          intro _hnonzero
          rw [hradial]
          ext i j
          simp [u, localNormalizedBlochDirection, mixedRadialProjector,
            QubitOracle.blochOuter]
          field_simp [hsqrt, hzero]
          rw [Real.sq_sqrt hrpos.le]
          ring }

/-! ## Literal Frobenius/trace exploitation and full information -/

/-- Per-observation adaptive exploitation information at truth `theta`, with
allocations and axes selected from the safe controller value `x`. -/
noncomputable def generalScheduleFrobeniusTraceControllerInformation
    (theta x : RLSVector 3) : Matrix (Fin 3) (Fin 3) Real :=
  let frame := mixedCanonicalRadialTangentFrame x
  mixedStageInformation theta
    (radialTangentMass
      (mixedCoherenceAllocation x) (mixedRadialAllocation x))
    (radialTangentAxes frame.tangentFirst frame.tangentSecond frame.radial)

theorem generalScheduleFrobeniusTraceControllerInformation_entry_norm_le
    (theta x : RLSVector 3)
    (hThetaInterior : QubitOracle.blochNormSq theta < 1)
    (hXInterior : QubitOracle.blochNormSq x < 1)
    (i j : Fin 3) :
    ‖generalScheduleFrobeniusTraceControllerInformation theta x i j‖ <=
      (1 - QubitOracle.blochNormSq theta)⁻¹ := by
  let frame := mixedCanonicalRadialTangentFrame x
  let mass := radialTangentMass
    (mixedCoherenceAllocation x) (mixedRadialAllocation x)
  let axis := radialTangentAxes frame.tangentFirst frame.tangentSecond frame.radial
  have hmass0 : forall k, 0 <= mass k :=
    radialTangentMass_nonnegative _ _
      (mixedCoherenceAllocation_pos x hXInterior).le
      (mixedRadialAllocation_pos x hXInterior).le
  have hmassSum : (∑ k, mass k) = 1 :=
    radialTangentMass_sum _ _ (mixedAllocations_sum x hXInterior)
  have haxis : forall k, QubitOracle.blochNormSq (axis k) = 1 :=
    radialTangentAxes_unit x frame
  rw [Real.norm_eq_abs]
  unfold generalScheduleFrobeniusTraceControllerInformation
    mixedStageInformation
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  change |∑ k, mass k * QubitOracle.mixedAxisFisher theta (axis k) i j| <= _
  calc
    |∑ k, mass k * QubitOracle.mixedAxisFisher theta (axis k) i j| <=
        ∑ k, |mass k * QubitOracle.mixedAxisFisher theta (axis k) i j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, mass k *
          ‖QubitOracle.mixedAxisFisher theta (axis k) i j‖ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [abs_mul, abs_of_nonneg (hmass0 k), Real.norm_eq_abs]
    _ <= ∑ k, mass k *
          (1 - QubitOracle.blochNormSq theta)⁻¹ := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left
        (mixedAxisInformation_entry_norm_le
          theta (axis k) hThetaInterior (haxis k) i j)
        (hmass0 k)
    _ = (1 - QubitOracle.blochNormSq theta)⁻¹ := by
      rw [← Finset.sum_mul, hmassSum, one_mul]

theorem generalSchedulePauliExploration_sub_frobeniusTrace_entry_norm_le
    (theta x : RLSVector 3)
    (hThetaInterior : QubitOracle.blochNormSq theta < 1)
    (hXInterior : QubitOracle.blochNormSq x < 1)
    (i j : Fin 3) :
    ‖generalSchedulePauliExplorationInformation theta i j -
      generalScheduleFrobeniusTraceControllerInformation theta x i j‖ <=
        2 * (1 - QubitOracle.blochNormSq theta)⁻¹ := by
  have hexplore := generalScheduleEqualAxisInformation_entry_norm_le
    theta qubitPauliCoordinateAxis hThetaInterior
      qubitPauliCoordinateAxis_normSq i j
  have hexploit :=
    generalScheduleFrobeniusTraceControllerInformation_entry_norm_le
      theta x hThetaInterior hXInterior i j
  have hexplore' :
      ‖generalSchedulePauliExplorationInformation theta i j‖ <=
        (1 - QubitOracle.blochNormSq theta)⁻¹ := by
    simpa [generalSchedulePauliExplorationInformation] using hexplore
  calc
    ‖generalSchedulePauliExplorationInformation theta i j -
        generalScheduleFrobeniusTraceControllerInformation theta x i j‖ <=
      ‖generalSchedulePauliExplorationInformation theta i j‖ +
        ‖generalScheduleFrobeniusTraceControllerInformation theta x i j‖ :=
      norm_sub_le _ _
    _ <= (1 - QubitOracle.blochNormSq theta)⁻¹ +
        (1 - QubitOracle.blochNormSq theta)⁻¹ :=
      add_le_add hexplore' hexploit
    _ = 2 * (1 - QubitOracle.blochNormSq theta)⁻¹ := by ring

/-! ## The same total controller closes Bures information at the center -/

/-- Equal-mass Bures exploitation information using the same total canonical
radial/tangent frame. -/
noncomputable def generalScheduleCanonicalBuresControllerInformation
    (theta x : RLSVector 3) : Matrix (Fin 3) (Fin 3) Real :=
  let frame := mixedCanonicalRadialTangentFrame x
  mixedStageInformation theta
    (radialTangentMass (1 / 3 : Real) (1 / 3 : Real))
    (radialTangentAxes frame.tangentFirst frame.tangentSecond frame.radial)

theorem generalScheduleCanonicalBuresControllerInformation_eq_equalAxis
    (theta x : RLSVector 3) :
    generalScheduleCanonicalBuresControllerInformation theta x =
      generalScheduleEqualAxisInformation theta
        (radialTangentAxes
          (mixedCanonicalRadialTangentFrame x).tangentFirst
          (mixedCanonicalRadialTangentFrame x).tangentSecond
          (mixedCanonicalRadialTangentFrame x).radial) := by
  ext i j
  simp [generalScheduleCanonicalBuresControllerInformation,
    generalScheduleEqualAxisInformation, mixedStageInformation,
    radialTangentMass, Fin.sum_univ_succ]
  ring

theorem generalScheduleCanonicalBuresControllerInformation_entry_norm_le
    (theta x : RLSVector 3)
    (hThetaInterior : QubitOracle.blochNormSq theta < 1)
    (i j : Fin 3) :
    ‖generalScheduleCanonicalBuresControllerInformation theta x i j‖ <=
      (1 - QubitOracle.blochNormSq theta)⁻¹ := by
  rw [generalScheduleCanonicalBuresControllerInformation_eq_equalAxis]
  apply generalScheduleEqualAxisInformation_entry_norm_le
    theta
      (radialTangentAxes
        (mixedCanonicalRadialTangentFrame x).tangentFirst
        (mixedCanonicalRadialTangentFrame x).tangentSecond
        (mixedCanonicalRadialTangentFrame x).radial)
      hThetaInterior
  exact radialTangentAxes_unit x (mixedCanonicalRadialTangentFrame x)

theorem generalSchedulePauliExploration_sub_canonicalBures_entry_norm_le
    (theta x : RLSVector 3)
    (hThetaInterior : QubitOracle.blochNormSq theta < 1)
    (i j : Fin 3) :
    ‖generalSchedulePauliExplorationInformation theta i j -
      generalScheduleCanonicalBuresControllerInformation theta x i j‖ <=
        2 * (1 - QubitOracle.blochNormSq theta)⁻¹ := by
  have hexplore :
      ‖generalSchedulePauliExplorationInformation theta i j‖ <=
        (1 - QubitOracle.blochNormSq theta)⁻¹ := by
    simpa [generalSchedulePauliExplorationInformation] using
      generalScheduleEqualAxisInformation_entry_norm_le
        theta qubitPauliCoordinateAxis hThetaInterior
          qubitPauliCoordinateAxis_normSq i j
  have hexploit :=
    generalScheduleCanonicalBuresControllerInformation_entry_norm_le
      theta x hThetaInterior i j
  calc
    ‖generalSchedulePauliExplorationInformation theta i j -
        generalScheduleCanonicalBuresControllerInformation theta x i j‖ <=
      ‖generalSchedulePauliExplorationInformation theta i j‖ +
        ‖generalScheduleCanonicalBuresControllerInformation theta x i j‖ :=
      norm_sub_le _ _
    _ <= (1 - QubitOracle.blochNormSq theta)⁻¹ +
        (1 - QubitOracle.blochNormSq theta)⁻¹ :=
      add_le_add hexplore hexploit
    _ = 2 * (1 - QubitOracle.blochNormSq theta)⁻¹ := by ring

/-- Literal total predictable Bures Fisher matrix driven by the same safe
past-only controller and cyclic-Pauli exploration. -/
noncomputable def cumulativePauliPastFullCanonicalBuresInformation
    (schedule : CumulativePauliPilotBatchSchedule)
    (theta : RLSVector 3)
    (omega : PauliPilotConsistencySampleSpace) :
    Nat -> Matrix (Fin 3) (Fin 3) Real :=
  batchedPredictableMatrixAverage schedule.budget.batchSize
    schedule.budget.explorationSize
    (fun k => generalScheduleCanonicalBuresControllerInformation theta
      (cumulativePauliPastSafeInteriorController schedule k omega))
    (fun _ => generalSchedulePauliExplorationInformation theta)

/-- The concrete arbitrary-batch Bures Fisher limit now includes the maximally
mixed state; no nonzero direction or seed assumption is needed. -/
theorem cumulativePauliPastFullCanonicalBuresInformation_tendsto_ae_closed
    (schedule : CumulativePauliPilotBatchSchedule)
    (theta : RLSVector 3) (hInterior : QubitOracle.blochNormSq theta < 1) :
    ∀ᵐ omega ∂pauliPilotConsistencyMeasure theta,
      BatchMatrixEntrywiseTendsto
        (cumulativePauliPastFullCanonicalBuresInformation
          schedule theta omega)
        (mixedBuresTarget theta) := by
  filter_upwards
      [cumulativePauliPastSafeInteriorController_tendsto_ae_closed
        schedule theta hInterior]
      with omega hcontrollerCoordinates
  have hcontroller : Tendsto
      (fun k => cumulativePauliPastSafeInteriorController schedule k omega)
      atTop (nhds theta) :=
    tendsto_pi_nhds.2 hcontrollerCoordinates
  have hexploitMatrix := mixedBuresStage_tendsto
    theta hInterior
    (fun k => cumulativePauliPastSafeInteriorController schedule k omega)
    hcontroller
    (fun k => cumulativePauliPastSafeInteriorController_strictInterior
      schedule k omega)
    (fun k => mixedCanonicalRadialTangentFrame
      (cumulativePauliPastSafeInteriorController schedule k omega))
  have hexploitation : BatchMatrixEntrywiseTendsto
      (fun k => generalScheduleCanonicalBuresControllerInformation theta
        (cumulativePauliPastSafeInteriorController schedule k omega))
      (mixedBuresTarget theta) := by
    intro i j
    exact tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hexploitMatrix i) j
  have htotal : Tendsto
      (fun K => ∑ k ∈ Finset.range K,
        (schedule.budget.batchSize k : Real)) atTop atTop := by
    simpa [cumulativeCount] using
      schedule.budget.totalSamples_tendsto_atTop
  apply batchedPredictableMatrixAverage_tendsto
    schedule.budget.batchSize schedule.budget.explorationSize
    (fun k => generalScheduleCanonicalBuresControllerInformation theta
      (cumulativePauliPastSafeInteriorController schedule k omega))
    (fun _ => generalSchedulePauliExplorationInformation theta)
    (mixedBuresTarget theta)
    (fun _ _ => 2 * (1 - QubitOracle.blochNormSq theta)⁻¹)
    htotal hexploitation
  · intro i j
    exact mul_nonneg (by norm_num)
      (inv_nonneg.mpr (sub_nonneg.mpr hInterior.le))
  · intro k i j
    exact generalSchedulePauliExploration_sub_canonicalBures_entry_norm_le
      theta (cumulativePauliPastSafeInteriorController schedule k omega)
      hInterior i j
  · simpa [cumulativeCount] using
      schedule.budget.cumulativeExplorationFraction_tendsto_zero

/-- The literal total predictable Fisher matrix for Frobenius and squared
trace loss: cyclic-Pauli exploration plus the safe past-controller
radial/tangent exploitation design. -/
noncomputable def cumulativePauliPastFullFrobeniusTraceInformation
    (schedule : CumulativePauliPilotBatchSchedule)
    (theta : RLSVector 3)
    (omega : PauliPilotConsistencySampleSpace) :
    Nat -> Matrix (Fin 3) (Fin 3) Real :=
  batchedPredictableMatrixAverage schedule.budget.batchSize
    schedule.budget.explorationSize
    (fun k => generalScheduleFrobeniusTraceControllerInformation theta
      (cumulativePauliPastSafeInteriorController schedule k omega))
    (fun _ => generalSchedulePauliExplorationInformation theta)

/-- For arbitrary predetermined batches with divergent cumulative Pauli pilot
and vanishing cumulative exploration fraction, the concrete adaptive Fisher
matrix converges almost surely to the exact Frobenius/trace optimal target. -/
theorem cumulativePauliPastFullFrobeniusTraceInformation_tendsto_ae_closed
    (schedule : CumulativePauliPilotBatchSchedule)
    (theta : RLSVector 3) (hInterior : QubitOracle.blochNormSq theta < 1) :
    ∀ᵐ omega ∂pauliPilotConsistencyMeasure theta,
      BatchMatrixEntrywiseTendsto
        (cumulativePauliPastFullFrobeniusTraceInformation
          schedule theta omega)
        (mixedFrobeniusTraceTarget theta) := by
  filter_upwards
      [cumulativePauliPastSafeInteriorController_tendsto_ae_closed
        schedule theta hInterior]
      with omega hcontrollerCoordinates
  have hcontroller : Tendsto
      (fun k => cumulativePauliPastSafeInteriorController schedule k omega)
      atTop (nhds theta) := by
    exact tendsto_pi_nhds.2 hcontrollerCoordinates
  have hexploitMatrix := mixedFrobeniusTraceStage_tendsto
    theta hInterior
    (fun k => cumulativePauliPastSafeInteriorController schedule k omega)
    hcontroller
    (fun k => cumulativePauliPastSafeInteriorController_strictInterior
      schedule k omega)
    (fun k => mixedCanonicalRadialTangentFrame
      (cumulativePauliPastSafeInteriorController schedule k omega))
  have hexploitation : BatchMatrixEntrywiseTendsto
      (fun k => generalScheduleFrobeniusTraceControllerInformation theta
        (cumulativePauliPastSafeInteriorController schedule k omega))
      (mixedFrobeniusTraceTarget theta) := by
    intro i j
    exact tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hexploitMatrix i) j
  have htotal : Tendsto
      (fun K => ∑ k ∈ Finset.range K,
        (schedule.budget.batchSize k : Real)) atTop atTop := by
    simpa [cumulativeCount] using
      schedule.budget.totalSamples_tendsto_atTop
  apply batchedPredictableMatrixAverage_tendsto
    schedule.budget.batchSize schedule.budget.explorationSize
    (fun k => generalScheduleFrobeniusTraceControllerInformation theta
      (cumulativePauliPastSafeInteriorController schedule k omega))
    (fun _ => generalSchedulePauliExplorationInformation theta)
    (mixedFrobeniusTraceTarget theta)
    (fun _ _ => 2 * (1 - QubitOracle.blochNormSq theta)⁻¹)
    htotal hexploitation
  · intro i j
    exact mul_nonneg (by norm_num)
      (inv_nonneg.mpr (sub_nonneg.mpr hInterior.le))
  · intro k i j
    exact generalSchedulePauliExploration_sub_frobeniusTrace_entry_norm_le
      theta (cumulativePauliPastSafeInteriorController schedule k omega)
      hInterior
      (cumulativePauliPastSafeInteriorController_strictInterior
        schedule k omega) i j
  · simpa [cumulativeCount] using
      schedule.budget.cumulativeExplorationFraction_tendsto_zero

/-- Squared trace distance has the same optimal design as Frobenius loss, so
the identical concrete predictable Fisher matrix has the same target. -/
theorem cumulativePauliPastFullSquaredTraceInformation_tendsto_ae_closed
    (schedule : CumulativePauliPilotBatchSchedule)
    (theta : RLSVector 3) (hInterior : QubitOracle.blochNormSq theta < 1) :
    ∀ᵐ omega ∂pauliPilotConsistencyMeasure theta,
      BatchMatrixEntrywiseTendsto
        (cumulativePauliPastFullFrobeniusTraceInformation
          schedule theta omega)
        (mixedFrobeniusTraceTarget theta) :=
  cumulativePauliPastFullFrobeniusTraceInformation_tendsto_ae_closed
    schedule theta hInterior

/-- Bundled exact endpoint for the arbitrary-batch mixed-qubit
Frobenius/squared-trace adaptive design. -/
theorem cumulativePauliPastFrobeniusTraceInformation_core_closed
    (schedule : CumulativePauliPilotBatchSchedule)
    (theta : RLSVector 3) (hInterior : QubitOracle.blochNormSq theta < 1) :
    (forall k omega,
      QubitOracle.blochNormSq
        (cumulativePauliPastSafeInteriorController schedule k omega) < 1) /\
    (∀ᵐ omega ∂pauliPilotConsistencyMeasure theta,
      forall j : Fin 3,
        Tendsto
          (fun k => cumulativePauliPastSafeInteriorController
            schedule k omega j)
          atTop (nhds (theta j))) /\
    (∀ᵐ omega ∂pauliPilotConsistencyMeasure theta,
      BatchMatrixEntrywiseTendsto
        (cumulativePauliPastFullFrobeniusTraceInformation
          schedule theta omega)
        (mixedFrobeniusTraceTarget theta)) := by
  exact
    ⟨fun k omega =>
        cumulativePauliPastSafeInteriorController_strictInterior
          schedule k omega,
      cumulativePauliPastSafeInteriorController_tendsto_ae_closed
        schedule theta hInterior,
      cumulativePauliPastFullFrobeniusTraceInformation_tendsto_ae_closed
        schedule theta hInterior⟩

/-- Joint non-LAN information theorem for the same concrete arbitrary-batch
protocol and all three rotationally invariant mixed-qubit losses. -/
theorem cumulativePauliPastMixedQubitInformation_core_closed
    (schedule : CumulativePauliPilotBatchSchedule)
    (theta : RLSVector 3) (hInterior : QubitOracle.blochNormSq theta < 1) :
    (forall k omega,
      QubitOracle.blochNormSq
        (cumulativePauliPastSafeInteriorController schedule k omega) < 1) /\
    (∀ᵐ omega ∂pauliPilotConsistencyMeasure theta,
      forall j : Fin 3,
        Tendsto
          (fun k => cumulativePauliPastSafeInteriorController
            schedule k omega j)
          atTop (nhds (theta j))) /\
    (∀ᵐ omega ∂pauliPilotConsistencyMeasure theta,
      BatchMatrixEntrywiseTendsto
        (cumulativePauliPastFullCanonicalBuresInformation
          schedule theta omega)
        (mixedBuresTarget theta)) /\
    (∀ᵐ omega ∂pauliPilotConsistencyMeasure theta,
      BatchMatrixEntrywiseTendsto
        (cumulativePauliPastFullFrobeniusTraceInformation
          schedule theta omega)
        (mixedFrobeniusTraceTarget theta)) := by
  exact
    ⟨fun k omega =>
        cumulativePauliPastSafeInteriorController_strictInterior
          schedule k omega,
      cumulativePauliPastSafeInteriorController_tendsto_ae_closed
        schedule theta hInterior,
      cumulativePauliPastFullCanonicalBuresInformation_tendsto_ae_closed
        schedule theta hInterior,
      cumulativePauliPastFullFrobeniusTraceInformation_tendsto_ae_closed
        schedule theta hInterior⟩

end

end QubitOracle.Paper
