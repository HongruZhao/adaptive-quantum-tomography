import QubitOracle.Paper.OneQubitGeneralScheduleAdaptiveBornProtocol
import QubitOracle.Paper.MixedScoreMoments
import QubitOracle.Paper.ProtocolRegularity
import QubitOracle.Paper.OneQubitRegularity

/-!
# Score primitives for the arbitrary predetermined-batch qubit protocol

This module works on the literal Ionescu--Tulcea path constructed in
`OneQubitGeneralScheduleAdaptiveBornProtocol`.  It contains no asymptotic or
external statistical input: all statements are pointwise identities for the
two Born outcomes.
-/

namespace QubitOracle.Paper

noncomputable section

/-- The concrete axis used for global shot `n` on an infinite realized path. -/
def generalScheduleActualAxis
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 → Real)
    (path : AdaptiveInfinitePath BinaryOutcome) (n : Nat) : Fin 3 → Real :=
  generalScheduleHistoryAxis schedule b n
    (adaptiveInfinitePathPrefix n path)

/-- Every actually selected axis is a projective unit Bloch axis. -/
theorem generalScheduleActualAxis_normSq
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 → Real)
    (path : AdaptiveInfinitePath BinaryOutcome) (n : Nat) :
    QubitOracle.blochNormSq (generalScheduleActualAxis schedule b path n) = 1 := by
  exact generalScheduleHistoryAxis_normSq schedule b n
    (adaptiveInfinitePathPrefix n path)

/-- At an interior mixed-qubit state, every selected binary Born experiment
has strictly positive Fisher denominator. -/
theorem generalScheduleActualProjection_sq_lt_one
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 → Real)
    (theta : OneQubitPhysicalParameter)
    (hInterior : QubitOracle.blochNormSq theta.1 < 1)
    (path : AdaptiveInfinitePath BinaryOutcome) (n : Nat) :
    QubitOracle.blochDot theta.1
        (generalScheduleActualAxis schedule b path n) ^ 2 < 1 := by
  calc
    QubitOracle.blochDot theta.1
          (generalScheduleActualAxis schedule b path n) ^ 2
        ≤ QubitOracle.blochNormSq theta.1 *
            QubitOracle.blochNormSq (generalScheduleActualAxis schedule b path n) :=
      blochDot_sq_le_normSq_mul_normSq theta.1
        (generalScheduleActualAxis schedule b path n)
    _ = QubitOracle.blochNormSq theta.1 := by
      rw [generalScheduleActualAxis_normSq]
      ring
    _ < 1 := hInterior

/-- The literal one-shot score vector evaluated at the true parameter. -/
def generalScheduleActualScoreVector
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 → Real)
    (theta : OneQubitPhysicalParameter)
    (path : AdaptiveInfinitePath BinaryOutcome) (n : Nat) :
    EuclideanSpace Real (Fin 3) :=
  mixedAxisScoreVector
    (QubitOracle.blochDot theta.1 (generalScheduleActualAxis schedule b path n))
    (generalScheduleActualAxis schedule b path n) (path n)

/-- The score vector before the next outcome is inserted. -/
def generalScheduleProspectiveScoreVector
    (theta : OneQubitPhysicalParameter) (axis : Fin 3 → Real)
    (y : BinaryOutcome) : EuclideanSpace Real (Fin 3) :=
  mixedAxisScoreVector (QubitOracle.blochDot theta.1 axis) axis y

/-- The concrete score is the prospective score at the predictable selected
axis and the observed outcome. -/
theorem generalScheduleActualScoreVector_eq
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 → Real)
    (theta : OneQubitPhysicalParameter)
    (path : AdaptiveInfinitePath BinaryOutcome) (n : Nat) :
    generalScheduleActualScoreVector schedule b theta path n =
      generalScheduleProspectiveScoreVector theta
        (generalScheduleActualAxis schedule b path n) (path n) := by
  rfl

/-- Uniform deterministic score envelope on a closed interior Bloch ball. -/
theorem generalScheduleProspectiveScoreVector_norm_le
    (theta : OneQubitPhysicalParameter) (axis : Fin 3 → Real)
    (hAxis : QubitOracle.blochNormSq axis ≤ 1)
    (s : Real) (hTheta : blochNorm theta.1 ≤ s) (hs : s < 1)
    (y : BinaryOutcome) :
    ‖generalScheduleProspectiveScoreVector theta axis y‖ ≤ (1 - s)⁻¹ := by
  apply mixedAxisScoreVector_norm_le
  · exact (abs_blochDot_le_blochNorm theta.1 axis hAxis).trans hTheta
  · exact hs
  · exact hAxis

/-- The same deterministic envelope for every score on the realized path. -/
theorem generalScheduleActualScoreVector_norm_le
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 → Real)
    (theta : OneQubitPhysicalParameter)
    (path : AdaptiveInfinitePath BinaryOutcome) (n : Nat)
    (s : Real) (hTheta : blochNorm theta.1 ≤ s) (hs : s < 1) :
    ‖generalScheduleActualScoreVector schedule b theta path n‖ ≤
      (1 - s)⁻¹ := by
  rw [generalScheduleActualScoreVector_eq]
  exact generalScheduleProspectiveScoreVector_norm_le theta
    (generalScheduleActualAxis schedule b path n)
    (generalScheduleActualAxis_normSq schedule b path n).le
    s hTheta hs (path n)

/-- Exact conditional centering of each score coordinate under the two Born
outcomes, before any probability-limit theorem is invoked. -/
theorem generalScheduleProspectiveScore_mean_zero
    (theta : OneQubitPhysicalParameter) (axis : Fin 3 → Real)
    (hRegular : QubitOracle.blochDot theta.1 axis ^ 2 < 1)
    (j : Fin 3) :
    binaryBornProbability (QubitOracle.blochDot theta.1 axis) .plus *
          generalScheduleProspectiveScoreVector theta axis .plus j +
        binaryBornProbability (QubitOracle.blochDot theta.1 axis) .minus *
          generalScheduleProspectiveScoreVector theta axis .minus j = 0 := by
  simpa [binaryBornProbability, BinaryOutcome.sign, sub_eq_add_neg,
    generalScheduleProspectiveScoreVector,
    mixedAxisScoreVector, binaryAxisScoreByOutcome,
    mixedAxisPlusScoreVector, mixedAxisMinusScoreVector,
    QubitOracle.binaryAxisPlusProbability,
    QubitOracle.binaryAxisMinusProbability] using
      (mixedAxisScore_mean_zero theta.1 axis hRegular j)

/-- Exact conditional score covariance: it is the one-shot adaptive Fisher
matrix, entry by entry. -/
theorem generalScheduleProspectiveScore_secondMoment_eq_fisher
    (theta : OneQubitPhysicalParameter) (axis : Fin 3 → Real)
    (hRegular : QubitOracle.blochDot theta.1 axis ^ 2 < 1)
    (i j : Fin 3) :
    binaryBornProbability (QubitOracle.blochDot theta.1 axis) .plus *
          generalScheduleProspectiveScoreVector theta axis .plus i *
          generalScheduleProspectiveScoreVector theta axis .plus j +
        binaryBornProbability (QubitOracle.blochDot theta.1 axis) .minus *
          generalScheduleProspectiveScoreVector theta axis .minus i *
          generalScheduleProspectiveScoreVector theta axis .minus j =
      QubitOracle.mixedAxisFisher theta.1 axis i j := by
  simpa [binaryBornProbability, BinaryOutcome.sign, sub_eq_add_neg,
    generalScheduleProspectiveScoreVector,
    mixedAxisScoreVector, binaryAxisScoreByOutcome,
    mixedAxisPlusScoreVector, mixedAxisMinusScoreVector,
    QubitOracle.binaryAxisPlusProbability,
    QubitOracle.binaryAxisMinusProbability] using
      (mixedAxisScore_secondMoment_eq_fisher theta.1 axis hRegular i j)

/-- Concrete pathwise score centering at every selected axis. -/
theorem generalScheduleActualScore_mean_zero
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 → Real)
    (theta : OneQubitPhysicalParameter)
    (hInterior : QubitOracle.blochNormSq theta.1 < 1)
    (path : AdaptiveInfinitePath BinaryOutcome) (n : Nat) (j : Fin 3) :
    binaryBornProbability
          (QubitOracle.blochDot theta.1
            (generalScheduleActualAxis schedule b path n)) .plus *
          generalScheduleProspectiveScoreVector theta
            (generalScheduleActualAxis schedule b path n) .plus j +
        binaryBornProbability
          (QubitOracle.blochDot theta.1
            (generalScheduleActualAxis schedule b path n)) .minus *
          generalScheduleProspectiveScoreVector theta
            (generalScheduleActualAxis schedule b path n) .minus j = 0 := by
  exact generalScheduleProspectiveScore_mean_zero theta
    (generalScheduleActualAxis schedule b path n)
    (generalScheduleActualProjection_sq_lt_one
      schedule b theta hInterior path n) j

/-- Concrete pathwise score covariance equals the selected-axis Fisher
information at every shot. -/
theorem generalScheduleActualScore_secondMoment_eq_fisher
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 → Real)
    (theta : OneQubitPhysicalParameter)
    (hInterior : QubitOracle.blochNormSq theta.1 < 1)
    (path : AdaptiveInfinitePath BinaryOutcome) (n : Nat) (i j : Fin 3) :
    binaryBornProbability
          (QubitOracle.blochDot theta.1
            (generalScheduleActualAxis schedule b path n)) .plus *
          generalScheduleProspectiveScoreVector theta
            (generalScheduleActualAxis schedule b path n) .plus i *
          generalScheduleProspectiveScoreVector theta
            (generalScheduleActualAxis schedule b path n) .plus j +
        binaryBornProbability
          (QubitOracle.blochDot theta.1
            (generalScheduleActualAxis schedule b path n)) .minus *
          generalScheduleProspectiveScoreVector theta
            (generalScheduleActualAxis schedule b path n) .minus i *
          generalScheduleProspectiveScoreVector theta
            (generalScheduleActualAxis schedule b path n) .minus j =
      QubitOracle.mixedAxisFisher theta.1
        (generalScheduleActualAxis schedule b path n) i j := by
  exact generalScheduleProspectiveScore_secondMoment_eq_fisher theta
    (generalScheduleActualAxis schedule b path n)
    (generalScheduleActualProjection_sq_lt_one
      schedule b theta hInterior path n) i j

end

end QubitOracle.Paper
