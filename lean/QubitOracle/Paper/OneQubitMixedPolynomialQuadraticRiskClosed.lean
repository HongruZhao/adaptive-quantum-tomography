import QubitOracle.Paper.OneQubitMixedFiniteInfinitePilotIntegrationBridge
import QubitOracle.Paper.OneQubitMixedGoodBranchUniformEnvelopeClosed
import QubitOracle.Paper.OneQubitMixedPolynomialBadBranchRisk

/-!
# Polynomial two-stage mixed-qubit quadratic risk

This file closes the deterministic/probabilistic reduction for the concrete
nonzero interior mixed-qubit polynomial protocol.  The loss is the local
quadratic Bures metric already used by `mixedFrameConditionalScaledQuadraticRisk`;
it is not the exact nonlinear Bures loss.

The exact-cycle final stage has `q = polynomialFinalShots n` observations in
each of three orthonormal frame directions, so its sample size and the scaling
proved first below are both `3 * q`.  We separately add the polynomial pilot
sample and prove that total-observation scaling has the same limit.

The only literature-relative premise retained here is the existing finite
Pauli-pilot Hoeffding contract.  No joint-law or uniform-integrability premise
is assumed: the finite/infinite integration bridge supplies the former, while
the frame-uniform bound below supplies the latter.
-/

noncomputable section

open scoped BigOperators ENNReal Topology
open Filter MeasureTheory Set

namespace QubitOracle.Paper

local instance mixedPolynomialQuadraticConsistencyPathMeasurableSpace (q : ℕ) :
    MeasurableSpace (PauliPilotPath q) :=
  pauliPilotConsistencyPathMeasurableSpace q

private theorem mixedPolynomialFiniteCoordinateObservable_measurable
    (n : ℕ)
    (f : PauliPilotPath (Nat.succ (polynomialPilotIndex n)) → ℝ≥0∞) :
    Measurable (fun omega : PauliPilotConsistencySampleSpace =>
      f (omega (polynomialPilotIndex n))) := by
  exact Measurable.of_discrete.comp
    (measurable_pi_apply (polynomialPilotIndex n))

private theorem mixedPolynomialPilotBadEvent_measurable_forConsistencyMeasure
    (theta : RLSVector 3) (n : ℕ) :
    MeasurableSet (polynomialPilotBadEvent theta n) := by
  have hCoordinateEvent (j : Fin 3) :
      MeasurableSet
        {omega : PauliPilotConsistencySampleSpace |
          polynomialPilotThreshold n ≤
            |polynomialPilotEstimator n omega j - theta j|} := by
    let E : Set (PauliPilotPath (Nat.succ (polynomialPilotIndex n))) :=
      {path |
        polynomialPilotThreshold n ≤ |pauliPilotEstimate path j - theta j|}
    have hE : MeasurableSet E := MeasurableSet.of_discrete
    have hEval : Measurable
        (fun omega : PauliPilotConsistencySampleSpace =>
          omega (polynomialPilotIndex n)) :=
      measurable_pi_apply _
    have hPreimage : MeasurableSet
        ((fun omega : PauliPilotConsistencySampleSpace =>
          omega (polynomialPilotIndex n)) ⁻¹' E) :=
      hEval hE
    simpa [E, polynomialPilotEstimator, pauliPilotConsistencyEstimator] using
      hPreimage
  unfold polynomialPilotBadEvent QubitOracle.coordinateDeltaBadEvent
  have hUnion :
      {omega : PauliPilotConsistencySampleSpace |
        ∃ j : Fin 3,
          polynomialPilotThreshold n ≤
            |polynomialPilotEstimator n omega j - theta j|} =
        ⋃ j : Fin 3,
          {omega : PauliPilotConsistencySampleSpace |
            polynomialPilotThreshold n ≤
              |polynomialPilotEstimator n omega j - theta j|} := by
    ext omega
    simp
  rw [hUnion]
  exact MeasurableSet.iUnion hCoordinateEvent

/-- A truth-only upper bound for every orthonormal-frame conditional risk. -/
def mixedInteriorFrameScaledQuadraticRiskBound
    (theta : Fin 3 → ℝ) : ℝ :=
  (3 / 4 : ℝ) *
    (3 + blochNormSq theta / (1 - blochNormSq theta))

/-- Orthogonal frame coordinates preserve the Bloch squared norm. -/
theorem qubitFrameCoordinates_blochNormSq_of_orthonormal
    (theta : Fin 3 → ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : MixedFrameOrthonormal R) :
    blochNormSq (qubitFrameCoordinates R theta) = blochNormSq theta := by
  let z := qubitFrameCoordinates R theta
  have hReconstruct : mixedFrameReconstruct R z = theta := by
    simpa [z] using mixedFrameReconstruct_coordinates R hR theta
  have hNorm :
      blochNormSq (mixedFrameReconstruct R z) = blochNormSq z := by
    simpa using mixedFrameReconstruct_normSq R hR z
  calc
    blochNormSq z = blochNormSq (mixedFrameReconstruct R z) := hNorm.symm
    _ = blochNormSq theta := congrArg blochNormSq hReconstruct

private theorem mixed_blochNormSq_nonnegative (x : Fin 3 → ℝ) :
    0 ≤ blochNormSq x := by
  unfold blochNormSq
  exact Finset.sum_nonneg fun j _ => sq_nonneg (x j)

private theorem qubitFrameCoordinate_sq_le_blochNormSq
    (theta : Fin 3 → ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : MixedFrameOrthonormal R) (j : Fin 3) :
    (qubitFrameCoordinates R theta j) ^ 2 ≤ blochNormSq theta := by
  rw [← qubitFrameCoordinates_blochNormSq_of_orthonormal theta R hR]
  unfold blochNormSq
  exact Finset.single_le_sum
    (fun k _ => sq_nonneg (qubitFrameCoordinates R theta k))
    (Finset.mem_univ j)

private theorem qubitFrame_one_minus_sq_sum_nonnegative
    (theta : Fin 3 → ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : MixedFrameOrthonormal R)
    (hInterior : blochNormSq theta < 1) :
    0 ≤ ∑ j : Fin 3, (1 - (qubitFrameCoordinates R theta j) ^ 2) := by
  apply Finset.sum_nonneg
  intro j _
  have hj := qubitFrameCoordinate_sq_le_blochNormSq theta R hR j
  linarith

private theorem qubitFrame_one_minus_sq_sum_le_three
    (theta : Fin 3 → ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ) :
    (∑ j : Fin 3, (1 - (qubitFrameCoordinates R theta j) ^ 2)) ≤ 3 := by
  calc
    (∑ j : Fin 3, (1 - (qubitFrameCoordinates R theta j) ^ 2))
        ≤ ∑ _j : Fin 3, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro j _
          nlinarith [sq_nonneg (qubitFrameCoordinates R theta j)]
    _ = 3 := by norm_num

private theorem qubitFrame_weighted_sq_sum_nonnegative
    (theta : Fin 3 → ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : MixedFrameOrthonormal R)
    (hInterior : blochNormSq theta < 1) :
    0 ≤ ∑ j : Fin 3,
      (qubitFrameCoordinates R theta j) ^ 2 *
        (1 - (qubitFrameCoordinates R theta j) ^ 2) := by
  apply Finset.sum_nonneg
  intro j _
  have hj := qubitFrameCoordinate_sq_le_blochNormSq theta R hR j
  exact mul_nonneg (sq_nonneg _) (by linarith)

private theorem qubitFrame_weighted_sq_sum_le_blochNormSq
    (theta : Fin 3 → ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : MixedFrameOrthonormal R) :
    (∑ j : Fin 3,
      (qubitFrameCoordinates R theta j) ^ 2 *
        (1 - (qubitFrameCoordinates R theta j) ^ 2))
      ≤ blochNormSq theta := by
  calc
    (∑ j : Fin 3,
      (qubitFrameCoordinates R theta j) ^ 2 *
        (1 - (qubitFrameCoordinates R theta j) ^ 2))
        ≤ ∑ j : Fin 3, (qubitFrameCoordinates R theta j) ^ 2 := by
          apply Finset.sum_le_sum
          intro j _
          nlinarith [sq_nonneg (qubitFrameCoordinates R theta j)]
    _ = blochNormSq (qubitFrameCoordinates R theta) := by
      simp [blochNormSq]
    _ = blochNormSq theta :=
      qubitFrameCoordinates_blochNormSq_of_orthonormal theta R hR

/-- The truth-only frame bound is finite and nonnegative at an interior truth. -/
theorem mixedInteriorFrameScaledQuadraticRiskBound_nonnegative
    (theta : Fin 3 → ℝ) (hInterior : blochNormSq theta < 1) :
    0 ≤ mixedInteriorFrameScaledQuadraticRiskBound theta := by
  have hNorm : 0 ≤ blochNormSq theta := mixed_blochNormSq_nonnegative theta
  have hDen : 0 ≤ 1 - blochNormSq theta := by linarith
  unfold mixedInteriorFrameScaledQuadraticRiskBound
  exact mul_nonneg (by norm_num) (add_nonneg (by norm_num) (div_nonneg hNorm hDen))

/-- Uniform conditional-risk bound for every orthonormal frame and every `q > 0`. -/
theorem mixedFrameConditionalScaledQuadraticRisk_le_interiorBound
    {q : ℕ} (hq : 0 < q) (theta : Fin 3 → ℝ)
    (hInterior : blochNormSq theta < 1)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : MixedFrameOrthonormal R) :
    mixedFrameConditionalScaledQuadraticRisk (q := q) theta R ≤
      mixedInteriorFrameScaledQuadraticRiskBound theta := by
  have hDen : 0 < 1 - blochNormSq theta := by linarith
  have hFirst := qubitFrame_one_minus_sq_sum_le_three theta R
  have hSecond := qubitFrame_weighted_sq_sum_le_blochNormSq theta R hR
  have hSecondDiv :
      (∑ j : Fin 3,
          (qubitFrameCoordinates R theta j) ^ 2 *
            (1 - (qubitFrameCoordinates R theta j) ^ 2)) /
            (1 - blochNormSq theta)
        ≤ blochNormSq theta / (1 - blochNormSq theta) :=
    div_le_div_of_nonneg_right hSecond hDen.le
  rw [mixedFrameConditionalScaledQuadraticRisk_eq_closedForm
    (q := q) hq theta hInterior R hR]
  unfold mixedFrameScaledQuadraticRiskClosedForm
  unfold mixedInteriorFrameScaledQuadraticRiskBound
  dsimp only
  nlinarith

/-- Conditional quadratic risk is nonnegative in every orthonormal frame. -/
theorem mixedFrameConditionalScaledQuadraticRisk_nonnegative_closed
    {q : ℕ} (hq : 0 < q) (theta : Fin 3 → ℝ)
    (hInterior : blochNormSq theta < 1)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : MixedFrameOrthonormal R) :
    0 ≤ mixedFrameConditionalScaledQuadraticRisk (q := q) theta R := by
  have hDen : 0 ≤ 1 - blochNormSq theta := by linarith
  have hFirst :=
    qubitFrame_one_minus_sq_sum_nonnegative theta R hR hInterior
  have hSecond :=
    qubitFrame_weighted_sq_sum_nonnegative theta R hR hInterior
  rw [mixedFrameConditionalScaledQuadraticRisk_eq_closedForm
    (q := q) hq theta hInterior R hR]
  unfold mixedFrameScaledQuadraticRiskClosedForm
  dsimp only
  exact mul_nonneg (by norm_num)
    (add_nonneg hFirst (div_nonneg hSecond hDen))

/-- A truth-only envelope for absolute deviation from the oracle value `9/4`. -/
theorem mixedFrameConditionalScaledQuadraticRisk_abs_sub_oracle_le
    {q : ℕ} (hq : 0 < q) (theta : Fin 3 → ℝ)
    (hInterior : blochNormSq theta < 1)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : MixedFrameOrthonormal R) :
    |mixedFrameConditionalScaledQuadraticRisk (q := q) theta R - 9 / 4| ≤
      mixedInteriorFrameScaledQuadraticRiskBound theta + 9 / 4 := by
  have hLower :=
    mixedFrameConditionalScaledQuadraticRisk_nonnegative_closed
      hq theta hInterior R hR
  have hUpper :=
    mixedFrameConditionalScaledQuadraticRisk_le_interiorBound
      hq theta hInterior R hR
  have hBoundNonnegative :=
    mixedInteriorFrameScaledQuadraticRiskBound_nonnegative theta hInterior
  rw [abs_le]
  constructor <;> linarith

/-- The exact-cycle final allocation used throughout this file. -/
def mixedPolynomialQuadraticQFinal (n : ℕ) : ℕ :=
  polynomialFinalShots n

/-- Every polynomial final allocation is positive. -/
theorem mixedPolynomialQuadraticQFinal_pos (n : ℕ) :
    0 < mixedPolynomialQuadraticQFinal n := by
  unfold mixedPolynomialQuadraticQFinal polynomialFinalShots polynomialScheduleM
  positivity

/-- The explicit finite-pilot average of final-stage scaled quadratic risk.
Its scaling is `3 * polynomialFinalShots n`, not pilot-plus-final sample size. -/
def mixedPolynomialFinalStageExpectedScaledQuadraticRisk
    (theta b : Fin 3 → ℝ) (n : ℕ) : ℝ≥0∞ :=
  mixedPolynomialFinitePilotAverageScaledRisk
    theta b mixedPolynomialQuadraticQFinal n

/-- The same expected risk represented on the common infinite pilot space. -/
def mixedPolynomialFinalStageRiskIntegral
    (theta b : Fin 3 → ℝ) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ omega,
    ENNReal.ofReal
      (mixedFrameConditionalScaledQuadraticRisk
        (q := mixedPolynomialQuadraticQFinal n) theta
        (mixedPilotSelectedLocalFrame b
          (polynomialPilotEstimator n omega)))
    ∂pauliPilotConsistencyMeasure theta

/-- Integrated absolute deviation from the oracle constant. -/
def mixedPolynomialFinalStageDeviationIntegral
    (theta b : Fin 3 → ℝ) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ omega,
    ENNReal.ofReal
      |mixedFrameConditionalScaledQuadraticRisk
        (q := mixedPolynomialQuadraticQFinal n) theta
        (mixedPilotSelectedLocalFrame b
          (polynomialPilotEstimator n omega)) - 9 / 4|
    ∂pauliPilotConsistencyMeasure theta

private theorem mixedPolynomialPilotFrame_risk_nonnegative
    (theta b : Fin 3 → ℝ) (hInterior : blochNormSq theta < 1)
    (n : ℕ) (omega) :
    0 ≤ mixedFrameConditionalScaledQuadraticRisk
      (q := mixedPolynomialQuadraticQFinal n) theta
      (mixedPilotSelectedLocalFrame b (polynomialPilotEstimator n omega)) := by
  apply mixedFrameConditionalScaledQuadraticRisk_nonnegative_closed
    (mixedPolynomialQuadraticQFinal_pos n) theta hInterior
  exact mixedPilotSelectedLocalFrame_orthonormal _ _

private theorem mixedPolynomialPilotFrame_deviation_envelope
    (theta b : Fin 3 → ℝ) (hInterior : blochNormSq theta < 1)
    (n : ℕ) (omega) :
    ENNReal.ofReal
      |mixedFrameConditionalScaledQuadraticRisk
        (q := mixedPolynomialQuadraticQFinal n) theta
        (mixedPilotSelectedLocalFrame b
          (polynomialPilotEstimator n omega)) - 9 / 4| ≤
      ENNReal.ofReal
        (mixedInteriorFrameScaledQuadraticRiskBound theta + 9 / 4) := by
  apply ENNReal.ofReal_le_ofReal
  apply mixedFrameConditionalScaledQuadraticRisk_abs_sub_oracle_le
    (mixedPolynomialQuadraticQFinal_pos n) theta hInterior
  exact mixedPilotSelectedLocalFrame_orthonormal _ _

/-- The finite pilot sum and the common-space integral are exactly identical. -/
theorem mixedPolynomialFinalStageExpectedScaledQuadraticRisk_eq_integral
    (theta b : Fin 3 → ℝ)
    (hphysical : PauliPilotPhysicalBloch theta) (n : ℕ) :
    mixedPolynomialFinalStageExpectedScaledQuadraticRisk theta b n =
      mixedPolynomialFinalStageRiskIntegral theta b n := by
  simpa [mixedPolynomialFinalStageExpectedScaledQuadraticRisk,
    mixedPolynomialFinalStageRiskIntegral,
    mixedPolynomialQuadraticQFinal,
    mixedPolynomialPilotConditionalScaledLoss] using
    (mixedPolynomialFinitePilotAverageScaledRisk_eq_lintegral
      theta b mixedPolynomialQuadraticQFinal hphysical n)

/-- The explicit finite exact-cycle row supplies the final joint-law premise;
this is not an assumed coupling. -/
theorem mixedPolynomialFinalStageExpectedScaledQuadraticRisk_jointLaw
    (theta b : Fin 3 → ℝ)
    (hphysical : PauliPilotPhysicalBloch theta) :
    MixedPilotFinalJointLawPremise theta b mixedPolynomialQuadraticQFinal
      (mixedPolynomialFinalStageExpectedScaledQuadraticRisk theta b) := by
  change MixedPilotFinalJointLawPremise theta b mixedPolynomialQuadraticQFinal
    (mixedPolynomialFinitePilotAverageScaledRisk
      theta b mixedPolynomialQuadraticQFinal)
  exact mixedPolynomialFinitePilotAverage_finalJointLawPremise
    theta b mixedPolynomialQuadraticQFinal hphysical

private theorem mixedPolynomialRisk_ofReal_le_oracle_add_deviation
    (theta b : Fin 3 → ℝ) (hInterior : blochNormSq theta < 1)
    (n : ℕ) (omega) :
    ENNReal.ofReal
      (mixedFrameConditionalScaledQuadraticRisk
        (q := mixedPolynomialQuadraticQFinal n) theta
        (mixedPilotSelectedLocalFrame b
          (polynomialPilotEstimator n omega))) ≤
      ENNReal.ofReal (9 / 4 : ℝ) +
        ENNReal.ofReal
          |mixedFrameConditionalScaledQuadraticRisk
            (q := mixedPolynomialQuadraticQFinal n) theta
            (mixedPilotSelectedLocalFrame b
              (polynomialPilotEstimator n omega)) - 9 / 4| := by
  let risk := mixedFrameConditionalScaledQuadraticRisk
    (q := mixedPolynomialQuadraticQFinal n) theta
    (mixedPilotSelectedLocalFrame b (polynomialPilotEstimator n omega))
  have hReal : risk ≤ 9 / 4 + |risk - 9 / 4| := by
    have hAbs := le_abs_self (risk - 9 / 4)
    linarith
  calc
    ENNReal.ofReal risk ≤ ENNReal.ofReal (9 / 4 + |risk - 9 / 4|) :=
      ENNReal.ofReal_le_ofReal hReal
    _ = ENNReal.ofReal (9 / 4 : ℝ) + ENNReal.ofReal |risk - 9 / 4| := by
      rw [ENNReal.ofReal_add (by norm_num) (abs_nonneg _)]

private theorem mixedPolynomialOracle_le_risk_ofReal_add_deviation
    (theta b : Fin 3 → ℝ) (hInterior : blochNormSq theta < 1)
    (n : ℕ) (omega) :
    ENNReal.ofReal (9 / 4 : ℝ) ≤
      ENNReal.ofReal
        (mixedFrameConditionalScaledQuadraticRisk
          (q := mixedPolynomialQuadraticQFinal n) theta
          (mixedPilotSelectedLocalFrame b
            (polynomialPilotEstimator n omega))) +
      ENNReal.ofReal
        |mixedFrameConditionalScaledQuadraticRisk
          (q := mixedPolynomialQuadraticQFinal n) theta
          (mixedPilotSelectedLocalFrame b
            (polynomialPilotEstimator n omega)) - 9 / 4| := by
  let risk := mixedFrameConditionalScaledQuadraticRisk
    (q := mixedPolynomialQuadraticQFinal n) theta
    (mixedPilotSelectedLocalFrame b (polynomialPilotEstimator n omega))
  have hRisk : 0 ≤ risk := by
    dsimp [risk]
    exact mixedPolynomialPilotFrame_risk_nonnegative theta b hInterior n omega
  have hReal : (9 / 4 : ℝ) ≤ risk + |risk - 9 / 4| := by
    have hAbs := neg_le_abs (risk - 9 / 4)
    linarith
  calc
    ENNReal.ofReal (9 / 4 : ℝ) ≤ ENNReal.ofReal (risk + |risk - 9 / 4|) :=
      ENNReal.ofReal_le_ofReal hReal
    _ = ENNReal.ofReal risk + ENNReal.ofReal |risk - 9 / 4| := by
      rw [ENNReal.ofReal_add hRisk (abs_nonneg _)]

/-- The closed good-event envelope plus the global frame bound make the
integrated absolute deviation tend to zero. -/
theorem mixedPolynomialFinalStageDeviationIntegral_tendsto_zero
    (theta b : Fin 3 → ℝ)
    (hPositive : 0 < blochNormSq theta)
    (hInterior : blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hphysical : PauliPilotPhysicalBloch theta)
    (hHoeffding :
      PauliPilotConsistencyHoeffdingContracts theta hphysical) :
    Tendsto (mixedPolynomialFinalStageDeviationIntegral theta b)
      atTop (nhds 0) := by
  letI : IsProbabilityMeasure (pauliPilotConsistencyMeasure theta) :=
    pauliPilotConsistencyMeasure_isProbability theta hphysical
  obtain ⟨envelope, hEnvelopeZero, hGood⟩ :=
    mixedPilotGoodBranchUniformFrameContinuityPremise_closed
      b theta mixedPolynomialQuadraticQFinal
      mixedPolynomialQuadraticQFinal_pos hPositive hInterior hSeed
  let deviationBound : ℝ≥0∞ :=
    ENNReal.ofReal
      (mixedInteriorFrameScaledQuadraticRiskBound theta + 9 / 4)
  have hPointwise : ∀ᶠ n in atTop, ∀ omega,
      ENNReal.ofReal
        |mixedFrameConditionalScaledQuadraticRisk
          (q := mixedPolynomialQuadraticQFinal n) theta
          (mixedPilotSelectedLocalFrame b
            (polynomialPilotEstimator n omega)) - 9 / 4| ≤
        envelope n +
          (polynomialPilotBadEvent theta n).indicator
            (fun _ => deviationBound) omega := by
    filter_upwards [hGood] with n hn
    intro omega
    by_cases hBad : omega ∈ polynomialPilotBadEvent theta n
    · simp only [Set.indicator_of_mem hBad]
      calc
        ENNReal.ofReal
            |mixedFrameConditionalScaledQuadraticRisk
              (q := mixedPolynomialQuadraticQFinal n) theta
              (mixedPilotSelectedLocalFrame b
                (polynomialPilotEstimator n omega)) - 9 / 4|
            ≤ deviationBound :=
          mixedPolynomialPilotFrame_deviation_envelope
            theta b hInterior n omega
        _ ≤ envelope n + deviationBound :=
          le_add_of_nonneg_left bot_le
    · simpa [hBad] using hn omega hBad
  have hIntegralUpper : ∀ᶠ n in atTop,
      mixedPolynomialFinalStageDeviationIntegral theta b n ≤
        envelope n + deviationBound *
          pauliPilotConsistencyMeasure theta
            (polynomialPilotBadEvent theta n) := by
    filter_upwards [hPointwise] with n hn
    calc
      mixedPolynomialFinalStageDeviationIntegral theta b n
          ≤ ∫⁻ omega,
              envelope n +
                (polynomialPilotBadEvent theta n).indicator
                  (fun _ => deviationBound) omega
              ∂pauliPilotConsistencyMeasure theta :=
        lintegral_mono hn
      _ = (∫⁻ _omega, envelope n ∂pauliPilotConsistencyMeasure theta) +
            ∫⁻ omega,
              (polynomialPilotBadEvent theta n).indicator
                (fun _ => deviationBound) omega
              ∂pauliPilotConsistencyMeasure theta :=
        MeasureTheory.lintegral_add_left measurable_const _
      _ = envelope n + deviationBound *
            pauliPilotConsistencyMeasure theta
              (polynomialPilotBadEvent theta n) := by
        have hIndicator :
            (∫⁻ omega,
              (polynomialPilotBadEvent theta n).indicator
                (fun _ => deviationBound) omega
              ∂pauliPilotConsistencyMeasure theta) =
              deviationBound * pauliPilotConsistencyMeasure theta
                (polynomialPilotBadEvent theta n) :=
          MeasureTheory.lintegral_indicator_const
            (μ := pauliPilotConsistencyMeasure theta)
            (mixedPolynomialPilotBadEvent_measurable_forConsistencyMeasure
              theta n) deviationBound
        rw [hIndicator]
        simp
  have hBadProbability :
      Tendsto
        (fun n => pauliPilotConsistencyMeasure theta
          (polynomialPilotBadEvent theta n)) atTop (nhds 0) :=
    polynomialPilot_badEventProbability_tendsto_zero
      theta hphysical hHoeffding
  have hDeviationBoundFinite : deviationBound ≠ ⊤ := by
    exact ENNReal.ofReal_ne_top
  have hBadScaled :
      Tendsto
        (fun n => deviationBound *
          pauliPilotConsistencyMeasure theta
            (polynomialPilotBadEvent theta n)) atTop (nhds 0) := by
    have hContinuous :=
      (ENNReal.continuousAt_const_mul
        (a := deviationBound) (b := 0)
        (Or.inl hDeviationBoundFinite)).tendsto
    simpa [Function.comp_def] using
      hContinuous.comp hBadProbability
  have hMajorant :
      Tendsto
        (fun n => envelope n + deviationBound *
          pauliPilotConsistencyMeasure theta
            (polynomialPilotBadEvent theta n)) atTop (nhds 0) := by
    simpa using hEnvelopeZero.add hBadScaled
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hMajorant
    (Eventually.of_forall fun _ => bot_le) hIntegralUpper

/-- The risk integral is trapped above by the oracle constant plus integrated
absolute deviation. -/
theorem mixedPolynomialFinalStageRiskIntegral_le_oracle_add_deviation
    (theta b : Fin 3 → ℝ)
    (hInterior : blochNormSq theta < 1)
    (hphysical : PauliPilotPhysicalBloch theta) (n : ℕ) :
    mixedPolynomialFinalStageRiskIntegral theta b n ≤
      ENNReal.ofReal (9 / 4 : ℝ) +
        mixedPolynomialFinalStageDeviationIntegral theta b n := by
  letI : IsProbabilityMeasure (pauliPilotConsistencyMeasure theta) :=
    pauliPilotConsistencyMeasure_isProbability theta hphysical
  calc
    mixedPolynomialFinalStageRiskIntegral theta b n
        ≤ ∫⁻ omega,
            ENNReal.ofReal (9 / 4 : ℝ) +
              ENNReal.ofReal
                |mixedFrameConditionalScaledQuadraticRisk
                  (q := mixedPolynomialQuadraticQFinal n) theta
                  (mixedPilotSelectedLocalFrame b
                    (polynomialPilotEstimator n omega)) - 9 / 4|
            ∂pauliPilotConsistencyMeasure theta :=
      lintegral_mono
        (mixedPolynomialRisk_ofReal_le_oracle_add_deviation
          theta b hInterior n)
    _ = (∫⁻ _omega, ENNReal.ofReal (9 / 4 : ℝ)
            ∂pauliPilotConsistencyMeasure theta) +
          mixedPolynomialFinalStageDeviationIntegral theta b n :=
      MeasureTheory.lintegral_add_left measurable_const _
    _ = ENNReal.ofReal (9 / 4 : ℝ) +
          mixedPolynomialFinalStageDeviationIntegral theta b n := by simp

/-- Conversely, the oracle constant is bounded by the risk integral plus the
same integrated absolute deviation. -/
theorem mixedPolynomial_oracle_le_FinalStageRiskIntegral_add_deviation
    (theta b : Fin 3 → ℝ)
    (hInterior : blochNormSq theta < 1)
    (hphysical : PauliPilotPhysicalBloch theta) (n : ℕ) :
    ENNReal.ofReal (9 / 4 : ℝ) ≤
      mixedPolynomialFinalStageRiskIntegral theta b n +
        mixedPolynomialFinalStageDeviationIntegral theta b n := by
  letI : IsProbabilityMeasure (pauliPilotConsistencyMeasure theta) :=
    pauliPilotConsistencyMeasure_isProbability theta hphysical
  have hRiskMeasurable :
      Measurable (fun omega : PauliPilotConsistencySampleSpace =>
        ENNReal.ofReal
          (mixedFrameConditionalScaledQuadraticRisk
            (q := mixedPolynomialQuadraticQFinal n) theta
            (mixedPilotSelectedLocalFrame b
              (polynomialPilotEstimator n omega)))) :=
    by
      simpa [polynomialPilotEstimator, pauliPilotConsistencyEstimator] using
        (mixedPolynomialFiniteCoordinateObservable_measurable n
          (fun path => ENNReal.ofReal
        (mixedFrameConditionalScaledQuadraticRisk
          (q := mixedPolynomialQuadraticQFinal n) theta
          (mixedPilotSelectedLocalFrame b (pauliPilotEstimate path)))))
  calc
    ENNReal.ofReal (9 / 4 : ℝ)
        = ∫⁻ _omega, ENNReal.ofReal (9 / 4 : ℝ)
            ∂pauliPilotConsistencyMeasure theta := by simp
    _ ≤ ∫⁻ omega,
          ENNReal.ofReal
            (mixedFrameConditionalScaledQuadraticRisk
              (q := mixedPolynomialQuadraticQFinal n) theta
              (mixedPilotSelectedLocalFrame b
                (polynomialPilotEstimator n omega))) +
          ENNReal.ofReal
            |mixedFrameConditionalScaledQuadraticRisk
              (q := mixedPolynomialQuadraticQFinal n) theta
              (mixedPilotSelectedLocalFrame b
                (polynomialPilotEstimator n omega)) - 9 / 4|
          ∂pauliPilotConsistencyMeasure theta :=
      lintegral_mono
        (mixedPolynomialOracle_le_risk_ofReal_add_deviation
          theta b hInterior n)
    _ = mixedPolynomialFinalStageRiskIntegral theta b n +
          mixedPolynomialFinalStageDeviationIntegral theta b n :=
      MeasureTheory.lintegral_add_left hRiskMeasurable _

/-- Common-space expected final-stage scaled quadratic risk tends to `9/4`. -/
theorem mixedPolynomialFinalStageRiskIntegral_tendsto_nine_fourths
    (theta b : Fin 3 → ℝ)
    (hPositive : 0 < blochNormSq theta)
    (hInterior : blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hphysical : PauliPilotPhysicalBloch theta)
    (hHoeffding :
      PauliPilotConsistencyHoeffdingContracts theta hphysical) :
    Tendsto (mixedPolynomialFinalStageRiskIntegral theta b)
      atTop (nhds (ENNReal.ofReal (9 / 4 : ℝ))) := by
  let a : ℝ≥0∞ := ENNReal.ofReal (9 / 4 : ℝ)
  have hDeviation :=
    mixedPolynomialFinalStageDeviationIntegral_tendsto_zero
      theta b hPositive hInterior hSeed hphysical hHoeffding
  have hUpper : ∀ᶠ n in atTop,
      mixedPolynomialFinalStageRiskIntegral theta b n ≤
        a + mixedPolynomialFinalStageDeviationIntegral theta b n :=
    Eventually.of_forall fun n =>
      mixedPolynomialFinalStageRiskIntegral_le_oracle_add_deviation
        theta b hInterior hphysical n
  have hTargetUpper : ∀ᶠ n in atTop,
      a ≤ mixedPolynomialFinalStageRiskIntegral theta b n +
        mixedPolynomialFinalStageDeviationIntegral theta b n :=
    Eventually.of_forall fun n =>
      mixedPolynomial_oracle_le_FinalStageRiskIntegral_add_deviation
        theta b hInterior hphysical n
  have haPositive : (0 : ℝ≥0∞) < a := by
    norm_num [a]
  have hDeviationLe : ∀ᶠ n in atTop,
      mixedPolynomialFinalStageDeviationIntegral theta b n ≤ a := by
    exact ((tendsto_order.1 hDeviation).2 a haPositive).mono
      (fun _ hn => le_of_lt hn)
  have hLower : ∀ᶠ n in atTop,
      a - mixedPolynomialFinalStageDeviationIntegral theta b n ≤
        mixedPolynomialFinalStageRiskIntegral theta b n := by
    filter_upwards [hDeviationLe, hTargetUpper] with n hDn hTarget
    exact tsub_le_iff_right.2 (by simpa [add_comm] using hTarget)
  have haFinite : a ≠ ⊤ := by
    exact ENNReal.ofReal_ne_top
  have hLowerLimit :
      Tendsto
        (fun n => a - mixedPolynomialFinalStageDeviationIntegral theta b n)
        atTop (nhds a) := by
    have hSub : Tendsto (fun x : ℝ≥0∞ => a - x) (nhds 0) (nhds a) := by
      simpa using (ENNReal.continuous_sub_left haFinite).tendsto (0 : ℝ≥0∞)
    exact hSub.comp hDeviation
  have hUpperLimit :
      Tendsto
        (fun n => a + mixedPolynomialFinalStageDeviationIntegral theta b n)
        atTop (nhds a) := by
    simpa using tendsto_const_nhds.add hDeviation
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hLowerLimit hUpperLimit hLower hUpper

/-- Concrete finite-row endpoint.  The expectation is the explicit pilot sum
and final exact-cycle product law, scaled by the final-stage count `3q`. -/
theorem mixedPolynomialFinalStageExpectedScaledQuadraticRisk_tendsto_nine_fourths
    (theta b : Fin 3 → ℝ)
    (hPositive : 0 < blochNormSq theta)
    (hInterior : blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hphysical : PauliPilotPhysicalBloch theta)
    (hHoeffding :
      PauliPilotConsistencyHoeffdingContracts theta hphysical) :
    Tendsto (mixedPolynomialFinalStageExpectedScaledQuadraticRisk theta b)
      atTop (nhds (ENNReal.ofReal (9 / 4 : ℝ))) := by
  apply (mixedPolynomialFinalStageRiskIntegral_tendsto_nine_fourths
    theta b hPositive hInterior hSeed hphysical hHoeffding).congr'
  exact Eventually.of_forall fun n =>
    (mixedPolynomialFinalStageExpectedScaledQuadraticRisk_eq_integral
      theta b hphysical n).symm

/-- Pilot plus exact-cycle final-stage observation count.  This deliberately
does not use the older schedule's one-copy `polynomialTotalShots`, because the
present exact cycle has three final blocks of length `q`. -/
def mixedPolynomialExactCycleTotalObservations (n : ℕ) : ℕ :=
  polynomialPilotObservations n + 3 * polynomialFinalShots n

/-- Conversion factor from final-stage scaling to total-observation scaling. -/
def mixedPolynomialExactCycleTotalToFinalRatio (n : ℕ) : ℝ :=
  (mixedPolynomialExactCycleTotalObservations n : ℝ) /
    (3 * polynomialFinalShots n : ℝ)

/-- The conversion factor is exactly `1 + 1/m` for the degree-five pilot and
degree-six allocation per final frame column. -/
theorem mixedPolynomialExactCycleTotalToFinalRatio_eq (n : ℕ) :
    mixedPolynomialExactCycleTotalToFinalRatio n =
      1 + 1 / (polynomialScheduleM n : ℝ) := by
  have hm : (polynomialScheduleM n : ℝ) ≠ 0 := by
    unfold polynomialScheduleM
    positivity
  unfold mixedPolynomialExactCycleTotalToFinalRatio
  unfold mixedPolynomialExactCycleTotalObservations
  unfold polynomialPilotObservations polynomialPilotBlocks polynomialFinalShots
  push_cast
  field_simp [hm]
  ring

private theorem polynomialScheduleM_reciprocal_tendsto_zero :
    Tendsto (fun n => 1 / (polynomialScheduleM n : ℝ))
      atTop (nhds 0) := by
  have hScaled :
      Tendsto
        (fun n => (1 / 6 : ℝ) * polynomialScaledSquaredErrorEnvelope n)
        atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds.mul
        polynomialScaledSquaredErrorEnvelope_tendsto_zero)
  apply hScaled.congr'
  filter_upwards with n
  unfold polynomialScaledSquaredErrorEnvelope polynomialScheduleM
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hn]

/-- The pilot is asymptotically negligible relative to the three final blocks. -/
theorem mixedPolynomialExactCycleTotalToFinalRatio_tendsto_one :
    Tendsto mixedPolynomialExactCycleTotalToFinalRatio atTop (nhds 1) := by
  have h :
      Tendsto
        (fun n : ℕ => (1 : ℝ) + 1 / (polynomialScheduleM n : ℝ))
        atTop (nhds ((1 : ℝ) + 0)) :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).add
        polynomialScheduleM_reciprocal_tendsto_zero
  simpa only [add_zero] using h.congr'
    (Eventually.of_forall fun n =>
      (mixedPolynomialExactCycleTotalToFinalRatio_eq n).symm)

/-- The explicit risk rescaled by pilot-plus-final observations. -/
def mixedPolynomialTotalObservationScaledQuadraticRisk
    (theta b : Fin 3 → ℝ) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (mixedPolynomialExactCycleTotalToFinalRatio n) *
    mixedPolynomialFinalStageExpectedScaledQuadraticRisk theta b n

/-- Total-observation scaling has the same `9/4` endpoint because the pilot
fraction tends to zero. -/
theorem mixedPolynomialTotalObservationScaledQuadraticRisk_tendsto_nine_fourths
    (theta b : Fin 3 → ℝ)
    (hPositive : 0 < blochNormSq theta)
    (hInterior : blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hphysical : PauliPilotPhysicalBloch theta)
    (hHoeffding :
      PauliPilotConsistencyHoeffdingContracts theta hphysical) :
    Tendsto (mixedPolynomialTotalObservationScaledQuadraticRisk theta b)
      atTop (nhds (ENNReal.ofReal (9 / 4 : ℝ))) := by
  have hRatioReal := mixedPolynomialExactCycleTotalToFinalRatio_tendsto_one
  have hRatio :
      Tendsto
        (fun n => ENNReal.ofReal
          (mixedPolynomialExactCycleTotalToFinalRatio n))
        atTop (nhds (1 : ℝ≥0∞)) := by
    simpa [Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hRatioReal
  have hRisk :=
    mixedPolynomialFinalStageExpectedScaledQuadraticRisk_tendsto_nine_fourths
      theta b hPositive hInterior hSeed hphysical hHoeffding
  have hMul := ENNReal.Tendsto.mul hRatio (Or.inl one_ne_zero)
    hRisk (Or.inr ENNReal.one_ne_top)
  have hMul' :
      Tendsto
        (fun n => ENNReal.ofReal
          (mixedPolynomialExactCycleTotalToFinalRatio n) *
            mixedPolynomialFinalStageExpectedScaledQuadraticRisk theta b n)
        atTop (nhds (ENNReal.ofReal (9 / 4 : ℝ))) := by
    simpa using hMul
  apply hMul'.congr'
  exact Eventually.of_forall fun _ => rfl

/-- Non-circular package of the concrete endpoint assumptions. -/
structure MixedPolynomialQuadraticRiskHypotheses
    (theta b : Fin 3 → ℝ) : Prop where
  positive : 0 < blochNormSq theta
  interior : blochNormSq theta < 1
  seed : LocalFrameSeedNonparallelAt b theta
  physical : PauliPilotPhysicalBloch theta
  hoeffding : PauliPilotConsistencyHoeffdingContracts theta physical

namespace Label

/-- Honest paper-facing label for the concrete nonzero-interior mixed-qubit
polynomial quadratic-risk reduction.  It does not assert exact Bures risk. -/
theorem eq_SI_mixed_polynomial_quadratic_risk_qubit_reduction
    (theta b : Fin 3 → ℝ)
    (h : MixedPolynomialQuadraticRiskHypotheses theta b) :
    Tendsto (mixedPolynomialFinalStageExpectedScaledQuadraticRisk theta b)
        atTop (nhds (ENNReal.ofReal (9 / 4 : ℝ))) ∧
      Tendsto (mixedPolynomialTotalObservationScaledQuadraticRisk theta b)
        atTop (nhds (ENNReal.ofReal (9 / 4 : ℝ))) := by
  constructor
  · exact mixedPolynomialFinalStageExpectedScaledQuadraticRisk_tendsto_nine_fourths
      theta b h.positive h.interior h.seed h.physical h.hoeffding
  · exact mixedPolynomialTotalObservationScaledQuadraticRisk_tendsto_nine_fourths
      theta b h.positive h.interior h.seed h.physical h.hoeffding

end Label
end QubitOracle.Paper
