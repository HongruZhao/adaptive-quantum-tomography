import QubitOracle.Paper.OneQubitMixedUniformLocalRiskCore
import QubitOracle.Paper.OneQubitPolynomialTwoStageSchedule
import QubitOracle.Paper.OneQubitMixedPolynomialBadBranchRisk
import QubitOracle.Paper.OneQubitMixedFiniteInfinitePilotIntegrationBridge
import QubitOracle.Paper.OneQubitMixedFinalEstimatorFourthMoment
import QubitOracle.Paper.OneQubitMixedPolynomialExactBuresRiskClosed

/-!
# Exact-cycle uniform local probability-envelope reduction

The exact-cycle schedule is

* `N(n) = 3 m^5 + 3 m^6`,
* `qFinal(n) = m^6`,
* `m = n + 1`.

This file proves the truth-parametric finite-row ingredients needed by
`MixedUniformLocalProbabilityEnvelope`:

* uniform polynomial-threshold Hoeffding control under every local truth;
* the deterministic local-mean-shift correction;
* uniform selected-frame quadratic-risk control on the actual polynomial good
  event;
* the varying-truth exact finite pilot/final joint-law identity;
* exact-cycle total-shot-scaled pilot bad-mass decay;
* frame-uniform second, third, and fourth moment bounds;
* the common interior denominator margin from the preceding module.

There is an important interface distinction.  The earlier
`MixedUniformLocalPilotGood` asks for pilot error at scale `1/sqrt(N)`, which is
of order `m^-3`.  The proved polynomial Hoeffding event uses threshold `m^-2`
for an `m^5` pilot.  Hoeffding at the polynomial threshold does not imply that
the smaller `m^-3` event has probability tending to one.  Therefore the proof
below uses the actual polynomial good event and does not manufacture the
missing implication.

One internal finite-sum lemma remains explicit as
`MixedExactCycleUniformExactLossAveragingBridge`: it must combine the exact
joint law, common local radius, frame-uniform moments, safeguard, and the two
exact loss remainders under the varying local truth.  It is a `Prop`, not an
axiom.  Conditional on that exact finite-row lemma, this file constructs the
original probability-envelope contract and the conditional minimax upper
reduction.  The only permitted literature input remains the exact finite
Hoeffding family passed as a parameter.
-/

open scoped BigOperators ENNReal
open Filter MeasureTheory

namespace QubitOracle.Paper

/-! ## Exact-cycle schedule -/

/-- Exact total number of observations in the three-axis final-cycle protocol. -/
abbrev mixedUniformLocalExactCycleN : ℕ → ℕ :=
  mixedPolynomialExactCycleTotalObservations

/-- Exact number of final observations per frame column. -/
abbrev mixedUniformLocalExactCycleQFinal : ℕ → ℕ :=
  mixedPolynomialQuadraticQFinal

/-- The exact-cycle total is `3 m^5 + 3 m^6`. -/
theorem mixedUniformLocalExactCycleN_eq (n : ℕ) :
    mixedUniformLocalExactCycleN n =
      3 * polynomialScheduleM n ^ 5 + 3 * polynomialScheduleM n ^ 6 := by
  simp [mixedUniformLocalExactCycleN,
    mixedPolynomialExactCycleTotalObservations,
    polynomialPilotObservations, polynomialPilotBlocks,
    polynomialFinalShots]

/-- The final allocation per coordinate is exactly `m^6`. -/
theorem mixedUniformLocalExactCycleQFinal_eq (n : ℕ) :
    mixedUniformLocalExactCycleQFinal n = polynomialScheduleM n ^ 6 := by
  simp [mixedUniformLocalExactCycleQFinal,
    mixedPolynomialQuadraticQFinal, polynomialFinalShots]

/-- Every exact-cycle final allocation is positive. -/
theorem mixedUniformLocalExactCycleQFinal_pos (n : ℕ) :
    0 < mixedUniformLocalExactCycleQFinal n :=
  mixedPolynomialQuadraticQFinal_pos n

/-- The exact total observation count tends to infinity. -/
theorem mixedUniformLocalExactCycleN_real_tendsto_atTop :
    Tendsto (fun n => (mixedUniformLocalExactCycleN n : ℝ))
      atTop atTop := by
  rw [tendsto_atTop]
  intro A
  obtain ⟨k, hk⟩ := exists_nat_ge A
  filter_upwards [eventually_ge_atTop k] with n hn
  have hmOne : (1 : ℝ) ≤ (polynomialScheduleM n : ℝ) := by
    simp [polynomialScheduleM]
  have hmFive :
      (1 : ℝ) ^ 5 ≤ (polynomialScheduleM n : ℝ) ^ 5 :=
    pow_le_pow_left₀ (by norm_num) hmOne 5
  have hmNonnegative : (0 : ℝ) ≤ (polynomialScheduleM n : ℝ) :=
    le_trans (by norm_num) hmOne
  have hmLeSix :
      (polynomialScheduleM n : ℝ) ≤
        (polynomialScheduleM n : ℝ) ^ 6 := by
    calc
      (polynomialScheduleM n : ℝ) =
          (polynomialScheduleM n : ℝ) * 1 := by ring
      _ ≤ (polynomialScheduleM n : ℝ) *
          (polynomialScheduleM n : ℝ) ^ 5 :=
        mul_le_mul_of_nonneg_left (by simpa using hmFive) hmNonnegative
      _ = (polynomialScheduleM n : ℝ) ^ 6 := by ring
  have hnLeM : (n : ℝ) ≤ (polynomialScheduleM n : ℝ) := by
    simp [polynomialScheduleM]
  have hScheduleLower :
      (n : ℝ) ≤ (mixedUniformLocalExactCycleN n : ℝ) := by
    rw [mixedUniformLocalExactCycleN_eq]
    push_cast
    have hmFiveNonnegative :
        (0 : ℝ) ≤ (polynomialScheduleM n : ℝ) ^ 5 := by positivity
    nlinarith
  exact hk.trans ((Nat.cast_le.mpr hn).trans hScheduleLower)

/-- Consequently the exact local scale `1/sqrt(N(n))` tends to zero. -/
theorem mixedUniformLocalExactCycleScale_tendsto_zero :
    Tendsto (mixedLocalScale mixedUniformLocalExactCycleN)
      atTop (nhds 0) := by
  have hSqrt : Tendsto
      (fun n => Real.sqrt (mixedUniformLocalExactCycleN n : ℝ))
      atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      mixedUniformLocalExactCycleN_real_tendsto_atTop
  change Tendsto
    (fun n => (Real.sqrt (mixedUniformLocalExactCycleN n : ℝ))⁻¹)
    atTop (nhds 0)
  refine (tendsto_inv_atTop_zero.comp hSqrt).congr' ?_
  exact Eventually.of_forall (fun _ => rfl)

/-- The polynomial pilot threshold `m^-2` tends to zero. -/
theorem polynomialPilotThreshold_tendsto_zero_local :
    Tendsto polynomialPilotThreshold atTop (nhds 0) := by
  exact polynomialPilotThreshold_tendsto_zero

/-! ## The sole permitted external finite Hoeffding family -/

/-- Exact finite Hoeffding input, uniformly quantified over the deterministic
local parameter family.  Each witness is precisely the already defined paired
finite Pauli Hoeffding contract; no conclusion is added to it. -/
structure MixedExactCycleUniformFiniteHoeffdingContract
    (theta : RLSVector 3) (H : ℝ) : Prop where
  eventually_contract :
    ∀ᶠ n in atTop, ∀ h : RLSVector 3,
      MixedLocalDirectionBall H h →
      ∃ hPhysical : PauliPilotPhysicalBloch
          (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h),
        PauliPilotConsistencyHoeffdingContracts
          (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h)
          hPhysical

/-- The actual polynomial pilot good event under the local truth. -/
def MixedExactCycleLocalPolynomialPilotGood
    (theta : RLSVector 3) (n : ℕ) (h : RLSVector 3)
    (omega : PauliPilotConsistencySampleSpace) : Prop :=
  omega ∉ polynomialPilotBadEvent
    (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h) n

/-- On the actual polynomial good event, every pilot coordinate is within the
proved `m^-2` threshold of the actual local mean. -/
theorem mixedExactCycleLocalPolynomialPilotGood_coordinate_lt
    (theta : RLSVector 3) (n : ℕ) (h : RLSVector 3)
    (omega : PauliPilotConsistencySampleSpace)
    (hGood : MixedExactCycleLocalPolynomialPilotGood theta n h omega)
    (j : Fin 3) :
    |polynomialPilotEstimator n omega j -
      mixedLocalAlternative theta mixedUniformLocalExactCycleN n h j| <
        polynomialPilotThreshold n := by
  by_contra hNot
  have hLarge : polynomialPilotThreshold n ≤
      |polynomialPilotEstimator n omega j -
        mixedLocalAlternative theta mixedUniformLocalExactCycleN n h j| :=
    le_of_not_gt hNot
  apply hGood
  unfold polynomialPilotBadEvent QubitOracle.coordinateDeltaBadEvent
  exact ⟨j, hLarge⟩

/-- Deterministic local-mean-shift correction on the actual polynomial good
event. -/
theorem mixedExactCycleLocalPolynomialPilotGood_center_error_le
    (theta : RLSVector 3) (H : ℝ) (n : ℕ) (h : RLSVector 3)
    (omega : PauliPilotConsistencySampleSpace)
    (hH : 0 ≤ H) (hBall : MixedLocalDirectionBall H h)
    (hGood : MixedExactCycleLocalPolynomialPilotGood theta n h omega)
    (j : Fin 3) :
    |polynomialPilotEstimator n omega j - theta j| ≤
      polynomialPilotThreshold n +
        |mixedLocalScale mixedUniformLocalExactCycleN n| * H := by
  have hPilot := le_of_lt
    (mixedExactCycleLocalPolynomialPilotGood_coordinate_lt
      theta n h omega hGood j)
  have hDirection := mixedLocalDirection_coordinate_abs_le H h hH hBall j
  have hShift :
      |mixedLocalAlternative theta mixedUniformLocalExactCycleN n h j -
          theta j| ≤
        |mixedLocalScale mixedUniformLocalExactCycleN n| * H := by
    simp only [mixedLocalAlternative, add_sub_cancel_left, abs_mul]
    exact mul_le_mul_of_nonneg_left hDirection (abs_nonneg _)
  calc
    |polynomialPilotEstimator n omega j - theta j| =
        |(polynomialPilotEstimator n omega j -
            mixedLocalAlternative theta mixedUniformLocalExactCycleN n h j) +
          (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h j -
            theta j)| := by
              congr 1
              ring
    _ ≤ |polynomialPilotEstimator n omega j -
          mixedLocalAlternative theta mixedUniformLocalExactCycleN n h j| +
        |mixedLocalAlternative theta mixedUniformLocalExactCycleN n h j -
          theta j| := abs_add_le _ _
    _ ≤ polynomialPilotThreshold n +
        |mixedLocalScale mixedUniformLocalExactCycleN n| * H :=
      add_le_add hPilot hShift

/-- Vanishing common coordinate envelope on the actual polynomial good event. -/
noncomputable def mixedExactCycleLocalPilotCenterEnvelope
    (H : ℝ) (n : ℕ) : ℝ :=
  polynomialPilotThreshold n +
    |mixedLocalScale mixedUniformLocalExactCycleN n| * H

/-- The local polynomial pilot's center envelope tends to zero. -/
theorem mixedExactCycleLocalPilotCenterEnvelope_tendsto_zero
    (H : ℝ) :
    Tendsto (mixedExactCycleLocalPilotCenterEnvelope H)
      atTop (nhds 0) := by
  have hShift := mixedUniformLocalExactCycleScale_tendsto_zero.abs.mul
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => H) atTop (nhds H))
  change Tendsto
    (fun n => polynomialPilotThreshold n +
      |mixedLocalScale mixedUniformLocalExactCycleN n| * H)
    atTop (nhds 0)
  simpa using polynomialPilotThreshold_tendsto_zero_local.add hShift

/-- The already proved sequential frame-continuity theorem now gives one
uniform quadratic-risk bound over all compact local directions on the actual
polynomial Hoeffding good event. -/
theorem mixedExactCycleLocalPolynomialGood_uniform_frozenFrameRisk
    (b theta : RLSVector 3) (H : ℝ)
    (hH : 0 ≤ H)
    (hPositive : 0 < QubitOracle.blochNormSq theta)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ n in atTop, ∀ h : RLSVector 3,
      MixedLocalDirectionBall H h →
      ∀ omega : PauliPilotConsistencySampleSpace,
        MixedExactCycleLocalPolynomialPilotGood theta n h omega →
        |mixedFrameConditionalScaledQuadraticRisk
            (q := mixedUniformLocalExactCycleQFinal n) theta
            (mixedPilotSelectedLocalFrame b
              (polynomialPilotEstimator n omega)) - 9 / 4| < epsilon := by
  have hEnvelopeNonnegative : ∀ᶠ n in atTop,
      0 ≤ mixedExactCycleLocalPilotCenterEnvelope H n := by
    exact Eventually.of_forall fun n =>
      add_nonneg (by
        unfold polynomialPilotThreshold
        positivity) (mul_nonneg (abs_nonneg _) hH)
  have hUniform :=
    mixedSelectedFrameConditionalScaledRisk_uniform_of_coordinateEnvelope
      b theta mixedUniformLocalExactCycleQFinal
      mixedUniformLocalExactCycleQFinal_pos
      hPositive hInterior hSeed
      (mixedExactCycleLocalPilotCenterEnvelope H)
      hEnvelopeNonnegative
      (mixedExactCycleLocalPilotCenterEnvelope_tendsto_zero H)
      epsilon hepsilon
  filter_upwards [hUniform] with n hn
  intro h hBall omega hGood
  apply hn
  intro j
  exact mixedExactCycleLocalPolynomialPilotGood_center_error_le
    theta H n h omega hH hBall hGood j

/-! ## Uniform finite Hoeffding and bad-branch bounds -/

/-- The same truth-independent `6 exp(-m/2)` envelope controls every local
pilot row. -/
theorem mixedExactCycleLocalPilot_badEvent_uniform_bound
    (theta : RLSVector 3) (H : ℝ)
    (hHoeffding : MixedExactCycleUniformFiniteHoeffdingContract theta H) :
    ∀ᶠ n in atTop, ∀ h : RLSVector 3,
      MixedLocalDirectionBall H h →
      pauliPilotConsistencyMeasure
          (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h)
          (polynomialPilotBadEvent
            (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h) n) ≤
        polynomialPilotBadEventEnvelope n := by
  filter_upwards [hHoeffding.eventually_contract] with n hn
  intro h hBall
  rcases hn h hBall with ⟨hPhysical, hFiniteHoeffding⟩
  exact polynomialPilot_badEvent_bound
    (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h)
    hPhysical hFiniteHoeffding n

/-- Exact-cycle observations are at most three times the older one-final-block
count used by the established exponential-decay lemma. -/
theorem mixedUniformLocalExactCycleN_le_three_mul_polynomialTotalShots
    (n : ℕ) :
    mixedUniformLocalExactCycleN n ≤ 3 * polynomialTotalShots n := by
  simp [mixedUniformLocalExactCycleN,
    mixedPolynomialExactCycleTotalObservations,
    polynomialTotalShots, polynomialPilotObservations,
    polynomialPilotBlocks, polynomialFinalShots]
  omega

/-- Exact-cycle total shots times the common pilot bad-event envelope tends to
zero. -/
theorem mixedUniformLocalExactCycleN_mul_badEventEnvelope_tendsto_zero :
    Tendsto
      (fun n => (mixedUniformLocalExactCycleN n : ℝ≥0∞) *
        polynomialPilotBadEventEnvelope n)
      atTop (nhds 0) := by
  have hBase : Tendsto
      (fun n => (polynomialTotalShots n : ℝ≥0∞) *
        polynomialPilotBadEventEnvelope n)
      atTop (nhds 0) :=
    polynomialTotalShots_mul_badEventEnvelope_tendsto_zero
  have hUpper : Tendsto
      (fun n => (3 : ℝ≥0∞) *
        ((polynomialTotalShots n : ℝ≥0∞) *
          polynomialPilotBadEventEnvelope n))
      atTop (nhds 0) := by
    have hTriple : Tendsto
        (fun n => (3 : ℝ≥0∞) *
          ((polynomialTotalShots n : ℝ≥0∞) *
            polynomialPilotBadEventEnvelope n))
        atTop (nhds (0 + 0 + 0)) := by
      refine ((hBase.add hBase).add hBase).congr' ?_
      exact Eventually.of_forall (fun _ => by ring)
    simpa using hTriple
  apply Tendsto.squeeze tendsto_const_nhds hUpper
  · intro n
    exact bot_le
  · intro n
    have hCount : (mixedUniformLocalExactCycleN n : ℝ≥0∞) ≤
        3 * (polynomialTotalShots n : ℝ≥0∞) := by
      exact_mod_cast
        mixedUniformLocalExactCycleN_le_three_mul_polynomialTotalShots n
    calc
      (mixedUniformLocalExactCycleN n : ℝ≥0∞) *
          polynomialPilotBadEventEnvelope n ≤
        (3 * (polynomialTotalShots n : ℝ≥0∞)) *
          polynomialPilotBadEventEnvelope n :=
        mul_le_mul_of_nonneg_right hCount (by positivity)
      _ = 3 * ((polynomialTotalShots n : ℝ≥0∞) *
          polynomialPilotBadEventEnvelope n) := by ac_rfl

/-- Uniform total-shot-scaled bad-event probability tends to zero; `h` remains
outside each finite-row measure. -/
theorem mixedExactCycleLocalPilot_scaledBadProbability_uniform
    (theta : RLSVector 3) (H : ℝ)
    (hHoeffding : MixedExactCycleUniformFiniteHoeffdingContract theta H)
    (epsilon : ℝ≥0∞) (hepsilon : 0 < epsilon) :
    ∀ᶠ n in atTop, ∀ h : RLSVector 3,
      MixedLocalDirectionBall H h →
      (mixedUniformLocalExactCycleN n : ℝ≥0∞) *
          pauliPilotConsistencyMeasure
            (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h)
            (polynomialPilotBadEvent
              (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h) n) <
        epsilon := by
  have hEnvelopeSmall : ∀ᶠ n in atTop,
      (mixedUniformLocalExactCycleN n : ℝ≥0∞) *
          polynomialPilotBadEventEnvelope n < epsilon :=
    (tendsto_order.1
      mixedUniformLocalExactCycleN_mul_badEventEnvelope_tendsto_zero).2
      epsilon hepsilon
  filter_upwards
    [mixedExactCycleLocalPilot_badEvent_uniform_bound
      theta H hHoeffding, hEnvelopeSmall] with n hn hSmall
  intro h hBall
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left (hn h hBall) (by positivity)) hSmall

/-! ## Varying-truth exact joint law and frame-uniform moments -/

/-- The exact finite pilot/final row identity holds at every local truth. -/
theorem mixedExactCycleLocalFiniteRowJointLaw
    (theta b : RLSVector 3) (n : ℕ) (h : RLSVector 3) :
    MixedPilotFiniteRowFinalJointLaw
      (mixedUniformLocalExactCycleQFinal n)
      (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h)
      (mixedPilotLocalSelectedFinalFrame
        (Nat.succ (polynomialPilotIndex n)) b) :=
  mixedPolynomialExactCycleFiniteRowJointLaw
    (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h)
    b mixedUniformLocalExactCycleQFinal n

/-- Frame-uniform local-truth moment package.  Constants `3`, `15`, and `18`
are independent of the local direction and selected orthonormal frame. -/
theorem mixedExactCycleLocalFinalMomentPackage
    (theta : RLSVector 3) (n : ℕ) (h : RLSVector 3)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : MixedFrameOrthonormal R)
    (hPhysical : PauliPilotPhysicalBloch
      (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h)) :
    pauliPilotFiniteExpectation
        (q := mixedUniformLocalExactCycleQFinal n)
        (qubitFrameCoordinates R
          (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h))
        (mixedFrameFinalSquaredError
          (q := mixedUniformLocalExactCycleQFinal n)
          (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h) R) ≤
        3 / (mixedUniformLocalExactCycleQFinal n : ℝ) ∧
      pauliPilotFiniteExpectation
        (q := mixedUniformLocalExactCycleQFinal n)
        (qubitFrameCoordinates R
          (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h))
        (fun path => mixedFrameFinalSquaredError
          (q := mixedUniformLocalExactCycleQFinal n)
          (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h)
          R path ^ 2) ≤
        15 / (mixedUniformLocalExactCycleQFinal n : ℝ) ^ 2 ∧
      pauliPilotFiniteExpectation
        (q := mixedUniformLocalExactCycleQFinal n)
        (qubitFrameCoordinates R
          (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h))
        (fun path => mixedFrameFinalErrorNorm
          (q := mixedUniformLocalExactCycleQFinal n)
          (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h)
          R path ^ 3) ≤
        18 / ((mixedUniformLocalExactCycleQFinal n : ℝ) *
          Real.sqrt (mixedUniformLocalExactCycleQFinal n : ℝ)) := by
  exact ⟨
    mixedFrameFinalSquaredError_expectation_le
      (mixedUniformLocalExactCycleQFinal_pos n)
      (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h)
      R hR hPhysical,
    mixedFrameFinalSquaredError_fourthMoment_le
      (mixedUniformLocalExactCycleQFinal_pos n)
      (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h)
      R hR hPhysical,
    mixedFrameFinalErrorNorm_thirdMoment_le
      (mixedUniformLocalExactCycleQFinal_pos n)
      (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h)
      R hR hPhysical⟩

/-- The preceding common-margin theorem specializes to the exact-cycle local
family and supplies a single positive denominator for every exact-loss
remainder constant. -/
theorem mixedExactCycleLocal_uniform_remainder_margin
    (theta : RLSVector 3) (H : ℝ)
    (hInterior : QubitOracle.blochNormSq theta < 1) :
    ∀ᶠ n in atTop, ∀ h : RLSVector 3,
      MixedLocalDirectionBall H h →
      (1 - QubitOracle.blochNormSq theta) / 2 ≤
        1 - QubitOracle.blochNormSq
          (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h) ∧
      0 < 1 - QubitOracle.blochNormSq
        (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h) :=
  mixedLocalAlternative_eventually_uniform_remainder_margin
    theta mixedUniformLocalExactCycleN H hInterior
    mixedUniformLocalExactCycleScale_tendsto_zero

/-! ## Exact remaining finite-sum bridge -/

/-- Narrow remaining internal lemma.

Unlike `MixedUniformLocalProbabilityEnvelope`, this statement uses the actual
high-probability polynomial good event (`m^-2`).  It asks only for the final
finite-sum combination of the already proved joint-law, bad-mass, common
margin, safeguard, and frame-uniform moment/remainder inequalities.

This is not a literature premise and is not declared as an axiom. -/
def MixedExactCycleUniformExactLossAveragingBridge
    (theta b : RLSVector 3) (H : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    (∀ᶠ n in atTop, ∀ h : RLSVector 3,
      MixedLocalDirectionBall H h →
      ∀ omega : PauliPilotConsistencySampleSpace,
        MixedExactCycleLocalPolynomialPilotGood theta n h omega →
        mixedFrameConditionalScaledQuadraticRisk
            (q := mixedUniformLocalExactCycleQFinal n) theta
            (mixedPilotSelectedLocalFrame b
              (polynomialPilotEstimator n omega)) ≤
          9 / 4 + epsilon) →
    ∀ᶠ n in atTop, ∀ loss : MixedUniformLocalExactLoss,
      ∀ h : RLSVector 3, MixedLocalDirectionBall H h →
        mixedUniformLocalTotalScaledExactRisk loss
            (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h)
            b n ≤
          ENNReal.ofReal (9 / 4 + 2 * epsilon)

/-! The usable constructor keeps the necessary radius, interior-truth, and
nonparallel-seed hypotheses explicit. -/
theorem mixedUniformLocalProbabilityEnvelope_exactCycle_reduction
    (theta b : RLSVector 3) (H : ℝ)
    (hH : 0 ≤ H)
    (hPositive : 0 < QubitOracle.blochNormSq theta)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hBridge : MixedExactCycleUniformExactLossAveragingBridge theta b H) :
    MixedUniformLocalProbabilityEnvelope
      theta b mixedUniformLocalExactCycleN H
      mixedUniformLocalExactCycleQFinal := by
  refine ⟨?_⟩
  intro epsilon hepsilon _hTooSmallGoodEvent
  have hActualGoodAbs :=
    mixedExactCycleLocalPolynomialGood_uniform_frozenFrameRisk
      b theta H hH hPositive hInterior hSeed epsilon hepsilon
  have hActualGoodUpper : ∀ᶠ n in atTop, ∀ h : RLSVector 3,
      MixedLocalDirectionBall H h →
      ∀ omega : PauliPilotConsistencySampleSpace,
        MixedExactCycleLocalPolynomialPilotGood theta n h omega →
        mixedFrameConditionalScaledQuadraticRisk
            (q := mixedUniformLocalExactCycleQFinal n) theta
            (mixedPilotSelectedLocalFrame b
              (polynomialPilotEstimator n omega)) ≤ 9 / 4 + epsilon := by
    filter_upwards [hActualGoodAbs] with n hn
    intro h hBall omega hGood
    have hAbs := hn h hBall omega hGood
    have hOneSide := le_abs_self
      (mixedFrameConditionalScaledQuadraticRisk
        (q := mixedUniformLocalExactCycleQFinal n) theta
        (mixedPilotSelectedLocalFrame b
          (polynomialPilotEstimator n omega)) - 9 / 4)
    linarith
  exact hBridge epsilon hepsilon hActualGoodUpper


end QubitOracle.Paper
