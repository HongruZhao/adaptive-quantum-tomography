import QubitOracle.Paper.OneQubitMixedPolynomialOrdinaryInfidelityEndpoint
import QubitOracle.Paper.OneQubitMixedGoodBranchUniformEnvelopeClosed
import QubitOracle.Paper.OneQubitMixedFrozenPolynomialEndpointCore

/-!
# Uniform local-risk non-LAN core for the mixed one-qubit protocol

This file treats the concrete polynomial two-stage mixed-qubit protocol near a
fixed nonzero interior truth `theta`.  Local alternatives have the exact form

`theta_n(h) = theta + h / sqrt(N_n)`

for `h : Fin 3 → ℝ` in the deterministic ball
`blochNormSq h ≤ H^2`.

The following parts are proved internally:

* a common eventual interior margin for all local directions in the ball;
* deterministic pilot consistency after including the local shift;
* a sequential-contradiction upgrade from coordinate consistency to a uniform
  frozen-center selected-frame quadratic-risk bound;
* a common positive denominator margin for all local exact-loss Taylor
  constants.

Exactly one residual `Prop` contract remains:
`MixedUniformLocalProbabilityEnvelope`.  It is the finite-law probability
step transferring the deterministic good-branch bound through the locally
varying pilot law, the pilot bad branch, the safeguarded final estimator, and
the exact Bures/ordinary-infidelity remainders.  It is not an axiom and is not
inhabited here.
-/

open scoped BigOperators ENNReal
open Filter

namespace QubitOracle.Paper

/-! ## Local alternatives and their deterministic interior margin -/

/-- Exact local scale `1 / sqrt(N_n)`.  Lean's value at `N_n = 0` is harmless;
the asymptotic schedule assumption below forces the scale to zero. -/
noncomputable def mixedLocalScale (N : ℕ → ℕ) (n : ℕ) : ℝ :=
  (Real.sqrt (N n : ℝ))⁻¹

/-- The local mixed-qubit Bloch alternative `theta + h / sqrt(N_n)`. -/
noncomputable def mixedLocalAlternative
    (theta : RLSVector 3) (N : ℕ → ℕ) (n : ℕ)
    (h : RLSVector 3) : RLSVector 3 :=
  fun j => theta j + mixedLocalScale N n * h j

/-- Deterministic compact local-direction ball used instead of an uncountable
measurable supremum. -/
def MixedLocalDirectionBall (H : ℝ) (h : RLSVector 3) : Prop :=
  QubitOracle.blochNormSq h ≤ H ^ 2

/-- A scalar inequality used to control the mixed term in the Bloch norm. -/
theorem two_mul_three_product_le_abs_mul_sq_add_sq
    (s a b : ℝ) :
    2 * s * a * b ≤ |s| * (a ^ 2 + b ^ 2) := by
  have hab : 2 * |a| * |b| ≤ |a| ^ 2 + |b| ^ 2 := by
    nlinarith [sq_nonneg (|a| - |b|)]
  have hab' : 2 * |a| * |b| ≤ a ^ 2 + b ^ 2 := by
    simpa [sq_abs] using hab
  have hscaled := mul_le_mul_of_nonneg_left hab' (abs_nonneg s)
  calc
    2 * s * a * b ≤ |2 * s * a * b| := le_abs_self _
    _ = 2 * |s| * |a| * |b| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ |s| * (a ^ 2 + b ^ 2) := by
      nlinarith

/-- Finite `Fin 3` Cauchy/Young bound for the local cross term. -/
theorem two_mul_blochDot_le_abs_scale_mul_normSums
    (s : ℝ) (theta h : RLSVector 3) :
    2 * s * QubitOracle.blochDot theta h ≤
      |s| * (QubitOracle.blochNormSq theta +
        QubitOracle.blochNormSq h) := by
  have h0 := two_mul_three_product_le_abs_mul_sq_add_sq
    s (theta 0) (h 0)
  have h1 := two_mul_three_product_le_abs_mul_sq_add_sq
    s (theta 1) (h 1)
  have h2 := two_mul_three_product_le_abs_mul_sq_add_sq
    s (theta 2) (h 2)
  simp [QubitOracle.blochDot, QubitOracle.blochNormSq,
    Fin.sum_univ_succ] at h0 h1 h2 ⊢
  nlinarith

/-- Exact squared-Bloch-norm expansion along a local direction. -/
theorem mixedLocalAlternative_blochNormSq_expansion
    (theta h : RLSVector 3) (N : ℕ → ℕ) (n : ℕ) :
    QubitOracle.blochNormSq (mixedLocalAlternative theta N n h) =
      QubitOracle.blochNormSq theta +
        2 * mixedLocalScale N n * QubitOracle.blochDot theta h +
        mixedLocalScale N n ^ 2 * QubitOracle.blochNormSq h := by
  simp [mixedLocalAlternative, QubitOracle.blochNormSq,
    QubitOracle.blochDot, Fin.sum_univ_succ]
  ring

/-- The explicit common perturbation envelope for all `h` in the radius-`H`
ball. -/
noncomputable def mixedLocalInteriorEnvelope
    (N : ℕ → ℕ) (H : ℝ) (n : ℕ) : ℝ :=
  |mixedLocalScale N n| * (1 + H ^ 2) +
    mixedLocalScale N n ^ 2 * H ^ 2

/-- Uniform deterministic upper bound for the local alternative's Bloch norm. -/
theorem mixedLocalAlternative_blochNormSq_le
    (theta h : RLSVector 3) (N : ℕ → ℕ) (H : ℝ) (n : ℕ)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hBall : MixedLocalDirectionBall H h) :
    QubitOracle.blochNormSq (mixedLocalAlternative theta N n h) ≤
      QubitOracle.blochNormSq theta + mixedLocalInteriorEnvelope N H n := by
  have hCross := two_mul_blochDot_le_abs_scale_mul_normSums
    (mixedLocalScale N n) theta h
  have hThetaNorm : QubitOracle.blochNormSq theta ≤ 1 :=
    le_of_lt hInterior
  have hAbs : 0 ≤ |mixedLocalScale N n| := abs_nonneg _
  have hSq : 0 ≤ mixedLocalScale N n ^ 2 := sq_nonneg _
  have hNormSum :
      QubitOracle.blochNormSq theta + QubitOracle.blochNormSq h ≤
        1 + H ^ 2 := by
    exact add_le_add hThetaNorm hBall
  have hCrossEnvelope := mul_le_mul_of_nonneg_left hNormSum hAbs
  have hSquareEnvelope := mul_le_mul_of_nonneg_left hBall hSq
  rw [mixedLocalAlternative_blochNormSq_expansion]
  unfold mixedLocalInteriorEnvelope
  nlinarith

/-- The interior perturbation envelope tends to zero whenever the exact local
scale tends to zero. -/
theorem mixedLocalInteriorEnvelope_tendsto_zero
    (N : ℕ → ℕ) (H : ℝ)
    (hScale : Tendsto (mixedLocalScale N) atTop (nhds 0)) :
    Tendsto (mixedLocalInteriorEnvelope N H) atTop (nhds 0) := by
  have hFirst := hScale.abs.mul
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 + H ^ 2 : ℝ))
      atTop (nhds (1 + H ^ 2)))
  have hSecond := (hScale.pow 2).mul
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (H ^ 2 : ℝ))
      atTop (nhds (H ^ 2)))
  change Tendsto
    (fun n => |mixedLocalScale N n| * (1 + H ^ 2) +
      mixedLocalScale N n ^ 2 * H ^ 2) atTop (nhds 0)
  simpa using hFirst.add hSecond

/-- Every compact local family stays in one strictly smaller Bloch ball for all
large rows.  The common remaining margin is half the truth margin. -/
theorem mixedLocalAlternative_eventually_uniform_interior_margin
    (theta : RLSVector 3) (N : ℕ → ℕ) (H : ℝ)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hScale : Tendsto (mixedLocalScale N) atTop (nhds 0)) :
    ∀ᶠ n in atTop, ∀ h : RLSVector 3,
      MixedLocalDirectionBall H h →
      QubitOracle.blochNormSq (mixedLocalAlternative theta N n h) ≤
        1 - (1 - QubitOracle.blochNormSq theta) / 2 := by
  have hEnvelope := mixedLocalInteriorEnvelope_tendsto_zero N H hScale
  have hHalfMargin : 0 < (1 - QubitOracle.blochNormSq theta) / 2 := by
    nlinarith
  have hSmall : ∀ᶠ n in atTop,
      mixedLocalInteriorEnvelope N H n <
        (1 - QubitOracle.blochNormSq theta) / 2 :=
    (tendsto_order.1 hEnvelope).2 _ hHalfMargin
  filter_upwards [hSmall] with n hn
  intro h hBall
  have hUpper := mixedLocalAlternative_blochNormSq_le
    theta h N H n hInterior hBall
  nlinarith

/-- In particular, every local alternative is physical and strictly interior
for all sufficiently large rows. -/
theorem mixedLocalAlternative_eventually_uniform_interior
    (theta : RLSVector 3) (N : ℕ → ℕ) (H : ℝ)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hScale : Tendsto (mixedLocalScale N) atTop (nhds 0)) :
    ∀ᶠ n in atTop, ∀ h : RLSVector 3,
      MixedLocalDirectionBall H h →
      QubitOracle.blochNormSq (mixedLocalAlternative theta N n h) < 1 := by
  filter_upwards
    [mixedLocalAlternative_eventually_uniform_interior_margin
      theta N H hInterior hScale] with n hn
  intro h hBall
  have hMarginPositive : 0 < (1 - QubitOracle.blochNormSq theta) / 2 := by
    nlinarith
  exact lt_of_le_of_lt (hn h hBall) (by nlinarith)

/-- Exact common denominator margin used by all interior Bures/fidelity
remainder constants. -/
theorem mixedLocalAlternative_eventually_uniform_remainder_margin
    (theta : RLSVector 3) (N : ℕ → ℕ) (H : ℝ)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hScale : Tendsto (mixedLocalScale N) atTop (nhds 0)) :
    ∀ᶠ n in atTop, ∀ h : RLSVector 3,
      MixedLocalDirectionBall H h →
      (1 - QubitOracle.blochNormSq theta) / 2 ≤
        1 - QubitOracle.blochNormSq (mixedLocalAlternative theta N n h) ∧
      0 < 1 - QubitOracle.blochNormSq
        (mixedLocalAlternative theta N n h) := by
  filter_upwards
    [mixedLocalAlternative_eventually_uniform_interior_margin
      theta N H hInterior hScale] with n hn
  intro h hBall
  have hHalfPositive : 0 < (1 - QubitOracle.blochNormSq theta) / 2 := by
    nlinarith
  constructor <;> nlinarith [hn h hBall]

/-! ## Uniform deterministic pilot consistency -/

/-- A Euclidean-ball direction has every coordinate bounded by `H`. -/
theorem mixedLocalDirection_coordinate_abs_le
    (H : ℝ) (h : RLSVector 3) (hH : 0 ≤ H)
    (hBall : MixedLocalDirectionBall H h) (j : Fin 3) :
    |h j| ≤ H := by
  have hjSq : h j ^ 2 ≤ H ^ 2 := by
    fin_cases j <;>
      simp [MixedLocalDirectionBall, QubitOracle.blochNormSq,
        Fin.sum_univ_succ] at hBall ⊢ <;>
      nlinarith [sq_nonneg (h 0), sq_nonneg (h 1), sq_nonneg (h 2)]
  exact (abs_le).2 ⟨by nlinarith, by nlinarith⟩

/-- Concrete local pilot good event.  The pilot coordinate error relative to
the actual local truth is at most the local `1/sqrt(N_n)` scale. -/
def MixedUniformLocalPilotGood
    (theta : RLSVector 3) (N : ℕ → ℕ) (n : ℕ)
    (h : RLSVector 3) (omega : PauliPilotConsistencySampleSpace) : Prop :=
  ∀ j : Fin 3,
    |polynomialPilotEstimator n omega j -
      mixedLocalAlternative theta N n h j| ≤ |mixedLocalScale N n|

/-- The corresponding explicit bad event.  Its uniform probability is exactly
part of the one residual probability-envelope contract below. -/
def mixedUniformLocalPilotBadEvent
    (theta : RLSVector 3) (N : ℕ → ℕ) (n : ℕ)
    (h : RLSVector 3) : Set PauliPilotConsistencySampleSpace :=
  {omega | ¬ MixedUniformLocalPilotGood theta N n h omega}

/-- Deterministic local-shift correction: on the local good event the pilot is
close to the fixed center `theta`, uniformly over the compact direction ball. -/
theorem mixedUniformLocalPilotGood_coordinate_error_le
    (theta : RLSVector 3) (N : ℕ → ℕ) (H : ℝ) (n : ℕ)
    (h : RLSVector 3) (omega : PauliPilotConsistencySampleSpace)
    (hH : 0 ≤ H) (hBall : MixedLocalDirectionBall H h)
    (hGood : MixedUniformLocalPilotGood theta N n h omega)
    (j : Fin 3) :
    |polynomialPilotEstimator n omega j - theta j| ≤
      |mixedLocalScale N n| * (1 + H) := by
  have hDirection := mixedLocalDirection_coordinate_abs_le H h hH hBall j
  have hShift :
      |mixedLocalAlternative theta N n h j - theta j| ≤
        |mixedLocalScale N n| * H := by
    simp only [mixedLocalAlternative, add_sub_cancel_left, abs_mul]
    exact mul_le_mul_of_nonneg_left hDirection (abs_nonneg _)
  calc
    |polynomialPilotEstimator n omega j - theta j| =
        |(polynomialPilotEstimator n omega j -
            mixedLocalAlternative theta N n h j) +
          (mixedLocalAlternative theta N n h j - theta j)| := by
            congr 1
            ring
    _ ≤ |polynomialPilotEstimator n omega j -
          mixedLocalAlternative theta N n h j| +
        |mixedLocalAlternative theta N n h j - theta j| := abs_add_le _ _
    _ ≤ |mixedLocalScale N n| + |mixedLocalScale N n| * H :=
      add_le_add (hGood j) hShift
    _ = |mixedLocalScale N n| * (1 + H) := by ring

/-- The common coordinate envelope for all local-good pilots. -/
noncomputable def mixedUniformLocalPilotCoordinateEnvelope
    (N : ℕ → ℕ) (H : ℝ) (n : ℕ) : ℝ :=
  |mixedLocalScale N n| * (1 + H)

/-- The common local-pilot coordinate envelope vanishes. -/
theorem mixedUniformLocalPilotCoordinateEnvelope_tendsto_zero
    (N : ℕ → ℕ) (H : ℝ)
    (hScale : Tendsto (mixedLocalScale N) atTop (nhds 0)) :
    Tendsto (mixedUniformLocalPilotCoordinateEnvelope N H)
      atTop (nhds 0) := by
  have hProduct := hScale.abs.mul
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 + H : ℝ))
      atTop (nhds (1 + H)))
  change Tendsto
    (fun n => |mixedLocalScale N n| * (1 + H)) atTop (nhds 0)
  simpa using hProduct

/-- Uniform coordinate consistency over every local direction and every local
good pilot path.  No probability statement is used here. -/
theorem mixedUniformLocalPilotGood_uniform_coordinate_consistency
    (theta : RLSVector 3) (N : ℕ → ℕ) (H : ℝ)
    (hH : 0 ≤ H)
    (hScale : Tendsto (mixedLocalScale N) atTop (nhds 0))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ n in atTop, ∀ h : RLSVector 3,
      MixedLocalDirectionBall H h →
      ∀ omega : PauliPilotConsistencySampleSpace,
        MixedUniformLocalPilotGood theta N n h omega →
        ∀ j : Fin 3,
          |polynomialPilotEstimator n omega j - theta j| < epsilon := by
  have hEnvelope :=
    mixedUniformLocalPilotCoordinateEnvelope_tendsto_zero N H hScale
  have hEnvelopeLt : ∀ᶠ n in atTop,
      mixedUniformLocalPilotCoordinateEnvelope N H n < epsilon :=
    (tendsto_order.1 hEnvelope).2 epsilon hepsilon
  filter_upwards [hEnvelopeLt] with n hn
  intro h hBall omega hGood j
  exact lt_of_le_of_lt
    (mixedUniformLocalPilotGood_coordinate_error_le
      theta N H n h omega hH hBall hGood j) hn

/-! ## Uniform selected-frame quadratic risk -/

/-- General sequential-contradiction lemma: coordinate envelopes shrinking to
zero give one common selected-frame conditional-risk envelope. -/
theorem mixedSelectedFrameConditionalScaledRisk_uniform_of_coordinateEnvelope
    (b theta : RLSVector 3) (qFinal : ℕ → ℕ)
    (hqFinal : ∀ n, 0 < qFinal n)
    (hPositive : 0 < QubitOracle.blochNormSq theta)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (envelope : ℕ → ℝ)
    (hEnvelopeNonnegative : ∀ᶠ n in atTop, 0 ≤ envelope n)
    (hEnvelope : Tendsto envelope atTop (nhds 0))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ n in atTop, ∀ x : RLSVector 3,
      (∀ j : Fin 3, |x j - theta j| ≤ envelope n) →
      |mixedFrameConditionalScaledQuadraticRisk (q := qFinal n) theta
          (mixedPilotSelectedLocalFrame b x) - 9 / 4| < epsilon := by
  classical
  by_contra hUniform
  let Bad : ℕ → RLSVector 3 → Prop := fun n x =>
    (∀ j : Fin 3, |x j - theta j| ≤ envelope n) ∧
      epsilon ≤
        |mixedFrameConditionalScaledQuadraticRisk (q := qFinal n) theta
            (mixedPilotSelectedLocalFrame b x) - 9 / 4|
  have hFar : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ x : RLSVector 3, Bad n x := by
    intro N
    by_contra hN
    push_neg at hN
    apply hUniform
    filter_upwards [eventually_ge_atTop N] with n hn
    intro x hx
    apply lt_of_not_ge
    intro hge
    exact hN n hn x ⟨hx, hge⟩
  let chosen : ℕ → RLSVector 3 := fun n =>
    if hexists : ∃ x : RLSVector 3, Bad n x then
      Classical.choose hexists
    else theta
  have hChosenBound : ∀ᶠ n in atTop,
      ∀ j : Fin 3, |chosen n j - theta j| ≤ envelope n := by
    filter_upwards [hEnvelopeNonnegative] with n hn
    intro j
    by_cases hexists : ∃ x : RLSVector 3, Bad n x
    · simpa [chosen, hexists] using (Classical.choose_spec hexists).1 j
    · simp [chosen, hexists, hn]
  have hChosenTendsto (j : Fin 3) :
      Tendsto (fun n => chosen n j) atTop (nhds (theta j)) := by
    rw [Metric.tendsto_atTop]
    intro delta hdelta
    have hEnvelopeLt : ∀ᶠ n in atTop, envelope n < delta :=
      (tendsto_order.1 hEnvelope).2 delta hdelta
    have hBoth : ∀ᶠ n in atTop,
        (∀ j : Fin 3, |chosen n j - theta j| ≤ envelope n) ∧
          envelope n < delta :=
      hChosenBound.and hEnvelopeLt
    rcases (eventually_atTop.1 hBoth) with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hAtN := hN n hn
    simpa [Real.dist_eq] using lt_of_le_of_lt (hAtN.1 j) hAtN.2
  have hRisk := mixedFrameConditionalScaledRisk_tendsto_of_coordinatewise
    b theta chosen qFinal hqFinal hChosenTendsto
    hPositive hInterior hSeed
  have hRiskClose : ∀ᶠ n in atTop,
      |mixedFrameConditionalScaledQuadraticRisk (q := qFinal n) theta
          (mixedPilotSelectedLocalFrame b (chosen n)) - 9 / 4| < epsilon := by
    simpa [Real.dist_eq] using
      (Metric.tendsto_atTop.1 hRisk epsilon hepsilon)
  rcases (eventually_atTop.1 hRiskClose) with ⟨N, hN⟩
  rcases hFar N with ⟨n, hn, x, hx⟩
  have hexists : ∃ y : RLSVector 3, Bad n y := ⟨x, hx⟩
  have hChosenBad : Bad n (chosen n) := by
    simpa [chosen, hexists] using (Classical.choose_spec hexists)
  exact (not_lt_of_ge hChosenBad.2) (hN n hn)

/-- The selected-frame conditional quadratic risk converges uniformly over all
compact local directions and all local-good pilot paths.  The risk is evaluated
at the frozen center `theta`; transfer to the varying local truth and exact
loss is the single probability-envelope boundary below. -/
theorem mixedUniformLocalGoodPilot_frozenCenter_scaledQuadraticRisk
    (b theta : RLSVector 3) (N : ℕ → ℕ) (H : ℝ)
    (qFinal : ℕ → ℕ) (hqFinal : ∀ n, 0 < qFinal n)
    (hH : 0 ≤ H)
    (hScale : Tendsto (mixedLocalScale N) atTop (nhds 0))
    (hPositive : 0 < QubitOracle.blochNormSq theta)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ n in atTop, ∀ h : RLSVector 3,
      MixedLocalDirectionBall H h →
      ∀ omega : PauliPilotConsistencySampleSpace,
        MixedUniformLocalPilotGood theta N n h omega →
        |mixedFrameConditionalScaledQuadraticRisk (q := qFinal n) theta
            (mixedPilotSelectedLocalFrame b
              (polynomialPilotEstimator n omega)) - 9 / 4| < epsilon := by
  have hEnvelope :=
    mixedUniformLocalPilotCoordinateEnvelope_tendsto_zero N H hScale
  have hEnvelopeNonnegative : ∀ᶠ n in atTop,
      0 ≤ mixedUniformLocalPilotCoordinateEnvelope N H n := by
    exact Eventually.of_forall fun n =>
      mul_nonneg (abs_nonneg _) (by nlinarith)
  have hUniform :=
    mixedSelectedFrameConditionalScaledRisk_uniform_of_coordinateEnvelope
      b theta qFinal hqFinal hPositive hInterior hSeed
      (mixedUniformLocalPilotCoordinateEnvelope N H)
      hEnvelopeNonnegative hEnvelope epsilon hepsilon
  filter_upwards [hUniform] with n hn
  intro h hBall omega hGood
  apply hn
  intro j
  exact mixedUniformLocalPilotGood_coordinate_error_le
    theta N H n h omega hH hBall hGood j

/-! ## The single residual finite-law probability envelope -/

/-- The two exact losses whose local quadratic term is `(1/4)||h||²`. -/
inductive MixedUniformLocalExactLoss
  | squaredBures
  | ordinaryInfidelity
  deriving DecidableEq

/-- Concrete total-observation-scaled exact risk under a supplied local truth. -/
noncomputable def mixedUniformLocalTotalScaledExactRisk
    (loss : MixedUniformLocalExactLoss)
    (z b : RLSVector 3) (n : ℕ) : ℝ≥0∞ :=
  match loss with
  | .squaredBures =>
      mixedPolynomialTotalObservationScaledExpectedExactBuresRisk z b n
  | .ordinaryInfidelity =>
      mixedPolynomialTotalObservationScaledExpectedOrdinaryInfidelityRisk z b n

/-- The exact residual probability contract.

For every positive epsilon, a deterministic `epsilon` upper bound on every
local-good frozen-center conditional quadratic risk transfers, under the
concrete locally varying finite joint law, to a `2*epsilon` upper bound for
both total-scaled exact losses.  Thus this contract contains precisely:

* the uniform Hoeffding probability of `mixedUniformLocalPilotBadEvent`;
* the finite pilot/final joint-law averaging under `theta_n(h)`;
* the bad-branch bounded-loss estimate;
* the uniformly interior exact Bures and ordinary-infidelity remainders.

It does not contain the final `9/4` limsup conclusion. -/
structure MixedUniformLocalProbabilityEnvelope
    (theta b : RLSVector 3) (N : ℕ → ℕ) (H : ℝ)
    (qFinal : ℕ → ℕ) : Prop where
  transfer_good_branch_to_exact_total :
    ∀ epsilon : ℝ, 0 < epsilon →
      (∀ᶠ n in atTop, ∀ h : RLSVector 3,
        MixedLocalDirectionBall H h →
        ∀ omega : PauliPilotConsistencySampleSpace,
          MixedUniformLocalPilotGood theta N n h omega →
          mixedFrameConditionalScaledQuadraticRisk (q := qFinal n) theta
              (mixedPilotSelectedLocalFrame b
                (polynomialPilotEstimator n omega)) ≤
            9 / 4 + epsilon) →
      ∀ᶠ n in atTop, ∀ loss : MixedUniformLocalExactLoss,
        ∀ h : RLSVector 3, MixedLocalDirectionBall H h →
          mixedUniformLocalTotalScaledExactRisk loss
              (mixedLocalAlternative theta N n h) b n ≤
            ENNReal.ofReal (9 / 4 + 2 * epsilon)

/-- Epsilon characterization of
`limsup_n sup_{||h||≤H} risk_n(theta_n(h)) ≤ constant`, avoiding any
measurability assertion for the uncountable supremum. -/
def MixedUniformLocalRiskLimsupLE
    (loss : MixedUniformLocalExactLoss)
    (theta b : RLSVector 3) (N : ℕ → ℕ) (H constant : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∀ᶠ n in atTop, ∀ h : RLSVector 3,
      MixedLocalDirectionBall H h →
      mixedUniformLocalTotalScaledExactRisk loss
          (mixedLocalAlternative theta N n h) b n ≤
        ENNReal.ofReal (constant + epsilon)

/-- Deterministic and model conditions for the concrete frozen polynomial row.
The only non-model premise in the upper endpoint remains
`MixedUniformLocalProbabilityEnvelope`. -/
structure MixedUniformLocalPolynomialConditions
    (theta b : RLSVector 3) (N : ℕ → ℕ) (H : ℝ)
    (qFinal : ℕ → ℕ) : Prop
    extends MixedFrozenPolynomialEndpointConditions theta b where
  radius_nonnegative : 0 ≤ H
  local_scale_tendsto_zero : Tendsto (mixedLocalScale N) atTop (nhds 0)
  final_allocation_positive : ∀ n, 0 < qFinal n

/-- Uniform local squared-Bures upper bound `9/4`, conditional only on the
single finite-law probability envelope. -/
theorem mixedUniformLocalSquaredBuresRisk_limsup_le_nine_fourths
    (theta b : RLSVector 3) (N : ℕ → ℕ) (H : ℝ)
    (qFinal : ℕ → ℕ)
    (h : MixedUniformLocalPolynomialConditions theta b N H qFinal)
    (probabilityEnvelope :
      MixedUniformLocalProbabilityEnvelope theta b N H qFinal) :
    MixedUniformLocalRiskLimsupLE .squaredBures theta b N H (9 / 4) := by
  intro delta hdelta
  let epsilon : ℝ := delta / 2
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    linarith
  have hGoodAbs :=
    mixedUniformLocalGoodPilot_frozenCenter_scaledQuadraticRisk
      b theta N H qFinal h.final_allocation_positive
      h.radius_nonnegative h.local_scale_tendsto_zero
      h.positive h.interior h.seed epsilon hepsilon
  have hGoodUpper : ∀ᶠ n in atTop, ∀ localDirection : RLSVector 3,
      MixedLocalDirectionBall H localDirection →
      ∀ omega : PauliPilotConsistencySampleSpace,
        MixedUniformLocalPilotGood theta N n localDirection omega →
        mixedFrameConditionalScaledQuadraticRisk (q := qFinal n) theta
            (mixedPilotSelectedLocalFrame b
              (polynomialPilotEstimator n omega)) ≤ 9 / 4 + epsilon := by
    filter_upwards [hGoodAbs] with n hn
    intro localDirection hBall omega hPilotGood
    have hAbs := hn localDirection hBall omega hPilotGood
    have hOneSide := le_abs_self
      (mixedFrameConditionalScaledQuadraticRisk (q := qFinal n) theta
        (mixedPilotSelectedLocalFrame b
          (polynomialPilotEstimator n omega)) - 9 / 4)
    linarith
  have hExact := probabilityEnvelope.transfer_good_branch_to_exact_total
    epsilon hepsilon hGoodUpper
  filter_upwards [hExact] with n hn
  intro localDirection hBall
  have hBound := hn .squaredBures localDirection hBall
  convert hBound using 1 <;> dsimp [epsilon] <;> ring

/-- Uniform local ordinary-infidelity upper bound `9/4`. -/
theorem mixedUniformLocalOrdinaryInfidelityRisk_limsup_le_nine_fourths
    (theta b : RLSVector 3) (N : ℕ → ℕ) (H : ℝ)
    (qFinal : ℕ → ℕ)
    (h : MixedUniformLocalPolynomialConditions theta b N H qFinal)
    (probabilityEnvelope :
      MixedUniformLocalProbabilityEnvelope theta b N H qFinal) :
    MixedUniformLocalRiskLimsupLE .ordinaryInfidelity theta b N H (9 / 4) := by
  intro delta hdelta
  let epsilon : ℝ := delta / 2
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    linarith
  have hGoodAbs :=
    mixedUniformLocalGoodPilot_frozenCenter_scaledQuadraticRisk
      b theta N H qFinal h.final_allocation_positive
      h.radius_nonnegative h.local_scale_tendsto_zero
      h.positive h.interior h.seed epsilon hepsilon
  have hGoodUpper : ∀ᶠ n in atTop, ∀ localDirection : RLSVector 3,
      MixedLocalDirectionBall H localDirection →
      ∀ omega : PauliPilotConsistencySampleSpace,
        MixedUniformLocalPilotGood theta N n localDirection omega →
        mixedFrameConditionalScaledQuadraticRisk (q := qFinal n) theta
            (mixedPilotSelectedLocalFrame b
              (polynomialPilotEstimator n omega)) ≤ 9 / 4 + epsilon := by
    filter_upwards [hGoodAbs] with n hn
    intro localDirection hBall omega hPilotGood
    have hAbs := hn localDirection hBall omega hPilotGood
    have hOneSide := le_abs_self
      (mixedFrameConditionalScaledQuadraticRisk (q := qFinal n) theta
        (mixedPilotSelectedLocalFrame b
          (polynomialPilotEstimator n omega)) - 9 / 4)
    linarith
  have hExact := probabilityEnvelope.transfer_good_branch_to_exact_total
    epsilon hepsilon hGoodUpper
  filter_upwards [hExact] with n hn
  intro localDirection hBall
  have hBound := hn .ordinaryInfidelity localDirection hBall
  convert hBound using 1 <;> dsimp [epsilon] <;> ring


end QubitOracle.Paper
