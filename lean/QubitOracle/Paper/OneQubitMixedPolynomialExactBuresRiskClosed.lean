import QubitOracle.Paper.OneQubitMixedFinalEstimatorFourthMoment
import QubitOracle.Paper.OneQubitMixedBuresFidelityLocalRemainder
import QubitOracle.Paper.OneQubitMixedPolynomialQuadraticRiskClosed
import QubitOracle.Paper.OneQubitMixedBuresRiskTransfer

/-!
# Safeguarded exact Bures risk for the concrete mixed-qubit polynomial protocol

This file performs the deterministic and conditional-final-row part of the
exact-loss transfer.  The final estimator is made physical by retaining the
three-axis linear estimate inside the closed Bloch ball and returning the
maximally mixed Bloch vector outside it.

The loss below is the nonnegative realization of the exact Bloch Bures
formula.  The `max 0` is harmless on physical pairs, and also makes the
finite-row argument independent of a separate global fidelity-range lemma.
On the local Taylor event, contraction of `max 0` toward the nonnegative
quadratic comparator gives exactly the source-level Bures remainder.

The final declarations isolate the one remaining paper-level operation:
identifying the exact finite joint-row risk with its common-pilot-space
conditional average.  No asymptotic risk statement is used in that boundary.
-/

open scoped BigOperators ENNReal
open Filter Topology MeasureTheory

namespace QubitOracle
namespace Paper

noncomputable section

/-! ## The implementable physical safeguard -/

/-- Keep the linear three-axis estimate when it is physical; otherwise return
the maximally mixed Bloch vector. -/
def mixedFrameSafeguardedFinalEstimator
    {q : ℕ} (R : Matrix (Fin 3) (Fin 3) ℝ)
    (path : PauliPilotPath q) : Fin 3 → ℝ :=
  let estimate := mixedFrameFinalLinearEstimator R path
  if blochNormSq estimate ≤ 1 then estimate else 0

/-- The safeguarded estimator always belongs to the closed Bloch ball. -/
theorem mixedFrameSafeguardedFinalEstimator_physical
    {q : ℕ} (R : Matrix (Fin 3) (Fin 3) ℝ)
    (path : PauliPilotPath q) :
    blochNormSq (mixedFrameSafeguardedFinalEstimator R path) ≤ 1 := by
  unfold mixedFrameSafeguardedFinalEstimator
  dsimp only
  split_ifs with h
  · exact h
  · simp [blochNormSq]

/-- The two names for the frame-reconstructed linear estimator are
definitionally the same. -/
theorem mixedFrameFinalLinearEstimator_eq_frameLinearEstimate
    {q : ℕ} (R : Matrix (Fin 3) (Fin 3) ℝ)
    (path : PauliPilotPath q) :
    mixedFrameFinalLinearEstimator R path =
      mixedFrameLinearEstimate R path := by
  rfl

/-- Add the linear estimation error back to the truth. -/
theorem mixedFrameFinalLinearError_add_truth
    {q : ℕ} (theta : Fin 3 → ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (path : PauliPilotPath q) :
    theta + mixedFrameFinalLinearError theta R path =
      mixedFrameFinalLinearEstimator R path := by
  ext j
  simp [mixedFrameFinalLinearError]

/-- On the explicit local Taylor ball, the linear estimate is already in the
open Bloch ball, so the safeguard does nothing. -/
theorem mixedFrameSafeguardedFinalEstimator_eq_linear_of_local
    {q : ℕ} {theta : Fin 3 → ℝ}
    {R : Matrix (Fin 3) (Fin 3) ℝ}
    {path : PauliPilotPath q}
    (hInterior : blochNormSq theta < 1)
    (hLocal : mixedFrameFinalErrorNorm theta R path ≤
      mixedBuresFidelityLocalRadius theta) :
    mixedFrameSafeguardedFinalEstimator R path =
      mixedFrameFinalLinearEstimator R path := by
  have hInside := mixedBuresFidelityLocalRadius_keeps_inside
    (theta := theta)
    (delta := mixedFrameFinalLinearError theta R path)
    hInterior hLocal
  rw [mixedFrameFinalLinearError_add_truth theta R path] at hInside
  simp [mixedFrameSafeguardedFinalEstimator, hInside.le]

/-! ## Exact physical loss and convention conversion -/

/-- Nonnegative exact squared-Bures loss of the physical safeguard. -/
def mixedFrameSafeguardedSquaredBuresLoss
    {q : ℕ} (theta : Fin 3 → ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (path : PauliPilotPath q) : ℝ :=
  max 0 (mixedQubitBlochBuresSqBetween theta
    (mixedFrameSafeguardedFinalEstimator R path))

/-- Nonnegative root-infidelity loss for the same estimator. -/
def mixedFrameSafeguardedRootInfidelityLoss
    {q : ℕ} (theta : Fin 3 → ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (path : PauliPilotPath q) : ℝ :=
  max 0 (mixedQubitBlochRootInfidelityBetween theta
    (mixedFrameSafeguardedFinalEstimator R path))

theorem mixedFrameSafeguardedSquaredBuresLoss_nonnegative
    {q : ℕ} (theta : Fin 3 → ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (path : PauliPilotPath q) :
    0 ≤ mixedFrameSafeguardedSquaredBuresLoss theta R path := by
  exact le_max_left _ _

/-- The exact Bloch formula has the global squared-Bures upper bound `2`.
The proof uses no local expansion. -/
theorem mixedFrameSafeguardedSquaredBuresLoss_le_two
    {q : ℕ} (theta : Fin 3 → ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (path : PauliPilotPath q) :
    mixedFrameSafeguardedSquaredBuresLoss theta R path ≤ 2 := by
  let sigma := mixedFrameSafeguardedFinalEstimator R path
  let delta : Fin 3 → ℝ := sigma - theta
  have hAdd : theta + delta = sigma := by
    ext j
    simp [delta, sigma]
  have hRaw : mixedQubitBlochBuresSqBetween theta sigma ≤ 2 := by
    rw [← hAdd,
      mixedQubitBlochBuresSqBetween_add_eq_mixedBlochBuresSq]
    simpa [mixedBlochBuresSq] using
      (mixedBlochBuresSq_le_two theta delta)
  unfold mixedFrameSafeguardedSquaredBuresLoss
  exact max_le (by norm_num) hRaw

/-- Squared Bures is exactly twice root infidelity, including after the
nonnegative realization.  Thus a `9/4` squared-Bures constant corresponds to
`9/8` for `1 - sqrt(F)` under the same sample-size scaling. -/
theorem mixedFrameSafeguardedSquaredBuresLoss_eq_two_mul_rootInfidelity
    {q : ℕ} (theta : Fin 3 → ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (path : PauliPilotPath q) :
    mixedFrameSafeguardedSquaredBuresLoss theta R path =
      2 * mixedFrameSafeguardedRootInfidelityLoss theta R path := by
  let x := mixedQubitBlochRootInfidelityBetween theta
    (mixedFrameSafeguardedFinalEstimator R path)
  have hRaw : mixedQubitBlochBuresSqBetween theta
      (mixedFrameSafeguardedFinalEstimator R path) = 2 * x := by
    rfl
  rw [mixedFrameSafeguardedSquaredBuresLoss,
    mixedFrameSafeguardedRootInfidelityLoss, hRaw]
  by_cases hx : 0 ≤ x
  · rw [max_eq_right hx, max_eq_right (mul_nonneg (by norm_num) hx)]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have htwo : 2 * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by norm_num) hx'
    rw [max_eq_left hx', max_eq_left htwo]
    ring

/-! ## Quadratic domination -/

theorem mixedInteriorBuresQuadraticLoss_nonnegative_exact
    {theta error : Fin 3 → ℝ}
    (hInterior : blochNormSq theta < 1) :
    0 ≤ mixedInteriorBuresQuadraticLoss theta error := by
  have hGap : 0 < 1 - blochNormSq theta := by linarith
  unfold mixedInteriorBuresQuadraticLoss
  exact add_nonneg
    (mul_nonneg (by positivity) (by
      unfold blochNormSq
      exact Finset.sum_nonneg fun j _ => sq_nonneg _))
    (mul_nonneg (by positivity) (sq_nonneg _))

/-- Interior Bures quadratic loss is bounded by Euclidean squared error divided
by four times the radial gap. -/
theorem mixedInteriorBuresQuadraticLoss_le_normSq_div_gap
    {theta error : Fin 3 → ℝ}
    (hInterior : blochNormSq theta < 1) :
    mixedInteriorBuresQuadraticLoss theta error ≤
      blochNormSq error / (4 * (1 - blochNormSq theta)) := by
  let gap : ℝ := 1 - blochNormSq theta
  have hGap : 0 < gap := by
    dsimp [gap]
    linarith
  have hCauchy := bloch_cauchy_schwarz theta error
  have hIdentity :
      mixedInteriorBuresQuadraticLoss theta error * (4 * gap) =
        gap * blochNormSq error + blochDot theta error ^ 2 := by
    unfold mixedInteriorBuresQuadraticLoss
    change (((4 : ℝ)⁻¹ * blochNormSq error +
      (4 * gap)⁻¹ * blochDot theta error ^ 2) * (4 * gap)) =
        gap * blochNormSq error + blochDot theta error ^ 2
    field_simp [hGap.ne'] <;> ring
  apply (le_div_iff₀ (mul_pos (by norm_num) hGap)).2
  rw [hIdentity]
  dsimp [gap]
  nlinarith

private theorem div_le_sq_div_mul_sq
    {x a eta : ℝ} (hx : 0 ≤ x) (ha : 0 < a) (hEta : 0 < eta)
    (hEtaSq : eta ^ 2 ≤ x) :
    x / a ≤ x ^ 2 / (a * eta ^ 2) := by
  apply (le_div_iff₀ (mul_pos ha (sq_pos_of_pos hEta))).2
  have hCancel : (x / a) * (a * eta ^ 2) = x * eta ^ 2 := by
    field_simp [ha.ne'] <;> ring
  rw [hCancel]
  nlinarith

/-- On the complement of the local ball, the quadratic comparator is paid for
by the fourth squared-error moment. -/
theorem mixedInteriorBuresQuadraticLoss_le_fourth_tail
    {q : ℕ} {theta : Fin 3 → ℝ}
    {R : Matrix (Fin 3) (Fin 3) ℝ}
    {path : PauliPilotPath q} {eta : ℝ}
    (hInterior : blochNormSq theta < 1)
    (hEta : 0 < eta)
    (hBad : eta < mixedFrameFinalErrorNorm theta R path) :
    mixedInteriorBuresQuadraticLoss theta
        (mixedFrameFinalLinearError theta R path) ≤
      mixedFrameFinalSquaredError theta R path ^ 2 /
        (4 * (1 - blochNormSq theta) * eta ^ 2) := by
  let e2 := mixedFrameFinalSquaredError theta R path
  have he2 : 0 ≤ e2 := mixedFrameFinalSquaredError_nonnegative theta R path
  have hNormSq := mixedFrameFinalErrorNorm_sq theta R path
  have hEtaSq : eta ^ 2 ≤ e2 := by
    nlinarith [mixedBlochEuclideanNorm_nonnegative
      (mixedFrameFinalLinearError theta R path)]
  have hBase := mixedInteriorBuresQuadraticLoss_le_normSq_div_gap
    (theta := theta)
    (error := mixedFrameFinalLinearError theta R path) hInterior
  have hGap : 0 < 4 * (1 - blochNormSq theta) := by
    positivity
  have hFourth := div_le_sq_div_mul_sq he2 hGap hEta hEtaSq
  exact hBase.trans (by
    simpa [e2, mixedFrameFinalSquaredError, mul_assoc] using hFourth)

private theorem abs_max_zero_sub_le_abs_sub_of_nonnegative
    {x y : ℝ} (hy : 0 ≤ y) :
    |max 0 x - y| ≤ |x - y| := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_right hx]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [max_eq_left hx']
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith

/-! ## Pathwise exact-loss transfer -/

/-- A pointwise envelope whose expectation is controlled by the proved third
and fourth moments and the fourth-moment tail estimate. -/
def mixedFrameExactBuresTransferIntegrand
    {q : ℕ} (theta : Fin 3 → ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (path : PauliPilotPath q) : ℝ :=
  let gap := 1 - blochNormSq theta
  let eta := mixedBuresFidelityLocalRadius theta
  let d := mixedFrameFinalErrorNorm theta R path
  let e2 := mixedFrameFinalSquaredError theta R path
  d ^ 3 / gap ^ 2 + 2 * e2 ^ 2 / gap ^ 3 +
    (if eta < d then 2 else 0) +
    e2 ^ 2 / (4 * gap * eta ^ 2)

theorem mixedFrameExactBuresTransferIntegrand_nonnegative
    {q : ℕ} {theta : Fin 3 → ℝ}
    (hInterior : blochNormSq theta < 1)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (path : PauliPilotPath q) :
    0 ≤ mixedFrameExactBuresTransferIntegrand theta R path := by
  have hGap : 0 < 1 - blochNormSq theta := by linarith
  have hEta := mixedBuresFidelityLocalRadius_pos hInterior
  have hd := mixedBlochEuclideanNorm_nonnegative
    (mixedFrameFinalLinearError theta R path)
  have he2 := mixedFrameFinalSquaredError_nonnegative theta R path
  unfold mixedFrameExactBuresTransferIntegrand
  dsimp only
  split_ifs <;> positivity

/-- The safeguarded exact Bures loss and the unsafeguarded linear quadratic
loss differ pointwise by the explicit moment integrand. -/
theorem mixedFrameSafeguardedBures_pointwise_transfer
    {q : ℕ} {theta : Fin 3 → ℝ}
    (hInterior : blochNormSq theta < 1)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (path : PauliPilotPath q) :
    |mixedFrameSafeguardedSquaredBuresLoss theta R path -
        mixedInteriorBuresQuadraticLoss theta
          (mixedFrameFinalLinearError theta R path)| ≤
      mixedFrameExactBuresTransferIntegrand theta R path := by
  let gap := 1 - blochNormSq theta
  let eta := mixedBuresFidelityLocalRadius theta
  let d := mixedFrameFinalErrorNorm theta R path
  let e2 := mixedFrameFinalSquaredError theta R path
  let error := mixedFrameFinalLinearError theta R path
  let quadratic := mixedInteriorBuresQuadraticLoss theta error
  have hGap : 0 < gap := by
    dsimp [gap]
    linarith
  have hEta : 0 < eta := by
    exact mixedBuresFidelityLocalRadius_pos hInterior
  have hQuadratic : 0 ≤ quadratic := by
    exact mixedInteriorBuresQuadraticLoss_nonnegative_exact hInterior
  have he2 : 0 ≤ e2 := by
    exact mixedFrameFinalSquaredError_nonnegative theta R path
  have hd : 0 ≤ d := by
    exact mixedBlochEuclideanNorm_nonnegative error
  have hFourth : d ^ 4 = e2 ^ 2 := by
    have hSq := mixedFrameFinalErrorNorm_sq theta R path
    dsimp [d, e2] at hSq ⊢
    nlinarith
  by_cases hBad : eta < d
  · have hLossUpper :=
      mixedFrameSafeguardedSquaredBuresLoss_le_two theta R path
    have hLossNonnegative :=
      mixedFrameSafeguardedSquaredBuresLoss_nonnegative theta R path
    have hQuadraticTail := mixedInteriorBuresQuadraticLoss_le_fourth_tail
      (theta := theta) (R := R) (path := path) hInterior hEta hBad
    have hAbs :
        |mixedFrameSafeguardedSquaredBuresLoss theta R path - quadratic| ≤
          mixedFrameSafeguardedSquaredBuresLoss theta R path + quadratic := by
      rw [abs_le]
      constructor <;> linarith
    have hLocalTerms :
        0 ≤ d ^ 3 / gap ^ 2 + 2 * e2 ^ 2 / gap ^ 3 := by
      positivity
    unfold mixedFrameExactBuresTransferIntegrand
    dsimp only
    rw [if_pos hBad]
    dsimp [quadratic, gap, eta, d, e2] at hAbs hLossUpper hQuadraticTail ⊢
    nlinarith
  · have hLocal : d ≤ eta := le_of_not_gt hBad
    have hSafeguard :=
      mixedFrameSafeguardedFinalEstimator_eq_linear_of_local
        (theta := theta) (R := R) (path := path) hInterior hLocal
    have hAdd := mixedFrameFinalLinearError_add_truth theta R path
    have hRemainder := mixedQubitBlochBuresSqBetween_add_local_remainder
      (theta := theta) (delta := error) hInterior hLocal
    have hRawRewrite :
        mixedQubitBlochBuresSqBetween theta
            (mixedFrameSafeguardedFinalEstimator R path) =
          mixedQubitBlochBuresSqBetween theta (theta + error) := by
      rw [hSafeguard, hAdd]
    have hContract :
        |mixedFrameSafeguardedSquaredBuresLoss theta R path - quadratic| ≤
          |mixedQubitBlochBuresSqBetween theta (theta + error) - quadratic| := by
      unfold mixedFrameSafeguardedSquaredBuresLoss
      rw [hRawRewrite]
      exact abs_max_zero_sub_le_abs_sub_of_nonnegative hQuadratic
    have hEnvelope :
        mixedBuresFidelityLocalRemainderEnvelope theta error =
          d ^ 3 / gap ^ 2 + 2 * e2 ^ 2 / gap ^ 3 := by
      unfold mixedBuresFidelityLocalRemainderEnvelope
      change d ^ 3 / gap ^ 2 + 2 * d ^ 4 / gap ^ 3 =
        d ^ 3 / gap ^ 2 + 2 * e2 ^ 2 / gap ^ 3
      rw [hFourth]
    unfold mixedFrameExactBuresTransferIntegrand
    dsimp only
    rw [if_neg hBad]
    dsimp [quadratic, gap, eta, d, e2, error] at hContract hRemainder hEnvelope ⊢
    rw [hEnvelope] at hRemainder
    have hLast :
        0 ≤ mixedFrameFinalSquaredError theta R path ^ 2 /
          (4 * (1 - blochNormSq theta) *
            mixedBuresFidelityLocalRadius theta ^ 2) := by
      positivity
    nlinarith

/-! ## Exact finite product-law integration -/

private theorem pauliPilotFiniteExpectation_add_exact
    {q : ℕ} (z : Fin 3 → ℝ)
    (f g : PauliPilotPath q → ℝ) :
    pauliPilotFiniteExpectation z (fun path => f path + g path) =
      pauliPilotFiniteExpectation z f +
        pauliPilotFiniteExpectation z g := by
  unfold pauliPilotFiniteExpectation
  simp [mul_add, Finset.sum_add_distrib]

private theorem pauliPilotFiniteExpectation_const_mul_exact
    {q : ℕ} (z : Fin 3 → ℝ) (c : ℝ)
    (f : PauliPilotPath q → ℝ) :
    pauliPilotFiniteExpectation z (fun path => c * f path) =
      c * pauliPilotFiniteExpectation z f := by
  unfold pauliPilotFiniteExpectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro path hpath
  ring

private theorem pauliPilotFiniteExpectation_div_exact
    {q : ℕ} (z : Fin 3 → ℝ) (c : ℝ)
    (f : PauliPilotPath q → ℝ) :
    pauliPilotFiniteExpectation z (fun path => f path / c) =
      pauliPilotFiniteExpectation z f / c := by
  simpa [div_eq_mul_inv, mul_comm] using
    (pauliPilotFiniteExpectation_const_mul_exact z c⁻¹ f)

private theorem pauliPilotFiniteExpectation_mono_exact
    {q : ℕ} (z : Fin 3 → ℝ)
    (hPhysical : PauliPilotPhysicalBloch z)
    {f g : PauliPilotPath q → ℝ}
    (hfg : ∀ path, f path ≤ g path) :
    pauliPilotFiniteExpectation z f ≤
      pauliPilotFiniteExpectation z g := by
  unfold pauliPilotFiniteExpectation
  exact Finset.sum_le_sum fun path _ =>
    mul_le_mul_of_nonneg_left (hfg path)
      (pauliPilotPathMass_nonnegative z hPhysical path)

private theorem pauliPilotFiniteExpectation_abs_sub_le
    {q : ℕ} (z : Fin 3 → ℝ)
    (hPhysical : PauliPilotPhysicalBloch z)
    (f g bound : PauliPilotPath q → ℝ)
    (hPointwise : ∀ path, |f path - g path| ≤ bound path) :
    |pauliPilotFiniteExpectation z f -
        pauliPilotFiniteExpectation z g| ≤
      pauliPilotFiniteExpectation z bound := by
  have hTriangle :
      |pauliPilotFiniteExpectation z f -
          pauliPilotFiniteExpectation z g| ≤
        pauliPilotFiniteExpectation z (fun path => |f path - g path|) := by
    unfold pauliPilotFiniteExpectation
    rw [← Finset.sum_sub_distrib]
    have hRewrite :
        (∑ path : PauliPilotPath q,
            (pauliPilotPathMass z path * f path -
              pauliPilotPathMass z path * g path)) =
          ∑ path : PauliPilotPath q,
            pauliPilotPathMass z path * (f path - g path) := by
      apply Finset.sum_congr rfl
      intro path hpath
      ring
    rw [hRewrite]
    calc
      |∑ path : PauliPilotPath q,
          pauliPilotPathMass z path * (f path - g path)| ≤
          ∑ path : PauliPilotPath q,
            |pauliPilotPathMass z path * (f path - g path)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ path : PauliPilotPath q,
          pauliPilotPathMass z path * |f path - g path| := by
        apply Finset.sum_congr rfl
        intro path hpath
        rw [abs_mul,
          abs_of_nonneg
            (pauliPilotPathMass_nonnegative z hPhysical path)]
  exact hTriangle.trans
    (pauliPilotFiniteExpectation_mono_exact z hPhysical hPointwise)

private theorem pauliPilotFiniteExpectation_two_tail
    {q : ℕ} (theta : Fin 3 → ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ) (eta : ℝ) :
    pauliPilotFiniteExpectation (q := q) (qubitFrameCoordinates R theta)
        (fun path : PauliPilotPath q =>
          if eta < mixedFrameFinalErrorNorm theta R path then 2 else 0) =
      2 * mixedFrameFinalErrorTailMass (q := q) theta R eta := by
  unfold pauliPilotFiniteExpectation mixedFrameFinalErrorTailMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro path hpath
  by_cases hBad : eta < mixedFrameFinalErrorNorm theta R path
  · simp [hBad, mul_comm]
  · simp [hBad]

/-- Unscaled moment envelope for the conditional exact-loss transfer. -/
def mixedFrameExactBuresUnscaledMomentBound
    (theta : Fin 3 → ℝ) (q : ℕ) : ℝ :=
  let qR := (q : ℝ)
  let gap := 1 - blochNormSq theta
  let eta := mixedBuresFidelityLocalRadius theta
  (18 / (qR * Real.sqrt qR)) / gap ^ 2 +
    2 * (15 / qR ^ 2) / gap ^ 3 +
    2 * (15 / (qR ^ 2 * eta ^ 4)) +
    (15 / qR ^ 2) / (4 * gap * eta ^ 2)

/-- The explicit final product law integrates the pathwise envelope at the
announced `q^(-3/2)` and `q^(-2)` moment rates, uniformly in the orthonormal
frame. -/
theorem mixedFrameExactBuresTransferIntegrand_expectation_le
    {q : ℕ} (hq : 0 < q) (theta : Fin 3 → ℝ)
    (hInterior : blochNormSq theta < 1)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : MixedFrameOrthonormal R) :
    pauliPilotFiniteExpectation (q := q) (qubitFrameCoordinates R theta)
        (mixedFrameExactBuresTransferIntegrand (q := q) theta R) ≤
      mixedFrameExactBuresUnscaledMomentBound theta q := by
  let z := qubitFrameCoordinates R theta
  let gap := 1 - blochNormSq theta
  let eta := mixedBuresFidelityLocalRadius theta
  have hPhysical : PauliPilotPhysicalBloch theta := by
    unfold PauliPilotPhysicalBloch
    exact hInterior.le
  have hzPhysical := qubitFrameCoordinates_physical theta R hR hPhysical
  have hGap : 0 < gap := by
    dsimp [gap]
    linarith
  have hEta : 0 < eta := by
    exact mixedBuresFidelityLocalRadius_pos hInterior
  have hThird := mixedFrameFinalErrorNorm_thirdMoment_le
    hq theta R hR hPhysical
  have hFourth := mixedFrameFinalSquaredError_fourthMoment_le
    hq theta R hR hPhysical
  have hTail := mixedFrameFinalErrorTailMass_le
    hq theta R hR hPhysical hEta
  have hExpand :
      pauliPilotFiniteExpectation (q := q) z
          (mixedFrameExactBuresTransferIntegrand (q := q) theta R) =
        pauliPilotFiniteExpectation (q := q) z
            (fun path : PauliPilotPath q =>
              mixedFrameFinalErrorNorm (q := q) theta R path ^ 3) /
              gap ^ 2 +
          2 * pauliPilotFiniteExpectation (q := q) z
            (fun path : PauliPilotPath q =>
              mixedFrameFinalSquaredError (q := q) theta R path ^ 2) /
              gap ^ 3 +
          2 * mixedFrameFinalErrorTailMass (q := q) theta R eta +
          pauliPilotFiniteExpectation (q := q) z
            (fun path : PauliPilotPath q =>
              mixedFrameFinalSquaredError (q := q) theta R path ^ 2) /
              (4 * gap * eta ^ 2) := by
    unfold mixedFrameExactBuresTransferIntegrand
    dsimp [z, gap, eta]
    rw [pauliPilotFiniteExpectation_add_exact,
      pauliPilotFiniteExpectation_add_exact,
      pauliPilotFiniteExpectation_add_exact,
      pauliPilotFiniteExpectation_div_exact,
      pauliPilotFiniteExpectation_div_exact,
      pauliPilotFiniteExpectation_div_exact,
      pauliPilotFiniteExpectation_const_mul_exact,
      pauliPilotFiniteExpectation_two_tail]
  rw [hExpand]
  unfold mixedFrameExactBuresUnscaledMomentBound
  dsimp [gap, eta]
  have hTermThird := div_le_div_of_nonneg_right hThird (sq_nonneg gap)
  have hTermFourth := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hFourth (by norm_num : (0 : ℝ) ≤ 2))
    (by positivity : 0 ≤ gap ^ 3)
  have hTermTail := mul_le_mul_of_nonneg_left hTail (by norm_num : (0 : ℝ) ≤ 2)
  have hTermLast := div_le_div_of_nonneg_right hFourth
    (by positivity : 0 ≤ 4 * gap * eta ^ 2)
  nlinarith

/-- Final-stage scaled conditional exact risk.  The scale is the final-stage
sample count `3q`, not pilot plus final observations. -/
def mixedFrameConditionalScaledSafeguardedBuresRisk
    {q : ℕ} (theta : Fin 3 → ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  (3 * (q : ℝ)) *
    pauliPilotFiniteExpectation (q := q) (qubitFrameCoordinates R theta)
      (mixedFrameSafeguardedSquaredBuresLoss (q := q) theta R)

/-- Explicit frame-uniform scaled transfer rate. -/
def mixedFrameExactBuresTransferRate
    (theta : Fin 3 → ℝ) (q : ℕ) : ℝ :=
  let qR := (q : ℝ)
  let gap := 1 - blochNormSq theta
  let eta := mixedBuresFidelityLocalRadius theta
  (54 / gap ^ 2) * (Real.sqrt qR)⁻¹ +
    (90 / gap ^ 3) * qR⁻¹ +
    (90 / eta ^ 4) * qR⁻¹ +
    (45 / (4 * gap * eta ^ 2)) * qR⁻¹

theorem mixedFrameConditionalScaledSafeguardedBuresRisk_transfer
    {q : ℕ} (hq : 0 < q) (theta : Fin 3 → ℝ)
    (hInterior : blochNormSq theta < 1)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : MixedFrameOrthonormal R) :
    |mixedFrameConditionalScaledSafeguardedBuresRisk
        (q := q) theta R -
      mixedFrameConditionalScaledQuadraticRisk (q := q) theta R| ≤
        mixedFrameExactBuresTransferRate theta q := by
  let z := qubitFrameCoordinates R theta
  have hPhysical : PauliPilotPhysicalBloch theta := by
    unfold PauliPilotPhysicalBloch
    exact hInterior.le
  have hzPhysical := qubitFrameCoordinates_physical theta R hR hPhysical
  have hExpectation := pauliPilotFiniteExpectation_abs_sub_le (q := q)
    z hzPhysical
    (mixedFrameSafeguardedSquaredBuresLoss (q := q) theta R)
    (fun path : PauliPilotPath q => mixedInteriorBuresQuadraticLoss theta
      (mixedFrameFinalLinearError theta R path))
    (mixedFrameExactBuresTransferIntegrand (q := q) theta R)
    (mixedFrameSafeguardedBures_pointwise_transfer (q := q) hInterior R)
  have hMoment := mixedFrameExactBuresTransferIntegrand_expectation_le
    hq theta hInterior R hR
  have hScale : 0 ≤ 3 * (q : ℝ) := by positivity
  have hScaled := mul_le_mul_of_nonneg_left (hExpectation.trans hMoment) hScale
  have hQuadraticIdentity :
      (3 * (q : ℝ)) *
          pauliPilotFiniteExpectation (q := q) z
            (fun path : PauliPilotPath q =>
              mixedInteriorBuresQuadraticLoss theta
                (mixedFrameFinalLinearError (q := q) theta R path)) =
        mixedFrameConditionalScaledQuadraticRisk (q := q) theta R := by
    rfl
  rw [mixedFrameConditionalScaledSafeguardedBuresRisk,
    ← hQuadraticIdentity, ← mul_sub, abs_mul, abs_of_nonneg hScale]
  calc
    (3 * (q : ℝ)) *
        |pauliPilotFiniteExpectation (q := q) z
            (mixedFrameSafeguardedSquaredBuresLoss (q := q) theta R) -
          pauliPilotFiniteExpectation (q := q) z
            (fun path : PauliPilotPath q =>
              mixedInteriorBuresQuadraticLoss theta
                (mixedFrameFinalLinearError (q := q) theta R path))| ≤
      (3 * (q : ℝ)) *
        mixedFrameExactBuresUnscaledMomentBound theta q := hScaled
    _ = mixedFrameExactBuresTransferRate theta q := by
      have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
      have hSqrt : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.2 hqR
      have hGap : 0 < 1 - blochNormSq theta := by linarith
      have hEta := mixedBuresFidelityLocalRadius_pos hInterior
      unfold mixedFrameExactBuresUnscaledMomentBound
        mixedFrameExactBuresTransferRate
      dsimp only
      field_simp [hqR.ne', hSqrt.ne', hGap.ne', hEta.ne']
      ring

/-- The conditional exact-to-quadratic transfer is `o(1)` uniformly over all
orthonormal pilot-selected frames.  `n + 1` makes the zero-sample case
explicit. -/
theorem mixedFrameExactBuresTransferRate_tendsto_zero
    (theta : Fin 3 → ℝ) (hInterior : blochNormSq theta < 1) :
    Tendsto (fun n => mixedFrameExactBuresTransferRate theta (n + 1))
      atTop (nhds 0) := by
  let gap := 1 - blochNormSq theta
  let eta := mixedBuresFidelityLocalRadius theta
  let N : ℕ → ℝ := fun n => (n + 1 : ℕ)
  have hN : Tendsto N atTop atTop := by
    rw [tendsto_atTop]
    intro a
    filter_upwards
      [(tendsto_atTop.1 tendsto_natCast_atTop_atTop) (a - 1)] with n hn
    dsimp [N]
    push_cast
    linarith
  have hSqrt : Tendsto (fun n => Real.sqrt (N n)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hN
  have hInvSqrt : Tendsto (fun n => (Real.sqrt (N n))⁻¹)
      atTop (nhds 0) := hSqrt.inv_tendsto_atTop
  have hInvN : Tendsto (fun n => (N n)⁻¹) atTop (nhds 0) :=
    hN.inv_tendsto_atTop
  have hOne :
      Tendsto (fun n => (54 / gap ^ 2) * (Real.sqrt (N n))⁻¹)
        atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (54 / gap ^ 2 : ℝ))
        atTop (nhds (54 / gap ^ 2))).mul hInvSqrt
  have hTwo :
      Tendsto (fun n => (90 / gap ^ 3) * (N n)⁻¹)
        atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (90 / gap ^ 3 : ℝ))
        atTop (nhds (90 / gap ^ 3))).mul hInvN
  have hThree :
      Tendsto (fun n => (90 / eta ^ 4) * (N n)⁻¹)
        atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (90 / eta ^ 4 : ℝ))
        atTop (nhds (90 / eta ^ 4))).mul hInvN
  have hFour :
      Tendsto (fun n => (45 / (4 * gap * eta ^ 2)) * (N n)⁻¹)
        atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => (45 / (4 * gap * eta ^ 2) : ℝ))
        atTop (nhds (45 / (4 * gap * eta ^ 2)))).mul hInvN
  simpa [mixedFrameExactBuresTransferRate, gap, eta, N] using
    (((hOne.add hTwo).add hThree).add hFour)

/-! ## Safeguarded versus linear quadratic loss -/

/-- Quadratic loss evaluated at the physical safeguarded estimator. -/
def mixedFrameSafeguardedQuadraticLoss
    {q : ℕ} (theta : Fin 3 → ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (path : PauliPilotPath q) : ℝ :=
  mixedInteriorBuresQuadraticLoss theta
    (mixedFrameSafeguardedFinalEstimator R path - theta)

theorem mixedFrameSafeguardedQuadraticLoss_eq_linear_of_local
    {q : ℕ} {theta : Fin 3 → ℝ}
    {R : Matrix (Fin 3) (Fin 3) ℝ}
    {path : PauliPilotPath q}
    (hInterior : blochNormSq theta < 1)
    (hLocal : mixedFrameFinalErrorNorm theta R path ≤
      mixedBuresFidelityLocalRadius theta) :
    mixedFrameSafeguardedQuadraticLoss theta R path =
      mixedInteriorBuresQuadraticLoss theta
        (mixedFrameFinalLinearError theta R path) := by
  rw [mixedFrameSafeguardedQuadraticLoss,
    mixedFrameSafeguardedFinalEstimator_eq_linear_of_local hInterior hLocal]
  rfl

/-! ## Exact remaining finite-row averaging boundary -/

/-- Common-pilot-space average of the exact conditional final-stage risk. -/
def mixedPolynomialFinalStageExactBuresRiskIntegral
    (theta b : Fin 3 → ℝ) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ omega,
    ENNReal.ofReal
      (mixedFrameConditionalScaledSafeguardedBuresRisk
        (q := mixedPolynomialQuadraticQFinal n) theta
        (mixedPilotSelectedLocalFrame b
          (polynomialPilotEstimator n omega)))
    ∂pauliPilotConsistencyMeasure theta

/-- Exact citation-free boundary still needed to identify an explicit finite
two-stage joint-row risk with the pilot average above.  This statement contains
only a finite-law identification; it contains no limiting-risk conclusion. -/
def MixedPolynomialExactBuresFinitePilotAveragingLemma
    (theta b : Fin 3 → ℝ)
    (explicitFiniteJointRowRisk : ℕ → ℝ≥0∞) : Prop :=
  ∀ n,
    explicitFiniteJointRowRisk n =
      mixedPolynomialFinalStageExactBuresRiskIntegral theta b n

/-- Once the finite-row identification is supplied, it changes no value: the
explicit row and common-space conditional average agree term by term. -/
theorem mixedPolynomialExactBuresFinitePilotAveraging_apply
    {theta b : Fin 3 → ℝ}
    {explicitFiniteJointRowRisk : ℕ → ℝ≥0∞}
    (hAverage : MixedPolynomialExactBuresFinitePilotAveragingLemma
      theta b explicitFiniteJointRowRisk) (n : ℕ) :
    explicitFiniteJointRowRisk n =
      mixedPolynomialFinalStageExactBuresRiskIntegral theta b n := by
  exact hAverage n

/-!
The proved endpoint in this source is therefore the frame-uniform conditional
transfer

`|3q E[d_B^2] - mixedFrameConditionalScaledQuadraticRisk| ≤ rate(theta,q)`

with `rate(theta,n+1) -> 0`.  Combining it with the already proved quadratic
`9/4` endpoint requires only the finite averaging identification above and the
standard finite-probability averaging of a frame-independent error bound.  It
is intentionally not presented here as already closed.
-/

end
end Paper
end QubitOracle
