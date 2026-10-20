import QubitOracle.Paper.OneQubitMixedPolynomialExactBuresRiskEndpoint
import QubitOracle.Paper.OneQubitMixedFinalEstimatorFourthMoment
import QubitOracle.Paper.OneQubitMixedBuresFidelityLocalRemainder

/-!
# Polynomial mixed-qubit ordinary-infidelity endpoint

For root fidelity `s` and squared Bures loss `B = 2 * (1 - s)`, the exact
identity is

`1 - F = B - B^2 / 4`.

The only additional asymptotic term beyond the exact-Bures endpoint is thus
the expected square of `B`.  On the local event this file proves

`B <= (13 / (32 * gap)) * ‖error‖^2`,

where `gap = 1 - ‖theta‖^2`.  On the complementary event it uses `B <= 2`.
The established fourth-moment and tail bounds then give a uniform `O(1/q)`
bound after multiplying by the final-stage sample count `3q`.
-/

open scoped BigOperators ENNReal
open Filter Topology MeasureTheory

namespace QubitOracle
namespace Paper

noncomputable section

/-! ## Physical fidelity range -/

private theorem mixedBlochNormSq_nonnegative_endpoint
    (x : Fin 3 → ℝ) : 0 ≤ blochNormSq x := by
  unfold blochNormSq
  exact Finset.sum_nonneg fun j _ => sq_nonneg _

/-- The exact two-state qubit squared fidelity lies in `[0,1]` on the closed
Bloch ball. -/
theorem mixedQubitBlochFidelitySqBetween_mem_Icc
    {theta sigma : Fin 3 → ℝ}
    (hTheta : blochNormSq theta ≤ 1)
    (hSigma : blochNormSq sigma ≤ 1) :
    mixedQubitBlochFidelitySqBetween theta sigma ∈ Set.Icc 0 1 := by
  let a := blochNormSq theta
  let b := blochNormSq sigma
  let d := blochDot theta sigma
  let x := Real.sqrt (a * b)
  let y := Real.sqrt ((1 - a) * (1 - b))
  let p := a * (1 - b)
  let q := b * (1 - a)
  have ha0 : 0 ≤ a := mixedBlochNormSq_nonnegative_endpoint theta
  have hb0 : 0 ≤ b := mixedBlochNormSq_nonnegative_endpoint sigma
  have ha1 : a ≤ 1 := hTheta
  have hb1 : b ≤ 1 := hSigma
  have hga : 0 ≤ 1 - a := by linarith
  have hgb : 0 ≤ 1 - b := by linarith
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hp : 0 ≤ p := mul_nonneg ha0 hgb
  have hq : 0 ≤ q := mul_nonneg hb0 hga
  have hxSq : x ^ 2 = a * b := by
    exact Real.sq_sqrt (mul_nonneg ha0 hb0)
  have hySq : y ^ 2 = (1 - a) * (1 - b) := by
    exact Real.sq_sqrt (mul_nonneg hga hgb)
  have hCauchy := bloch_cauchy_schwarz theta sigma
  have hAbsDotSq : |d| ^ 2 = d ^ 2 := by
    rw [sq_abs]
  have hAbsDot : |d| ≤ x := by
    dsimp [x, a, b] at hx hxSq ⊢
    nlinarith [hAbsDotSq]
  have hDotUpper : d ≤ x := (le_abs_self d).trans hAbsDot
  have hDotLower : -x ≤ d := by
    have := neg_abs_le d
    linarith
  have hxySq : (x * y) ^ 2 = p * q := by
    dsimp [p, q]
    rw [mul_pow, hxSq, hySq]
    ring
  have hPQ : 2 * (x * y) ≤ p + q := by
    have hDisc : 0 ≤ (p - q) ^ 2 := sq_nonneg _
    have hLeft : 0 ≤ 2 * (x * y) := by positivity
    have hRight : 0 ≤ p + q := add_nonneg hp hq
    nlinarith
  have hXY : x + y ≤ 1 := by
    have hSquare : (x + y) ^ 2 ≤ 1 := by
      dsimp [p, q] at hPQ
      nlinarith
    have hNonnegative : 0 ≤ x + y := add_nonneg hx hy
    nlinarith
  have hxLeOne : x ≤ 1 := by linarith
  constructor
  · unfold mixedQubitBlochFidelitySqBetween
    dsimp [a, b, d, y] at hDotLower hy ⊢
    nlinarith
  · unfold mixedQubitBlochFidelitySqBetween
    dsimp [a, b, d, y] at hDotUpper hXY ⊢
    nlinarith

/-- Root fidelity lies in `[0,1]` for physical Bloch vectors. -/
theorem mixedQubitBlochRootFidelityBetween_mem_Icc
    {theta sigma : Fin 3 → ℝ}
    (hTheta : blochNormSq theta ≤ 1)
    (hSigma : blochNormSq sigma ≤ 1) :
    mixedQubitBlochRootFidelityBetween theta sigma ∈ Set.Icc 0 1 := by
  have hF := mixedQubitBlochFidelitySqBetween_mem_Icc hTheta hSigma
  constructor
  · exact Real.sqrt_nonneg _
  · unfold mixedQubitBlochRootFidelityBetween
    have hSq := Real.sq_sqrt hF.1
    have hSqrt := Real.sqrt_nonneg
      (mixedQubitBlochFidelitySqBetween theta sigma)
    nlinarith [hF.2]

/-! ## Exact ordinary-infidelity identity -/

/-- Ordinary infidelity of the safeguarded estimator. -/
def mixedFrameSafeguardedOrdinaryInfidelityLoss
    {q : ℕ} (theta : Fin 3 → ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (path : PauliPilotPath q) : ℝ :=
  max 0 (mixedQubitBlochInfidelityBetween theta
    (mixedFrameSafeguardedFinalEstimator (q := q) R path))

theorem mixedFrameSafeguardedOrdinaryInfidelityLoss_nonnegative
    {q : ℕ} (theta : Fin 3 → ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (path : PauliPilotPath q) :
    0 ≤ mixedFrameSafeguardedOrdinaryInfidelityLoss theta R path := by
  exact le_max_left _ _

/-- Exact identity `1-F = B-B^2/4` for the physical safeguarded estimator. -/
theorem mixedFrameSafeguardedOrdinaryInfidelity_eq_bures_sub_quarter_sq
    {q : ℕ} (theta : Fin 3 → ℝ)
    (hPhysical : PauliPilotPhysicalBloch theta)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (path : PauliPilotPath q) :
    mixedFrameSafeguardedOrdinaryInfidelityLoss theta R path =
      mixedFrameSafeguardedSquaredBuresLoss theta R path -
        mixedFrameSafeguardedSquaredBuresLoss theta R path ^ 2 / 4 := by
  let sigma := mixedFrameSafeguardedFinalEstimator R path
  let F := mixedQubitBlochFidelitySqBetween theta sigma
  let s := mixedQubitBlochRootFidelityBetween theta sigma
  have hTheta : blochNormSq theta ≤ 1 := by
    exact hPhysical
  have hSigma : blochNormSq sigma ≤ 1 := by
    exact mixedFrameSafeguardedFinalEstimator_physical R path
  have hF := mixedQubitBlochFidelitySqBetween_mem_Icc hTheta hSigma
  have hs := mixedQubitBlochRootFidelityBetween_mem_Icc hTheta hSigma
  have hsSq : s ^ 2 = F := by
    exact Real.sq_sqrt hF.1
  have hRootInfidelity : 0 ≤ 1 - s := by linarith [hs.2]
  have hInfidelity : 0 ≤ 1 - F := by linarith [hF.2]
  have hBures : 0 ≤ 2 * (1 - s) :=
    mul_nonneg (by norm_num) hRootInfidelity
  unfold mixedFrameSafeguardedOrdinaryInfidelityLoss
    mixedFrameSafeguardedSquaredBuresLoss
    mixedQubitBlochInfidelityBetween mixedQubitBlochBuresSqBetween
    mixedQubitBlochRootInfidelityBetween
  dsimp [F, s, sigma] at hF hs hsSq hInfidelity hBures ⊢
  rw [max_eq_right hInfidelity, max_eq_right hBures]
  nlinarith

/-! ## Local quadratic envelope for squared Bures -/

/-- Local coefficient in `B <= coefficient * ‖error‖^2`. -/
def mixedBuresLocalQuadraticEnvelopeCoefficient
    (theta : Fin 3 → ℝ) : ℝ :=
  13 / (32 * (1 - blochNormSq theta))

theorem mixedBuresLocalQuadraticEnvelopeCoefficient_nonnegative
    {theta : Fin 3 → ℝ} (hInterior : blochNormSq theta < 1) :
    0 ≤ mixedBuresLocalQuadraticEnvelopeCoefficient theta := by
  unfold mixedBuresLocalQuadraticEnvelopeCoefficient
  positivity

/-- On the local event, exact safeguarded squared Bures is bounded by a fixed
multiple of squared Euclidean estimation error. -/
theorem mixedFrameSafeguardedSquaredBuresLoss_le_localQuadraticEnvelope
    {q : ℕ} (theta : Fin 3 → ℝ)
    (hInterior : blochNormSq theta < 1)
    (hPhysical : PauliPilotPhysicalBloch theta)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (path : PauliPilotPath q)
    (hLocal : mixedFrameFinalErrorNorm theta R path ≤
      mixedBuresFidelityLocalRadius theta) :
    mixedFrameSafeguardedSquaredBuresLoss theta R path ≤
      mixedBuresLocalQuadraticEnvelopeCoefficient theta *
        mixedFrameFinalSquaredError theta R path := by
  let gap := 1 - blochNormSq theta
  let d := mixedFrameFinalErrorNorm theta R path
  let e2 := mixedFrameFinalSquaredError theta R path
  let error := mixedFrameFinalLinearError theta R path
  let quadratic := mixedInteriorBuresQuadraticLoss theta error
  have hGap : 0 < gap := by
    dsimp [gap]
    linarith
  have hGapLeOne : gap ≤ 1 := by
    have hTheta0 := mixedBlochNormSq_nonnegative_endpoint theta
    dsimp [gap]
    linarith
  have hd : 0 ≤ d := mixedBlochEuclideanNorm_nonnegative error
  have he2 : 0 ≤ e2 := mixedFrameFinalSquaredError_nonnegative theta R path
  have hNormSq := mixedFrameFinalErrorNorm_sq theta R path
  have hDLe : d ≤ gap / 8 := by
    simpa [d, gap, mixedBuresFidelityLocalRadius] using hLocal
  have hD2 : d ^ 2 ≤ gap ^ 2 / 64 := by
    have hMul := mul_le_mul hDLe hDLe hd (by positivity : 0 ≤ gap / 8)
    nlinarith
  have hD3Mul : d ^ 3 ≤ d ^ 2 * gap / 8 := by
    have hMul := mul_le_mul_of_nonneg_left hDLe (sq_nonneg d)
    nlinarith
  have hCubic : d ^ 3 / gap ^ 2 ≤ e2 / (8 * gap) := by
    dsimp [d, e2] at hNormSq hD3Mul ⊢
    field_simp [hGap.ne']
    nlinarith
  have hQuartic : 2 * d ^ 4 / gap ^ 3 ≤ e2 / (32 * gap) := by
    dsimp [d, e2] at hNormSq hD2 ⊢
    field_simp [hGap.ne']
    nlinarith
  have hQuadratic := mixedInteriorBuresQuadraticLoss_le_normSq_div_gap
    (theta := theta) (error := error) hInterior
  have hRemainder := mixedQubitBlochBuresSqBetween_add_local_remainder
    (theta := theta) (delta := error) hInterior hLocal
  have hSafeguard :=
    mixedFrameSafeguardedFinalEstimator_eq_linear_of_local
      (theta := theta) (R := R) (path := path) hInterior hLocal
  have hAdd := mixedFrameFinalLinearError_add_truth theta R path
  have hTheta : blochNormSq theta ≤ 1 := hPhysical
  have hSigma : blochNormSq
      (mixedFrameSafeguardedFinalEstimator R path) ≤ 1 :=
    mixedFrameSafeguardedFinalEstimator_physical R path
  have hs := mixedQubitBlochRootFidelityBetween_mem_Icc hTheta hSigma
  have hRawNonnegative :
      0 ≤ mixedQubitBlochBuresSqBetween theta
        (mixedFrameSafeguardedFinalEstimator R path) := by
    unfold mixedQubitBlochBuresSqBetween
      mixedQubitBlochRootInfidelityBetween
    linarith [hs.2]
  have hRawRewrite :
      mixedQubitBlochBuresSqBetween theta
          (mixedFrameSafeguardedFinalEstimator R path) =
        mixedQubitBlochBuresSqBetween theta (theta + error) := by
    rw [hSafeguard, hAdd]
  have hExactUpper :
      mixedFrameSafeguardedSquaredBuresLoss theta R path ≤
        quadratic + mixedBuresFidelityLocalRemainderEnvelope theta error := by
    unfold mixedFrameSafeguardedSquaredBuresLoss
    rw [max_eq_right hRawNonnegative, hRawRewrite]
    have hUpper := le_abs_self
      (mixedQubitBlochBuresSqBetween theta (theta + error) - quadratic)
    nlinarith
  have hFourth : d ^ 4 = e2 ^ 2 := by
    dsimp [d, e2] at hNormSq ⊢
    nlinarith
  have hEnvelope :
      mixedBuresFidelityLocalRemainderEnvelope theta error =
        d ^ 3 / gap ^ 2 + 2 * d ^ 4 / gap ^ 3 := by
    rfl
  have hQuadratic' : quadratic ≤ e2 / (4 * gap) := by
    simpa [quadratic, error, e2, gap, mixedFrameFinalSquaredError] using hQuadratic
  rw [hEnvelope] at hExactUpper
  calc
    mixedFrameSafeguardedSquaredBuresLoss theta R path ≤
        quadratic +
          (d ^ 3 / gap ^ 2 + 2 * d ^ 4 / gap ^ 3) := hExactUpper
    _ ≤ e2 / (4 * gap) + (e2 / (8 * gap) + e2 / (32 * gap)) :=
      add_le_add hQuadratic' (add_le_add hCubic hQuartic)
    _ = mixedBuresLocalQuadraticEnvelopeCoefficient theta * e2 := by
      unfold mixedBuresLocalQuadraticEnvelopeCoefficient
      dsimp [gap]
      field_simp [hGap.ne']
      ring

/-! ## Conditional second moment -/

/-- Final-stage-scaled conditional second moment of exact squared Bures. -/
def mixedFrameConditionalScaledBuresSecondMoment
    {q : ℕ} (theta : Fin 3 → ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  (3 * (q : ℝ)) *
    pauliPilotFiniteExpectation (q := q) (qubitFrameCoordinates R theta)
      (fun path : PauliPilotPath q =>
        mixedFrameSafeguardedSquaredBuresLoss (q := q) theta R path ^ 2)

/-- Pointwise local/bad-event envelope requiring only the fourth error moment. -/
def mixedFrameSquaredBuresSecondMomentIntegrand
    {q : ℕ} (theta : Fin 3 → ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (path : PauliPilotPath q) : ℝ :=
  mixedBuresLocalQuadraticEnvelopeCoefficient theta ^ 2 *
      mixedFrameFinalSquaredError theta R path ^ 2 +
    if mixedBuresFidelityLocalRadius theta <
        mixedFrameFinalErrorNorm theta R path then 4 else 0

theorem mixedFrameSafeguardedSquaredBuresLoss_sq_le_momentIntegrand
    {q : ℕ} (theta : Fin 3 → ℝ)
    (hInterior : blochNormSq theta < 1)
    (hPhysical : PauliPilotPhysicalBloch theta)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (path : PauliPilotPath q) :
    mixedFrameSafeguardedSquaredBuresLoss theta R path ^ 2 ≤
      mixedFrameSquaredBuresSecondMomentIntegrand theta R path := by
  have hCoefficient :=
    mixedBuresLocalQuadraticEnvelopeCoefficient_nonnegative hInterior
  have he2 := mixedFrameFinalSquaredError_nonnegative theta R path
  by_cases hBad : mixedBuresFidelityLocalRadius theta <
      mixedFrameFinalErrorNorm theta R path
  · have hB := mixedFrameSafeguardedSquaredBuresLoss_le_two theta R path
    have hB0 := mixedFrameSafeguardedSquaredBuresLoss_nonnegative theta R path
    unfold mixedFrameSquaredBuresSecondMomentIntegrand
    rw [if_pos hBad]
    nlinarith [sq_nonneg
      (mixedBuresLocalQuadraticEnvelopeCoefficient theta *
        mixedFrameFinalSquaredError theta R path)]
  · have hLocal : mixedFrameFinalErrorNorm theta R path ≤
        mixedBuresFidelityLocalRadius theta := le_of_not_gt hBad
    have hB := mixedFrameSafeguardedSquaredBuresLoss_le_localQuadraticEnvelope
      theta hInterior hPhysical R path hLocal
    have hB0 := mixedFrameSafeguardedSquaredBuresLoss_nonnegative theta R path
    have hRight0 : 0 ≤ mixedBuresLocalQuadraticEnvelopeCoefficient theta *
        mixedFrameFinalSquaredError theta R path :=
      mul_nonneg hCoefficient he2
    unfold mixedFrameSquaredBuresSecondMomentIntegrand
    rw [if_neg hBad]
    nlinarith

private theorem pauliPilotFiniteExpectation_mono_ordinary
    {q : ℕ} (z : Fin 3 → ℝ)
    (hPhysical : PauliPilotPhysicalBloch z)
    {f g : PauliPilotPath q → ℝ}
    (hfg : ∀ path, f path ≤ g path) :
    pauliPilotFiniteExpectation z f ≤ pauliPilotFiniteExpectation z g := by
  unfold pauliPilotFiniteExpectation
  exact Finset.sum_le_sum fun path _ =>
    mul_le_mul_of_nonneg_left (hfg path)
      (pauliPilotPathMass_nonnegative z hPhysical path)

private theorem pauliPilotFiniteExpectation_four_tail
    {q : ℕ} (theta : Fin 3 → ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ) (eta : ℝ) :
    pauliPilotFiniteExpectation (q := q) (qubitFrameCoordinates R theta)
        (fun path : PauliPilotPath q =>
          if eta < mixedFrameFinalErrorNorm (q := q) theta R path
          then 4 else 0) =
      4 * mixedFrameFinalErrorTailMass (q := q) theta R eta := by
  unfold pauliPilotFiniteExpectation mixedFrameFinalErrorTailMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro path hpath
  by_cases hBad : eta < mixedFrameFinalErrorNorm theta R path
  · simp [hBad, mul_comm]
  · simp [hBad]

/-- Explicit conditional second-moment rate. -/
def mixedFrameScaledBuresSecondMomentRate
    (theta : Fin 3 → ℝ) (q : ℕ) : ℝ :=
  let coefficient := mixedBuresLocalQuadraticEnvelopeCoefficient theta
  let eta := mixedBuresFidelityLocalRadius theta
  (45 * coefficient ^ 2 + 180 / eta ^ 4) / (q : ℝ)

/-- Uniform conditional estimate
`3q E[B^2] <= (45 coefficient^2 + 180/eta^4)/q`. -/
theorem mixedFrameConditionalScaledBuresSecondMoment_le
    {q : ℕ} (hq : 0 < q) (theta : Fin 3 → ℝ)
    (hInterior : blochNormSq theta < 1)
    (hPhysical : PauliPilotPhysicalBloch theta)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : MixedFrameOrthonormal R) :
    mixedFrameConditionalScaledBuresSecondMoment (q := q) theta R ≤
      mixedFrameScaledBuresSecondMomentRate theta q := by
  let z := qubitFrameCoordinates R theta
  let coefficient := mixedBuresLocalQuadraticEnvelopeCoefficient theta
  let eta := mixedBuresFidelityLocalRadius theta
  have hzPhysical := qubitFrameCoordinates_physical theta R hR hPhysical
  have hEta : 0 < eta := mixedBuresFidelityLocalRadius_pos hInterior
  have hPointwise :
      pauliPilotFiniteExpectation (q := q) z
          (fun path : PauliPilotPath q =>
            mixedFrameSafeguardedSquaredBuresLoss (q := q) theta R path ^ 2) ≤
        pauliPilotFiniteExpectation (q := q) z
          (mixedFrameSquaredBuresSecondMomentIntegrand (q := q) theta R) :=
    pauliPilotFiniteExpectation_mono_ordinary (q := q) z hzPhysical
      (fun path =>
        mixedFrameSafeguardedSquaredBuresLoss_sq_le_momentIntegrand
          (q := q) theta hInterior hPhysical R path)
  have hFourth := mixedFrameFinalSquaredError_fourthMoment_le
    hq theta R hR hPhysical
  have hTail := mixedFrameFinalErrorTailMass_le
    hq theta R hR hPhysical hEta
  have hExpand :
      pauliPilotFiniteExpectation (q := q) z
          (mixedFrameSquaredBuresSecondMomentIntegrand (q := q) theta R) =
        coefficient ^ 2 *
          pauliPilotFiniteExpectation (q := q) z
            (fun path : PauliPilotPath q =>
              mixedFrameFinalSquaredError (q := q) theta R path ^ 2) +
          4 * mixedFrameFinalErrorTailMass (q := q) theta R eta := by
    unfold mixedFrameSquaredBuresSecondMomentIntegrand
      pauliPilotFiniteExpectation
    dsimp [z, coefficient, eta]
    rw [show
        (∑ path : PauliPilotPath q,
          pauliPilotPathMass (qubitFrameCoordinates R theta) path *
            (mixedBuresLocalQuadraticEnvelopeCoefficient theta ^ 2 *
                mixedFrameFinalSquaredError theta R path ^ 2 +
              if mixedBuresFidelityLocalRadius theta <
                  mixedFrameFinalErrorNorm theta R path then 4 else 0)) =
          (∑ path : PauliPilotPath q,
            pauliPilotPathMass (qubitFrameCoordinates R theta) path *
              (mixedBuresLocalQuadraticEnvelopeCoefficient theta ^ 2 *
                mixedFrameFinalSquaredError theta R path ^ 2)) +
          ∑ path : PauliPilotPath q,
            pauliPilotPathMass (qubitFrameCoordinates R theta) path *
              (if mixedBuresFidelityLocalRadius theta <
                  mixedFrameFinalErrorNorm theta R path then 4 else 0) by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro path hpath
        ring]
    congr 1
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro path hpath
      ring
    · simpa [pauliPilotFiniteExpectation] using
        (pauliPilotFiniteExpectation_four_tail
          (q := q) theta R (mixedBuresFidelityLocalRadius theta))
  have hCoefficient : 0 ≤ coefficient :=
    mixedBuresLocalQuadraticEnvelopeCoefficient_nonnegative hInterior
  have hExpectation :
      pauliPilotFiniteExpectation (q := q) z
          (mixedFrameSquaredBuresSecondMomentIntegrand (q := q) theta R) ≤
        coefficient ^ 2 * (15 / (q : ℝ) ^ 2) +
          4 * (15 / ((q : ℝ) ^ 2 * eta ^ 4)) := by
    rw [hExpand]
    exact add_le_add
      (mul_le_mul_of_nonneg_left hFourth (sq_nonneg coefficient))
      (mul_le_mul_of_nonneg_left hTail (by norm_num))
  have hScale : 0 ≤ 3 * (q : ℝ) := by positivity
  unfold mixedFrameConditionalScaledBuresSecondMoment
    mixedFrameScaledBuresSecondMomentRate
  dsimp [coefficient, eta]
  calc
    (3 * (q : ℝ)) *
        pauliPilotFiniteExpectation (q := q) z
          (fun path : PauliPilotPath q =>
            mixedFrameSafeguardedSquaredBuresLoss (q := q) theta R path ^ 2) ≤
      (3 * (q : ℝ)) *
        pauliPilotFiniteExpectation (q := q) z
          (mixedFrameSquaredBuresSecondMomentIntegrand (q := q) theta R) :=
        mul_le_mul_of_nonneg_left hPointwise hScale
    _ ≤ (3 * (q : ℝ)) *
        (coefficient ^ 2 * (15 / (q : ℝ) ^ 2) +
          4 * (15 / ((q : ℝ) ^ 2 * eta ^ 4))) :=
        mul_le_mul_of_nonneg_left hExpectation hScale
    _ = (45 * coefficient ^ 2 + 180 / eta ^ 4) / (q : ℝ) := by
      have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
      field_simp [hqR.ne', hEta.ne']
      ring

/-! ## Conditional ordinary-infidelity identity -/

/-- Conditional final-stage-scaled ordinary infidelity. -/
def mixedFrameConditionalScaledOrdinaryInfidelityRisk
    {q : ℕ} (theta : Fin 3 → ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  (3 * (q : ℝ)) *
    pauliPilotFiniteExpectation (q := q) (qubitFrameCoordinates R theta)
      (mixedFrameSafeguardedOrdinaryInfidelityLoss (q := q) theta R)

theorem mixedFrameConditionalOrdinaryInfidelity_eq_bures_sub_secondMoment
    {q : ℕ} (theta : Fin 3 → ℝ)
    (hPhysical : PauliPilotPhysicalBloch theta)
    (R : Matrix (Fin 3) (Fin 3) ℝ) :
    mixedFrameConditionalScaledOrdinaryInfidelityRisk (q := q) theta R =
      mixedFrameConditionalScaledSafeguardedBuresRisk (q := q) theta R -
        mixedFrameConditionalScaledBuresSecondMoment (q := q) theta R / 4 := by
  unfold mixedFrameConditionalScaledOrdinaryInfidelityRisk
    mixedFrameConditionalScaledSafeguardedBuresRisk
    mixedFrameConditionalScaledBuresSecondMoment
    pauliPilotFiniteExpectation
  have hPointwise : ∀ path : PauliPilotPath q,
      mixedFrameSafeguardedOrdinaryInfidelityLoss theta R path =
        mixedFrameSafeguardedSquaredBuresLoss theta R path -
          mixedFrameSafeguardedSquaredBuresLoss theta R path ^ 2 / 4 :=
    fun path =>
      mixedFrameSafeguardedOrdinaryInfidelity_eq_bures_sub_quarter_sq
        theta hPhysical R path
  have hSum :
      (∑ path : PauliPilotPath q,
        pauliPilotPathMass (qubitFrameCoordinates R theta) path *
          mixedFrameSafeguardedOrdinaryInfidelityLoss theta R path) =
        (∑ path : PauliPilotPath q,
          pauliPilotPathMass (qubitFrameCoordinates R theta) path *
            mixedFrameSafeguardedSquaredBuresLoss theta R path) -
        (∑ path : PauliPilotPath q,
          pauliPilotPathMass (qubitFrameCoordinates R theta) path *
            mixedFrameSafeguardedSquaredBuresLoss theta R path ^ 2) / 4 := by
    calc
      (∑ path : PauliPilotPath q,
        pauliPilotPathMass (qubitFrameCoordinates R theta) path *
          mixedFrameSafeguardedOrdinaryInfidelityLoss theta R path) =
        ∑ path : PauliPilotPath q,
          (pauliPilotPathMass (qubitFrameCoordinates R theta) path *
              mixedFrameSafeguardedSquaredBuresLoss theta R path -
            pauliPilotPathMass (qubitFrameCoordinates R theta) path *
              mixedFrameSafeguardedSquaredBuresLoss theta R path ^ 2 / 4) := by
        apply Finset.sum_congr rfl
        intro path hpath
        rw [hPointwise path]
        ring
      _ = (∑ path : PauliPilotPath q,
          pauliPilotPathMass (qubitFrameCoordinates R theta) path *
            mixedFrameSafeguardedSquaredBuresLoss theta R path) -
          ∑ path : PauliPilotPath q,
            pauliPilotPathMass (qubitFrameCoordinates R theta) path *
              mixedFrameSafeguardedSquaredBuresLoss theta R path ^ 2 / 4 := by
        rw [Finset.sum_sub_distrib]
      _ = (∑ path : PauliPilotPath q,
          pauliPilotPathMass (qubitFrameCoordinates R theta) path *
            mixedFrameSafeguardedSquaredBuresLoss theta R path) -
        (∑ path : PauliPilotPath q,
          pauliPilotPathMass (qubitFrameCoordinates R theta) path *
            mixedFrameSafeguardedSquaredBuresLoss theta R path ^ 2) / 4 := by
        rw [Finset.sum_div]
  rw [hSum]
  ring

theorem mixedFrameConditionalOrdinaryInfidelity_abs_sub_bures_le
    {q : ℕ} (hq : 0 < q) (theta : Fin 3 → ℝ)
    (hInterior : blochNormSq theta < 1)
    (hPhysical : PauliPilotPhysicalBloch theta)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : MixedFrameOrthonormal R) :
    |mixedFrameConditionalScaledOrdinaryInfidelityRisk (q := q) theta R -
        mixedFrameConditionalScaledSafeguardedBuresRisk (q := q) theta R| ≤
      mixedFrameScaledBuresSecondMomentRate theta q / 4 := by
  rw [mixedFrameConditionalOrdinaryInfidelity_eq_bures_sub_secondMoment
    theta hPhysical R]
  have hSecond0 : 0 ≤
      mixedFrameConditionalScaledBuresSecondMoment (q := q) theta R := by
    unfold mixedFrameConditionalScaledBuresSecondMoment
      pauliPilotFiniteExpectation
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun path _ =>
        mul_nonneg
          (pauliPilotPathMass_nonnegative
            (qubitFrameCoordinates R theta)
            (qubitFrameCoordinates_physical theta R hR hPhysical) path)
          (sq_nonneg _))
  have hUpper := mixedFrameConditionalScaledBuresSecondMoment_le
    hq theta hInterior hPhysical R hR
  rw [show
      mixedFrameConditionalScaledSafeguardedBuresRisk (q := q) theta R -
          mixedFrameConditionalScaledBuresSecondMoment (q := q) theta R / 4 -
        mixedFrameConditionalScaledSafeguardedBuresRisk (q := q) theta R =
          -mixedFrameConditionalScaledBuresSecondMoment (q := q) theta R / 4 by
      ring]
  rw [abs_of_nonpos (by nlinarith :
    -mixedFrameConditionalScaledBuresSecondMoment (q := q) theta R / 4 ≤ 0)]
  nlinarith

/-! ## Polynomial pilot averaging -/

/-- The explicit polynomial ordinary-infidelity row is its finite pilot
average of conditional ordinary-infidelity risks. -/
theorem mixedPolynomialFinalStageExpectedScaledOrdinaryInfidelityRiskReal_eq_pilotAverage
    (theta b : RLSVector 3)
    (hPhysical : PauliPilotPhysicalBloch theta) (n : ℕ) :
    mixedPolynomialFinalStageExpectedScaledOrdinaryInfidelityRiskReal theta b n =
      pauliPilotFiniteExpectation theta
        (fun pilot : PauliPilotPath (Nat.succ (polynomialPilotIndex n)) =>
          mixedFrameConditionalScaledOrdinaryInfidelityRisk
            (q := mixedPolynomialQuadraticQFinal n) theta
            (mixedPilotSelectedLocalFrame b (pauliPilotEstimate pilot))) := by
  classical
  let qPilot := Nat.succ (polynomialPilotIndex n)
  let r := mixedPolynomialQuadraticQFinal n
  let selected := mixedPilotLocalSelectedFinalFrame qPilot b
  have hFiber : ∀ pilot : PauliPilotPath qPilot,
      (∑ finalPath : MixedTwoStageFinalPath (3 * r),
        mixedTwoStageFiniteRowMass theta selected (pilot, finalPath) *
          mixedTwoStageFiniteRowScaledOrdinaryInfidelityLoss
            theta selected (pilot, finalPath)) =
        pauliPilotPathMass theta pilot *
          mixedFrameConditionalScaledOrdinaryInfidelityRisk
            (q := r) theta (selected.frame pilot) := by
    intro pilot
    have hFinal :
        (∑ finalPath : MixedTwoStageFinalPath (3 * r),
          mixedTwoStageConditionalFinalPathMass theta selected pilot finalPath *
            mixedFrameSafeguardedOrdinaryInfidelityLoss (q := r) theta
              (selected.frame pilot)
              (mixedTwoStageFinalPathPauliEquiv r finalPath)) =
          pauliPilotFiniteExpectation (q := r)
            (qubitFrameCoordinates (selected.frame pilot) theta)
            (mixedFrameSafeguardedOrdinaryInfidelityLoss (q := r) theta
              (selected.frame pilot)) := by
      unfold pauliPilotFiniteExpectation
      exact Fintype.sum_equiv (mixedTwoStageFinalPathPauliEquiv r)
        (fun finalPath : MixedTwoStageFinalPath (3 * r) =>
          mixedTwoStageConditionalFinalPathMass theta selected pilot finalPath *
            mixedFrameSafeguardedOrdinaryInfidelityLoss (q := r) theta
              (selected.frame pilot)
              (mixedTwoStageFinalPathPauliEquiv r finalPath))
        (fun path : PauliPilotPath r =>
          pauliPilotPathMass
              (qubitFrameCoordinates (selected.frame pilot) theta) path *
            mixedFrameSafeguardedOrdinaryInfidelityLoss (q := r) theta
              (selected.frame pilot) path)
        (fun finalPath => by
          rw [mixedTwoStageConditionalFinalPathMass_eq_pauliPilotPathMass])
    unfold mixedTwoStageFiniteRowMass
      mixedTwoStageFiniteRowScaledOrdinaryInfidelityLoss
      mixedFrameConditionalScaledOrdinaryInfidelityRisk
      mixedFrameSafeguardedOrdinaryInfidelityLoss
    calc
      (∑ finalPath : MixedTwoStageFinalPath (3 * r),
        (pauliPilotPathMass theta pilot *
            mixedTwoStageConditionalFinalPathMass
              theta selected pilot finalPath) *
          ((3 * (r : ℝ)) * max 0
            (mixedQubitBlochInfidelityBetween theta
              (mixedFrameSafeguardedFinalEstimator
                (selected.frame pilot)
                (mixedTwoStageFinalPathPauliEquiv r finalPath))))) =
        pauliPilotPathMass theta pilot * (3 * (r : ℝ)) *
          (∑ finalPath : MixedTwoStageFinalPath (3 * r),
            mixedTwoStageConditionalFinalPathMass
                theta selected pilot finalPath *
              mixedFrameSafeguardedOrdinaryInfidelityLoss (q := r) theta
                (selected.frame pilot)
                (mixedTwoStageFinalPathPauliEquiv r finalPath)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro finalPath hfinal
          unfold mixedFrameSafeguardedOrdinaryInfidelityLoss
          ring
      _ = pauliPilotPathMass theta pilot * (3 * (r : ℝ)) *
          pauliPilotFiniteExpectation (q := r)
            (qubitFrameCoordinates (selected.frame pilot) theta)
            (mixedFrameSafeguardedOrdinaryInfidelityLoss (q := r) theta
              (selected.frame pilot)) := by rw [hFinal]
      _ = pauliPilotPathMass theta pilot *
          ((3 * (r : ℝ)) *
            pauliPilotFiniteExpectation (q := r)
              (qubitFrameCoordinates (selected.frame pilot) theta)
              (mixedFrameSafeguardedOrdinaryInfidelityLoss (q := r) theta
                (selected.frame pilot))) := by ring
  unfold mixedPolynomialFinalStageExpectedScaledOrdinaryInfidelityRiskReal
    pauliPilotFiniteExpectation
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro pilot hpilot
  simpa [qPilot, r, selected, mixedPilotLocalSelectedFinalFrame] using
    hFiber pilot

private theorem pauliPilotFiniteExpectation_abs_sub_le_constant_ordinary
    {q : ℕ} (theta : RLSVector 3)
    (hPhysical : PauliPilotPhysicalBloch theta)
    (f g : PauliPilotPath q → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hPointwise : ∀ pilot, |f pilot - g pilot| ≤ c) :
    |pauliPilotFiniteExpectation theta f -
        pauliPilotFiniteExpectation theta g| ≤ c := by
  unfold pauliPilotFiniteExpectation
  rw [← Finset.sum_sub_distrib]
  have hRewrite :
      (∑ pilot : PauliPilotPath q,
        (pauliPilotPathMass theta pilot * f pilot -
          pauliPilotPathMass theta pilot * g pilot)) =
        ∑ pilot : PauliPilotPath q,
          pauliPilotPathMass theta pilot * (f pilot - g pilot) := by
    apply Finset.sum_congr rfl
    intro pilot hpilot
    ring
  rw [hRewrite]
  calc
    |∑ pilot : PauliPilotPath q,
      pauliPilotPathMass theta pilot * (f pilot - g pilot)| ≤
        ∑ pilot : PauliPilotPath q,
          |pauliPilotPathMass theta pilot * (f pilot - g pilot)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ pilot : PauliPilotPath q,
        pauliPilotPathMass theta pilot * |f pilot - g pilot| := by
      apply Finset.sum_congr rfl
      intro pilot hpilot
      rw [abs_mul,
        abs_of_nonneg
          (pauliPilotPathMass_nonnegative theta hPhysical pilot)]
    _ ≤ ∑ pilot : PauliPilotPath q,
        pauliPilotPathMass theta pilot * c :=
      Finset.sum_le_sum fun pilot _ =>
        mul_le_mul_of_nonneg_left (hPointwise pilot)
          (pauliPilotPathMass_nonnegative theta hPhysical pilot)
    _ = c := by
      rw [← Finset.sum_mul, pauliPilotPathMass_sum_one]
      ring

/-- The precise higher-order expectation bound from the previous file is now
closed, with constant
`(45 * (13/(32 gap))^2 + 180/eta^4) / 4`. -/
theorem mixedPolynomialOrdinaryInfidelityHigherOrderExpectationBound_closed
    (theta b : RLSVector 3)
    (hInterior : blochNormSq theta < 1)
    (hPhysical : PauliPilotPhysicalBloch theta) :
    MixedPolynomialOrdinaryInfidelityHigherOrderExpectationBound theta b := by
  let coefficient := mixedBuresLocalQuadraticEnvelopeCoefficient theta
  let eta := mixedBuresFidelityLocalRadius theta
  refine ⟨(45 * coefficient ^ 2 + 180 / eta ^ 4) / 4, ?_, ?_⟩
  · have hCoefficient :=
      mixedBuresLocalQuadraticEnvelopeCoefficient_nonnegative hInterior
    have hEta := mixedBuresFidelityLocalRadius_pos hInterior
    positivity
  · intro n
    rw [mixedPolynomialFinalStageExpectedScaledOrdinaryInfidelityRiskReal_eq_pilotAverage
      theta b hPhysical n,
      mixedPolynomialFinalStageExpectedScaledExactBuresRiskReal_eq_pilotAverage]
    have hq := mixedPolynomialQuadraticQFinal_pos n
    have hRateNonnegative :
        0 ≤ mixedFrameScaledBuresSecondMomentRate theta
          (mixedPolynomialQuadraticQFinal n) / 4 := by
      have hCoefficient :=
        mixedBuresLocalQuadraticEnvelopeCoefficient_nonnegative hInterior
      have hEta := mixedBuresFidelityLocalRadius_pos hInterior
      unfold mixedFrameScaledBuresSecondMomentRate
      dsimp only
      positivity
    have hAverage :=
      pauliPilotFiniteExpectation_abs_sub_le_constant_ordinary
        theta hPhysical
        (fun pilot : PauliPilotPath (Nat.succ (polynomialPilotIndex n)) =>
          mixedFrameConditionalScaledOrdinaryInfidelityRisk
            (q := mixedPolynomialQuadraticQFinal n) theta
            (mixedPilotSelectedLocalFrame b (pauliPilotEstimate pilot)))
        (fun pilot => mixedFrameConditionalScaledSafeguardedBuresRisk
          (q := mixedPolynomialQuadraticQFinal n) theta
          (mixedPilotSelectedLocalFrame b (pauliPilotEstimate pilot)))
        (mixedFrameScaledBuresSecondMomentRate theta
          (mixedPolynomialQuadraticQFinal n) / 4)
        hRateNonnegative
        (fun pilot => mixedFrameConditionalOrdinaryInfidelity_abs_sub_bures_le
          hq theta hInterior hPhysical
          (mixedPilotSelectedLocalFrame b (pauliPilotEstimate pilot))
          (mixedPilotSelectedLocalFrame_orthonormal _ _))
    unfold mixedFrameScaledBuresSecondMomentRate at hAverage
    dsimp [coefficient, eta] at hAverage ⊢
    convert hAverage using 1 <;> ring

/-! ## Ordinary-infidelity endpoints -/

/-- Final-stage-scaled finite two-stage ordinary infidelity. -/
def mixedPolynomialFinalStageExpectedScaledOrdinaryInfidelityRisk
    (theta b : RLSVector 3) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (mixedPolynomialFinalStageExpectedScaledOrdinaryInfidelityRiskReal theta b n)

theorem mixedPolynomialFinalStageExpectedScaledOrdinaryInfidelityRiskReal_tendsto_nine_fourths
    (theta b : RLSVector 3)
    (hPositive : 0 < blochNormSq theta)
    (hInterior : blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hPhysical : PauliPilotPhysicalBloch theta)
    (hHoeffding : PauliPilotConsistencyHoeffdingContracts theta hPhysical) :
    Tendsto
      (mixedPolynomialFinalStageExpectedScaledOrdinaryInfidelityRiskReal theta b)
      atTop (nhds (9 / 4 : ℝ)) :=
  mixedPolynomialFinalStageExpectedScaledOrdinaryInfidelityRiskReal_tendsto_nine_fourths_of_higherOrder
    theta b hPositive hInterior hSeed hPhysical hHoeffding
    (mixedPolynomialOrdinaryInfidelityHigherOrderExpectationBound_closed
      theta b hInterior hPhysical)

/-- Final-stage-scaled ordinary infidelity tends to `9/4`. -/
theorem mixedPolynomialFinalStageExpectedScaledOrdinaryInfidelityRisk_tendsto_nine_fourths
    (theta b : RLSVector 3)
    (hPositive : 0 < blochNormSq theta)
    (hInterior : blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hPhysical : PauliPilotPhysicalBloch theta)
    (hHoeffding : PauliPilotConsistencyHoeffdingContracts theta hPhysical) :
    Tendsto
      (mixedPolynomialFinalStageExpectedScaledOrdinaryInfidelityRisk theta b)
      atTop (nhds (ENNReal.ofReal (9 / 4 : ℝ))) := by
  exact (ENNReal.continuous_ofReal.tendsto (9 / 4 : ℝ)).comp
    (mixedPolynomialFinalStageExpectedScaledOrdinaryInfidelityRiskReal_tendsto_nine_fourths
      theta b hPositive hInterior hSeed hPhysical hHoeffding)

/-- Pilot-plus-final total-observation scaling for ordinary infidelity. -/
def mixedPolynomialTotalObservationScaledExpectedOrdinaryInfidelityRisk
    (theta b : RLSVector 3) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (mixedPolynomialExactCycleTotalToFinalRatio n) *
    mixedPolynomialFinalStageExpectedScaledOrdinaryInfidelityRisk theta b n

/-- Total-observation-scaled ordinary infidelity tends to `9/4`. -/
theorem mixedPolynomialTotalObservationScaledExpectedOrdinaryInfidelityRisk_tendsto_nine_fourths
    (theta b : RLSVector 3)
    (hPositive : 0 < blochNormSq theta)
    (hInterior : blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hPhysical : PauliPilotPhysicalBloch theta)
    (hHoeffding : PauliPilotConsistencyHoeffdingContracts theta hPhysical) :
    Tendsto
      (mixedPolynomialTotalObservationScaledExpectedOrdinaryInfidelityRisk theta b)
      atTop (nhds (ENNReal.ofReal (9 / 4 : ℝ))) := by
  have hRatioReal := mixedPolynomialExactCycleTotalToFinalRatio_tendsto_one
  have hRatio : Tendsto
      (fun n => ENNReal.ofReal
        (mixedPolynomialExactCycleTotalToFinalRatio n))
      atTop (nhds (ENNReal.ofReal (1 : ℝ))) := by
    change Tendsto
      (ENNReal.ofReal ∘ mixedPolynomialExactCycleTotalToFinalRatio)
      atTop (nhds (ENNReal.ofReal (1 : ℝ)))
    exact (ENNReal.continuous_ofReal.tendsto 1).comp hRatioReal
  have hOrdinary :=
    mixedPolynomialFinalStageExpectedScaledOrdinaryInfidelityRisk_tendsto_nine_fourths
      theta b hPositive hInterior hSeed hPhysical hHoeffding
  change Tendsto
    (fun n => ENNReal.ofReal (mixedPolynomialExactCycleTotalToFinalRatio n) *
      mixedPolynomialFinalStageExpectedScaledOrdinaryInfidelityRisk theta b n)
    atTop (nhds (ENNReal.ofReal (9 / 4 : ℝ)))
  simpa using
    ENNReal.Tendsto.mul hRatio (by simp) hOrdinary (by simp)

namespace Label

/-- Paper-facing fidelity-optimal endpoint for the concrete nonzero interior
mixed-qubit polynomial two-stage protocol.  The loss convention is ordinary
infidelity `1-F`, and the scaling uses all pilot and final observations. -/
theorem thm_mixed_polynomial_fidelity_optimal_endpoint_qubit
    (theta b : RLSVector 3)
    (hPositive : 0 < blochNormSq theta)
    (hInterior : blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hPhysical : PauliPilotPhysicalBloch theta)
    (hHoeffding : PauliPilotConsistencyHoeffdingContracts theta hPhysical) :
    Tendsto
      (mixedPolynomialTotalObservationScaledExpectedOrdinaryInfidelityRisk
        theta b)
      atTop (nhds (ENNReal.ofReal (9 / 4 : ℝ))) :=
  mixedPolynomialTotalObservationScaledExpectedOrdinaryInfidelityRisk_tendsto_nine_fourths
    theta b hPositive hInterior hSeed hPhysical hHoeffding

end Label

end
end Paper
end QubitOracle
