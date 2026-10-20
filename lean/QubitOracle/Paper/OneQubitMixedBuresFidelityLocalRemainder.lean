import QubitOracle.Paper.OneQubitMixedBuresFullRemainder
import QubitOracle.Paper.OneQubitMixedQuadraticLossCore
import QubitOracle.Paper.OneQubitMixedLocalBuresRadius

/-!
# Local mixed-qubit Bures and fidelity remainder

This file is deterministic.  At a fixed interior Bloch truth `theta`, it
specializes the clean algebraic remainder from
`OneQubitMixedBuresFullRemainder` to the displacement `theta + delta`.

The explicit neighborhood is

`eta(theta) = (1 - blochNormSq theta) / 8`.

Inside this neighborhood the displaced Bloch vector remains strictly inside
the unit ball, and the exact squared Bures loss differs from
`mixedInteriorBuresQuadraticLoss theta delta` by a cubic-plus-quartic envelope.
The squared-fidelity defect has the same quadratic term.  Root infidelity, and
therefore the decrement of root fidelity, has one half of that quadratic term.

No estimator expectation or exact nonlinear-risk transfer is performed here.
-/

noncomputable section

open scoped BigOperators

namespace QubitOracle.Paper

/-! ## Exact Bloch formulas -/

/-- Squared Uhlmann fidelity in the exact one-qubit Bloch formula. -/
def mixedQubitBlochFidelitySqBetween
    (theta sigma : Fin 3 → ℝ) : ℝ :=
  (1 + blochDot theta sigma +
      Real.sqrt
        ((1 - blochNormSq theta) * (1 - blochNormSq sigma))) / 2

/-- Root fidelity corresponding to `mixedQubitBlochFidelitySqBetween`. -/
def mixedQubitBlochRootFidelityBetween
    (theta sigma : Fin 3 → ℝ) : ℝ :=
  Real.sqrt (mixedQubitBlochFidelitySqBetween theta sigma)

/-- Infidelity in the squared-fidelity convention: `1 - F`. -/
def mixedQubitBlochInfidelityBetween
    (theta sigma : Fin 3 → ℝ) : ℝ :=
  1 - mixedQubitBlochFidelitySqBetween theta sigma

/-- Root infidelity: `1 - sqrt F`. -/
def mixedQubitBlochRootInfidelityBetween
    (theta sigma : Fin 3 → ℝ) : ℝ :=
  1 - mixedQubitBlochRootFidelityBetween theta sigma

/-- Exact squared Bures distance in the paper's fidelity convention. -/
def mixedQubitBlochBuresSqBetween
    (theta sigma : Fin 3 → ℝ) : ℝ :=
  2 * mixedQubitBlochRootInfidelityBetween theta sigma

/-- Euclidean Bloch norm used in the local remainder statement. -/
def mixedBlochEuclideanNorm (delta : Fin 3 → ℝ) : ℝ :=
  Real.sqrt (blochNormSq delta)

/-- Cubic-plus-quartic local envelope. -/
def mixedBuresFidelityLocalRemainderEnvelope
    (theta delta : Fin 3 → ℝ) : ℝ :=
  mixedBlochEuclideanNorm delta ^ 3 /
      (1 - blochNormSq theta) ^ 2 +
    2 * mixedBlochEuclideanNorm delta ^ 4 /
      (1 - blochNormSq theta) ^ 3

/-- Squared norm after an additive Bloch displacement. -/
theorem blochNormSq_add_displacement
    (theta delta : Fin 3 → ℝ) :
    blochNormSq (theta + delta) =
      blochNormSq theta + 2 * blochDot theta delta +
        blochNormSq delta := by
  simp only [blochNormSq, blochDot, Pi.add_apply, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- Dot product with an additively displaced second argument. -/
theorem blochDot_add_displacement
    (theta delta : Fin 3 → ℝ) :
    blochDot theta (theta + delta) =
      blochNormSq theta + blochDot theta delta := by
  simp [blochNormSq, blochDot, Pi.add_apply, mul_add,
    Finset.sum_add_distrib, pow_two]

/-- The general two-state fidelity formula reduces to the source-faithful
`rSq,x,q` formula at `sigma = theta + delta`. -/
theorem mixedQubitBlochFidelitySqBetween_add_eq
    (theta delta : Fin 3 → ℝ) :
    mixedQubitBlochFidelitySqBetween theta (theta + delta) =
      qubitBlochFidelitySq (blochNormSq theta)
        (blochDot theta delta) (blochNormSq delta) := by
  unfold mixedQubitBlochFidelitySqBetween qubitBlochFidelitySq
  rw [blochDot_add_displacement, blochNormSq_add_displacement]
  congr 2
  · ring
  · congr 1
    ring

/-- Exact root-fidelity formula for `theta` and `theta + delta`. -/
theorem mixedQubitBlochRootFidelityBetween_add_formula
    (theta delta : Fin 3 → ℝ) :
    mixedQubitBlochRootFidelityBetween theta (theta + delta) =
      Real.sqrt
        ((1 + blochNormSq theta + blochDot theta delta +
          Real.sqrt
            ((1 - blochNormSq theta) *
              (1 - blochNormSq theta -
                2 * blochDot theta delta - blochNormSq delta))) / 2) := by
  unfold mixedQubitBlochRootFidelityBetween
  rw [mixedQubitBlochFidelitySqBetween_add_eq]
  rfl

/-- Exact squared-fidelity infidelity formula for `theta` and
`theta + delta`. -/
theorem mixedQubitBlochInfidelityBetween_add_formula
    (theta delta : Fin 3 → ℝ) :
    mixedQubitBlochInfidelityBetween theta (theta + delta) =
      1 -
        ((1 + blochNormSq theta + blochDot theta delta +
          Real.sqrt
            ((1 - blochNormSq theta) *
              (1 - blochNormSq theta -
                2 * blochDot theta delta - blochNormSq delta))) / 2) := by
  unfold mixedQubitBlochInfidelityBetween
  rw [mixedQubitBlochFidelitySqBetween_add_eq]
  rfl

/-- Exact squared Bures formula for `theta` and `theta + delta`. -/
theorem mixedQubitBlochBuresSqBetween_add_formula
    (theta delta : Fin 3 → ℝ) :
    mixedQubitBlochBuresSqBetween theta (theta + delta) =
      2 *
        (1 - Real.sqrt
          ((1 + blochNormSq theta + blochDot theta delta +
            Real.sqrt
              ((1 - blochNormSq theta) *
                (1 - blochNormSq theta -
                  2 * blochDot theta delta - blochNormSq delta))) / 2)) := by
  unfold mixedQubitBlochBuresSqBetween
    mixedQubitBlochRootInfidelityBetween
    mixedQubitBlochRootFidelityBetween
  rw [mixedQubitBlochFidelitySqBetween_add_eq]
  rfl

/-- The two-state formula agrees exactly with the existing displacement-form
squared Bures loss. -/
theorem mixedQubitBlochBuresSqBetween_add_eq_mixedBlochBuresSq
    (theta delta : Fin 3 → ℝ) :
    mixedQubitBlochBuresSqBetween theta (theta + delta) =
      mixedBlochBuresSq theta delta := by
  unfold mixedQubitBlochBuresSqBetween
    mixedQubitBlochRootInfidelityBetween
    mixedQubitBlochRootFidelityBetween
    mixedBlochBuresSq qubitBlochBuresSq
  rw [mixedQubitBlochFidelitySqBetween_add_eq]

/-- Root infidelity is exactly one half of squared Bures distance. -/
theorem mixedQubitBlochRootInfidelityBetween_eq_half_bures
    (theta sigma : Fin 3 → ℝ) :
    mixedQubitBlochRootInfidelityBetween theta sigma =
      mixedQubitBlochBuresSqBetween theta sigma / 2 := by
  unfold mixedQubitBlochBuresSqBetween
  ring

/-! ## Concrete local domain -/

private theorem mixed_blochNormSq_nonnegative_local
    (x : Fin 3 → ℝ) : 0 ≤ blochNormSq x := by
  unfold blochNormSq
  exact Finset.sum_nonneg fun j _ => sq_nonneg (x j)

/-- The Euclidean Bloch norm is nonnegative. -/
theorem mixedBlochEuclideanNorm_nonnegative
    (delta : Fin 3 → ℝ) :
    0 ≤ mixedBlochEuclideanNorm delta := by
  exact Real.sqrt_nonneg _

/-- Its square is exactly `blochNormSq`. -/
theorem mixedBlochEuclideanNorm_sq
    (delta : Fin 3 → ℝ) :
    mixedBlochEuclideanNorm delta ^ 2 = blochNormSq delta := by
  unfold mixedBlochEuclideanNorm
  exact Real.sq_sqrt (mixed_blochNormSq_nonnegative_local delta)

/-- At a physical truth, Cauchy--Schwarz bounds the radial displacement by the
Euclidean displacement norm. -/
theorem abs_blochDot_le_mixedBlochEuclideanNorm
    {theta delta : Fin 3 → ℝ}
    (hTheta : blochNormSq theta ≤ 1) :
    |blochDot theta delta| ≤ mixedBlochEuclideanNorm delta := by
  have hDelta : 0 ≤ blochNormSq delta :=
    mixed_blochNormSq_nonnegative_local delta
  have hCauchy := bloch_cauchy_schwarz theta delta
  have hProduct :
      blochNormSq theta * blochNormSq delta ≤ blochNormSq delta := by
    have hNonnegative :
        0 ≤ (1 - blochNormSq theta) * blochNormSq delta :=
      mul_nonneg (sub_nonneg.mpr hTheta) hDelta
    nlinarith
  have hDotSq :
      (blochDot theta delta) ^ 2 ≤ blochNormSq delta :=
    hCauchy.trans hProduct
  have hAbsSq : |blochDot theta delta| ^ 2 =
      (blochDot theta delta) ^ 2 := sq_abs _
  have hNormSq := mixedBlochEuclideanNorm_sq delta
  have hAbsNonnegative := abs_nonneg (blochDot theta delta)
  have hNormNonnegative := mixedBlochEuclideanNorm_nonnegative delta
  nlinarith

/-- The norm-radius assumption implies the exact scalar neighborhood required
by the rationalized square-root proof. -/
theorem mixedBuresFidelityLocalRadius_implies_scalar_local
    {theta delta : Fin 3 → ℝ}
    (hInterior : blochNormSq theta < 1)
    (hDelta : mixedBlochEuclideanNorm delta ≤
      mixedBuresFidelityLocalRadius theta) :
    2 * |blochDot theta delta| + blochNormSq delta ≤
      (1 - blochNormSq theta) / 2 := by
  let gap : ℝ := 1 - blochNormSq theta
  let d : ℝ := mixedBlochEuclideanNorm delta
  have hGap : 0 < gap := by
    dsimp [gap]
    linarith
  have hThetaNonnegative := mixed_blochNormSq_nonnegative_local theta
  have hGapLeOne : gap ≤ 1 := by
    dsimp [gap]
    linarith
  have hGapProduct : 0 ≤ gap * (1 - gap) :=
    mul_nonneg hGap.le (sub_nonneg.mpr hGapLeOne)
  have hEta : mixedBuresFidelityLocalRadius theta = gap / 8 := rfl
  have hDNonnegative : 0 ≤ d :=
    mixedBlochEuclideanNorm_nonnegative delta
  have hEtaNonnegative : 0 ≤ gap / 8 := by positivity
  have hDLe : d ≤ gap / 8 := by
    simpa [hEta, d] using hDelta
  have hSquareOrder : d ^ 2 ≤ (gap / 8) ^ 2 := by
    have hProduct := mul_nonneg (sub_nonneg.mpr hDLe)
      (add_nonneg hEtaNonnegative hDNonnegative)
    nlinarith
  have hNormSq : blochNormSq delta = d ^ 2 := by
    simpa [d] using (mixedBlochEuclideanNorm_sq delta).symm
  have hDot : |blochDot theta delta| ≤ d :=
    abs_blochDot_le_mixedBlochEuclideanNorm (le_of_lt hInterior)
  rw [hNormSq]
  dsimp [gap] at hGap hGapLeOne hGapProduct ⊢
  nlinarith

/-- The explicit local radius keeps the displaced Bloch vector strictly
inside the Bloch ball. -/
theorem mixedBuresFidelityLocalRadius_keeps_inside
    {theta delta : Fin 3 → ℝ}
    (hInterior : blochNormSq theta < 1)
    (hDelta : mixedBlochEuclideanNorm delta ≤
      mixedBuresFidelityLocalRadius theta) :
    blochNormSq (theta + delta) < 1 := by
  have hLocal :=
    mixedBuresFidelityLocalRadius_implies_scalar_local hInterior hDelta
  have hDotUpper :
      blochDot theta delta ≤ |blochDot theta delta| :=
    le_abs_self _
  rw [blochNormSq_add_displacement]
  nlinarith

/-- The explicit norm ball supplies all hypotheses of the clean scalar
remainder theorem, with margin equal to the true radial gap. -/
theorem mixedBuresFidelityLocal_scalarRegion
    {theta delta : Fin 3 → ℝ}
    (hInterior : blochNormSq theta < 1)
    (hDelta : mixedBlochEuclideanNorm delta ≤
      mixedBuresFidelityLocalRadius theta) :
    MixedBuresGeneralScalarRegion
      (blochNormSq theta) (blochDot theta delta)
      (blochNormSq delta) (1 - blochNormSq theta) where
  radius_nonnegative := mixed_blochNormSq_nonnegative_local theta
  margin_positive := sub_pos.mpr hInterior
  margin_le_gap := le_rfl
  displacement_nonnegative := mixed_blochNormSq_nonnegative_local delta
  cauchy := bloch_cauchy_schwarz theta delta
  local_radius :=
    mixedBuresFidelityLocalRadius_implies_scalar_local hInterior hDelta

/-! ## Quadratic identification and Bures remainder -/

/-- The scalar quadratic term is exactly the quadratic loss used by the mixed
polynomial risk endpoint. -/
theorem mixedInteriorBuresQuadraticLoss_eq_generalQuadratic
    (theta delta : Fin 3 → ℝ) :
    mixedInteriorBuresQuadraticLoss theta delta =
      mixedBuresGeneralQuadratic (blochNormSq theta)
        (blochDot theta delta) (blochNormSq delta) := by
  unfold mixedInteriorBuresQuadraticLoss
    mixedBuresGeneralQuadratic mixedBuresGeneralGap
  by_cases hgap : 1 - blochNormSq theta = 0
  · simp [hgap]
    ring
  · field_simp [hgap]

/-- Exact second-order decomposition.  The last term contains the genuine
sign-changing cubic radial contribution. -/
theorem mixedQubitBlochBuresSqBetween_add_secondOrder_decomposition
    {theta delta : Fin 3 → ℝ}
    (hInterior : blochNormSq theta < 1)
    (hDelta : mixedBlochEuclideanNorm delta ≤
      mixedBuresFidelityLocalRadius theta) :
    mixedQubitBlochBuresSqBetween theta (theta + delta) =
      mixedInteriorBuresQuadraticLoss theta delta +
        (1 - mixedQubitBlochRootFidelityBetween
          theta (theta + delta)) ^ 2 +
        mixedBuresGeneralOddTerm (blochNormSq theta)
          (blochDot theta delta) (blochNormSq delta) := by
  have hRegion :=
    mixedBuresFidelityLocal_scalarRegion hInterior hDelta
  have hExact := mixedBuresGeneral_exact_remainder_decomposition hRegion
  rw [mixedQubitBlochBuresSqBetween_add_eq_mixedBlochBuresSq,
    mixedInteriorBuresQuadraticLoss_eq_generalQuadratic]
  unfold mixedBlochBuresSq at ⊢
  rw [mixedQubitBlochRootFidelityBetween_add_formula]
  unfold qubitBlochFidelitySq at hExact
  linarith

/-- Coordinate-level local remainder inherited from the exact rationalized
square-root calculation. -/
theorem mixedQubitBlochBuresSqBetween_add_coordinate_remainder
    {theta delta : Fin 3 → ℝ}
    (hInterior : blochNormSq theta < 1)
    (hDelta : mixedBlochEuclideanNorm delta ≤
      mixedBuresFidelityLocalRadius theta) :
    |mixedQubitBlochBuresSqBetween theta (theta + delta) -
        mixedInteriorBuresQuadraticLoss theta delta| ≤
      |blochDot theta delta| * blochNormSq delta /
          (1 - blochNormSq theta) ^ 2 +
        (((blochDot theta delta) ^ 2 * blochNormSq delta +
          (blochNormSq delta) ^ 2) /
            (1 - blochNormSq theta) ^ 3) := by
  have hRegion :=
    mixedBuresFidelityLocal_scalarRegion hInterior hDelta
  have hBound := qubitBlochBuresSq_general_margin_remainder hRegion
  rw [mixedQubitBlochBuresSqBetween_add_eq_mixedBlochBuresSq,
    mixedInteriorBuresQuadraticLoss_eq_generalQuadratic]
  exact hBound

/-- Explicit cubic-plus-quartic Euclidean local remainder. -/
theorem mixedQubitBlochBuresSqBetween_add_local_remainder
    {theta delta : Fin 3 → ℝ}
    (hInterior : blochNormSq theta < 1)
    (hDelta : mixedBlochEuclideanNorm delta ≤
      mixedBuresFidelityLocalRadius theta) :
    |mixedQubitBlochBuresSqBetween theta (theta + delta) -
        mixedInteriorBuresQuadraticLoss theta delta| ≤
      mixedBuresFidelityLocalRemainderEnvelope theta delta := by
  let d : ℝ := mixedBlochEuclideanNorm delta
  let gap : ℝ := 1 - blochNormSq theta
  have hGap : 0 < gap := by
    dsimp [gap]
    linarith
  have hQ : 0 ≤ blochNormSq delta :=
    mixed_blochNormSq_nonnegative_local delta
  have hD : 0 ≤ d := by
    exact mixedBlochEuclideanNorm_nonnegative delta
  have hDSq : d ^ 2 = blochNormSq delta := by
    simpa [d] using mixedBlochEuclideanNorm_sq delta
  have hDotAbs : |blochDot theta delta| ≤ d :=
    abs_blochDot_le_mixedBlochEuclideanNorm (le_of_lt hInterior)
  have hDotSq : (blochDot theta delta) ^ 2 ≤ blochNormSq delta := by
    calc
      (blochDot theta delta) ^ 2 ≤
          blochNormSq theta * blochNormSq delta :=
        bloch_cauchy_schwarz theta delta
      _ ≤ blochNormSq delta := by
        have hProduct :
            0 ≤ (1 - blochNormSq theta) * blochNormSq delta :=
          mul_nonneg (sub_nonneg.mpr (le_of_lt hInterior)) hQ
        nlinarith
  have hCubicNumerator :
      |blochDot theta delta| * blochNormSq delta ≤ d ^ 3 := by
    calc
      |blochDot theta delta| * blochNormSq delta
          ≤ d * blochNormSq delta :=
        mul_le_mul_of_nonneg_right hDotAbs hQ
      _ = d ^ 3 := by rw [← hDSq]; ring
  have hQuarticNumerator :
      (blochDot theta delta) ^ 2 * blochNormSq delta +
          (blochNormSq delta) ^ 2 ≤ 2 * d ^ 4 := by
    have hFirst :
        (blochDot theta delta) ^ 2 * blochNormSq delta ≤
          (blochNormSq delta) ^ 2 := by
      simpa [pow_two] using mul_le_mul_of_nonneg_right hDotSq hQ
    rw [← hDSq] at hFirst ⊢
    nlinarith
  have hCoordinate :=
    mixedQubitBlochBuresSqBetween_add_coordinate_remainder
      hInterior hDelta
  calc
    |mixedQubitBlochBuresSqBetween theta (theta + delta) -
        mixedInteriorBuresQuadraticLoss theta delta|
        ≤ |blochDot theta delta| * blochNormSq delta / gap ^ 2 +
          ((blochDot theta delta) ^ 2 * blochNormSq delta +
            (blochNormSq delta) ^ 2) / gap ^ 3 := by
          simpa [gap] using hCoordinate
    _ ≤ d ^ 3 / gap ^ 2 + 2 * d ^ 4 / gap ^ 3 := by
      exact add_le_add
        (div_le_div_of_nonneg_right hCubicNumerator
          (sq_nonneg gap))
        (div_le_div_of_nonneg_right hQuarticNumerator
          (pow_nonneg hGap.le 3))
    _ = mixedBuresFidelityLocalRemainderEnvelope theta delta := by
      rfl

/-! ## Fidelity, infidelity, and root-fidelity conversion -/

/-- Squared-fidelity infidelity has exactly the same quadratic term; unlike the
Bures loss it has only the explicit odd term as its remainder. -/
theorem mixedQubitBlochInfidelityBetween_add_secondOrder_expansion
    {theta delta : Fin 3 → ℝ}
    (hInterior : blochNormSq theta < 1)
    (hDelta : mixedBlochEuclideanNorm delta ≤
      mixedBuresFidelityLocalRadius theta) :
    mixedQubitBlochInfidelityBetween theta (theta + delta) =
      mixedInteriorBuresQuadraticLoss theta delta +
        mixedBuresGeneralOddTerm (blochNormSq theta)
          (blochDot theta delta) (blochNormSq delta) := by
  have hRegion :=
    mixedBuresFidelityLocal_scalarRegion hInterior hDelta
  have hExpansion :=
    mixedBuresGeneral_fidelityDefect_sub_quadratic hRegion
  rw [mixedQubitBlochInfidelityBetween_add_formula,
    mixedInteriorBuresQuadraticLoss_eq_generalQuadratic]
  unfold mixedBuresGeneralFidelityDefect qubitBlochFidelitySq at hExpansion
  linarith

/-- Exact coordinate remainder for squared-fidelity infidelity. -/
theorem mixedQubitBlochInfidelityBetween_add_coordinate_remainder
    {theta delta : Fin 3 → ℝ}
    (hInterior : blochNormSq theta < 1)
    (hDelta : mixedBlochEuclideanNorm delta ≤
      mixedBuresFidelityLocalRadius theta) :
    |mixedQubitBlochInfidelityBetween theta (theta + delta) -
        mixedInteriorBuresQuadraticLoss theta delta| ≤
      |blochDot theta delta| * blochNormSq delta /
          (1 - blochNormSq theta) ^ 2 +
        (blochDot theta delta) ^ 2 * blochNormSq delta /
          (4 * (1 - blochNormSq theta) ^ 3) +
        (blochNormSq delta) ^ 2 /
          (4 * (1 - blochNormSq theta) ^ 2) := by
  have hRegion :=
    mixedBuresFidelityLocal_scalarRegion hInterior hDelta
  have hOdd := mixedBuresGeneral_oddTerm_abs_le hRegion
  rw [mixedQubitBlochInfidelityBetween_add_secondOrder_expansion
    hInterior hDelta]
  simpa [mixedBuresGeneralGap] using hOdd

/-- Squared fidelity itself equals one minus the common quadratic term and the
odd remainder. -/
theorem mixedQubitBlochFidelitySqBetween_add_secondOrder_expansion
    {theta delta : Fin 3 → ℝ}
    (hInterior : blochNormSq theta < 1)
    (hDelta : mixedBlochEuclideanNorm delta ≤
      mixedBuresFidelityLocalRadius theta) :
    mixedQubitBlochFidelitySqBetween theta (theta + delta) =
      1 - mixedInteriorBuresQuadraticLoss theta delta -
        mixedBuresGeneralOddTerm (blochNormSq theta)
          (blochDot theta delta) (blochNormSq delta) := by
  have hInfidelity :=
    mixedQubitBlochInfidelityBetween_add_secondOrder_expansion
      hInterior hDelta
  unfold mixedQubitBlochInfidelityBetween at hInfidelity
  linarith

/-- Root fidelity has one half of the Bures quadratic coefficient.  Its
absolute remainder is one half of the proved Bures envelope. -/
theorem mixedQubitBlochRootFidelityBetween_add_local_remainder
    {theta delta : Fin 3 → ℝ}
    (hInterior : blochNormSq theta < 1)
    (hDelta : mixedBlochEuclideanNorm delta ≤
      mixedBuresFidelityLocalRadius theta) :
    |mixedQubitBlochRootFidelityBetween theta (theta + delta) -
        (1 - mixedInteriorBuresQuadraticLoss theta delta / 2)| ≤
      mixedBuresFidelityLocalRemainderEnvelope theta delta / 2 := by
  have hBures :=
    mixedQubitBlochBuresSqBetween_add_local_remainder
      hInterior hDelta
  have hIdentity :
      mixedQubitBlochRootFidelityBetween theta (theta + delta) -
          (1 - mixedInteriorBuresQuadraticLoss theta delta / 2) =
        -(mixedQubitBlochBuresSqBetween theta (theta + delta) -
          mixedInteriorBuresQuadraticLoss theta delta) / 2 := by
    unfold mixedQubitBlochBuresSqBetween
      mixedQubitBlochRootInfidelityBetween
    ring
  rw [hIdentity, abs_div, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact div_le_div_of_nonneg_right hBures (by norm_num)

/-- Root infidelity has quadratic coefficient `1/2` relative to squared Bures
and squared-fidelity infidelity. -/
theorem mixedQubitBlochRootInfidelityBetween_add_local_remainder
    {theta delta : Fin 3 → ℝ}
    (hInterior : blochNormSq theta < 1)
    (hDelta : mixedBlochEuclideanNorm delta ≤
      mixedBuresFidelityLocalRadius theta) :
    |mixedQubitBlochRootInfidelityBetween theta (theta + delta) -
        mixedInteriorBuresQuadraticLoss theta delta / 2| ≤
      mixedBuresFidelityLocalRemainderEnvelope theta delta / 2 := by
  rw [mixedQubitBlochRootInfidelityBetween_eq_half_bures]
  have hBures :=
    mixedQubitBlochBuresSqBetween_add_local_remainder
      hInterior hDelta
  have hIdentity :
      mixedQubitBlochBuresSqBetween theta (theta + delta) / 2 -
          mixedInteriorBuresQuadraticLoss theta delta / 2 =
        (mixedQubitBlochBuresSqBetween theta (theta + delta) -
          mixedInteriorBuresQuadraticLoss theta delta) / 2 := by ring
  rw [hIdentity, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact div_le_div_of_nonneg_right hBures (by norm_num)

namespace Label

/-- Paper-facing nonzero-interior local Bures/fidelity remainder reduction.
The nonzero hypothesis records the intended mixed protocol stratum; the
calculus bound itself remains valid at the maximally mixed truth. -/
theorem lem_SI_mixed_bures_fidelity_local_remainder_qubit
    {theta : Fin 3 → ℝ}
    (hNonzero : 0 < blochNormSq theta)
    (hInterior : blochNormSq theta < 1) :
    0 < mixedBuresFidelityLocalRadius theta ∧
      ∀ delta : Fin 3 → ℝ,
        mixedBlochEuclideanNorm delta ≤
            mixedBuresFidelityLocalRadius theta →
          blochNormSq (theta + delta) < 1 ∧
          |mixedQubitBlochBuresSqBetween theta (theta + delta) -
              mixedInteriorBuresQuadraticLoss theta delta| ≤
            mixedBuresFidelityLocalRemainderEnvelope theta delta ∧
          |mixedQubitBlochRootFidelityBetween theta (theta + delta) -
              (1 - mixedInteriorBuresQuadraticLoss theta delta / 2)| ≤
            mixedBuresFidelityLocalRemainderEnvelope theta delta / 2 := by
  have _hNonzero := hNonzero
  refine ⟨mixedBuresFidelityLocalRadius_pos hInterior, ?_⟩
  intro delta hDelta
  exact ⟨
    mixedBuresFidelityLocalRadius_keeps_inside hInterior hDelta,
    mixedQubitBlochBuresSqBetween_add_local_remainder hInterior hDelta,
    mixedQubitBlochRootFidelityBetween_add_local_remainder hInterior hDelta⟩

end Label
end QubitOracle.Paper
