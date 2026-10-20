import QubitOracle.FiniteGillMassar
/-! Supporting definitions and proved lemmas used by the manuscript. -/

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




/-! ## Quadratic identification and Bures remainder -/





/-! ## Fidelity, infidelity, and root-fidelity conversion -/






namespace Label


end Label
end QubitOracle.Paper
