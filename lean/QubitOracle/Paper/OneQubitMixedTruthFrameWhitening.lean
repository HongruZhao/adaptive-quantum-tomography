import QubitOracle.Paper.OneQubitMixedTruthFrameInformationMatrix

/-!
# Explicit truth-frame whitening for the mixed one-qubit protocol

The finite map below converts a local coordinate vector into a physical Bloch
direction.  Coordinate `k` is scaled by the square root of the Bernoulli
variance along the `k`th limiting adaptive axis.  All identities are finite
three-dimensional calculations; this file introduces no external theorem atom.
-/

open Matrix
open scoped BigOperators

namespace QubitOracle.Paper

noncomputable section

/-- Bernoulli variance denominator along one limiting truth-frame axis. -/
def mixedPolynomialTruthFrameDenominator
    (theta b : Fin 3 → ℝ) (k : Fin 3) : ℝ :=
  1 - (blochDot theta
    (mixedTwoStageFrameAxis
      (localContinuousQubitFrame b theta) k)) ^ 2

/-- The limiting truth-frame axes are orthonormal. -/
theorem mixedPolynomialTruthFrameAxes_orthogonal
    (theta b : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (k l : Fin 3) :
    blochDot
        (mixedTwoStageFrameAxis
          (localContinuousQubitFrame b theta) k)
        (mixedTwoStageFrameAxis
          (localContinuousQubitFrame b theta) l) =
      if k = l then 1 else 0 := by
  change blochDot
      (qubitFrameAxis (localContinuousQubitFrame b theta) k)
      (qubitFrameAxis (localContinuousQubitFrame b theta) l) =
    if k = l then 1 else 0
  exact localContinuousQubitFrame_axes_orthogonal
    (b := b) (x := theta) ⟨hTruth.1, hSeed⟩ k l

/-- Every whitening denominator is strictly positive at an interior truth. -/
theorem mixedPolynomialTruthFrameDenominator_pos
    (theta b : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (k : Fin 3) :
    0 < mixedPolynomialTruthFrameDenominator theta b k := by
  unfold mixedPolynomialTruthFrameDenominator
  apply mixedTwoStageAxisFisherDenominator_pos theta _ hTruth.2
  change blochNormSq
    (qubitFrameAxis (localContinuousQubitFrame b theta) k) = 1
  exact localContinuousQubitFrame_axis_unit ⟨hTruth.1, hSeed⟩ k

/-- Explicit physical Bloch direction associated with a whitened local
coordinate vector. -/
def mixedPolynomialTruthFrameWhiteningDirection
    (theta b h : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => ∑ k : Fin 3,
    mixedTwoStageFrameAxis
        (localContinuousQubitFrame b theta) k i *
      (Real.sqrt (mixedPolynomialTruthFrameDenominator theta b k) * h k)

/-- The whitening map preserves zero. -/
@[simp]
theorem mixedPolynomialTruthFrameWhiteningDirection_zero
    (theta b : Fin 3 → ℝ) :
    mixedPolynomialTruthFrameWhiteningDirection theta b 0 = 0 := by
  funext i
  simp [mixedPolynomialTruthFrameWhiteningDirection]

/-- The whitening map is additive. -/
theorem mixedPolynomialTruthFrameWhiteningDirection_add
    (theta b h g : Fin 3 → ℝ) :
    mixedPolynomialTruthFrameWhiteningDirection theta b (h + g) =
      mixedPolynomialTruthFrameWhiteningDirection theta b h +
        mixedPolynomialTruthFrameWhiteningDirection theta b g := by
  funext i
  unfold mixedPolynomialTruthFrameWhiteningDirection
  rw [Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Pi.add_apply]
  ring

/-- The whitening map commutes with real scalar multiplication. -/
theorem mixedPolynomialTruthFrameWhiteningDirection_smul
    (theta b h : Fin 3 → ℝ) (c : ℝ) :
    mixedPolynomialTruthFrameWhiteningDirection theta b (c • h) =
      c • mixedPolynomialTruthFrameWhiteningDirection theta b h := by
  funext i
  unfold mixedPolynomialTruthFrameWhiteningDirection
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Analysis of a synthesized whitened direction recovers the scaled
coordinate exactly. -/
theorem mixedPolynomialTruthFrameWhiteningDirection_projection
    (theta b h : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (j : Fin 3) :
    blochDot
        (mixedPolynomialTruthFrameWhiteningDirection theta b h)
        (mixedTwoStageFrameAxis
          (localContinuousQubitFrame b theta) j) =
      Real.sqrt (mixedPolynomialTruthFrameDenominator theta b j) * h j := by
  calc
    blochDot
        (mixedPolynomialTruthFrameWhiteningDirection theta b h)
        (mixedTwoStageFrameAxis
          (localContinuousQubitFrame b theta) j) =
      ∑ k : Fin 3,
        (Real.sqrt
            (mixedPolynomialTruthFrameDenominator theta b k) * h k) *
          blochDot
            (mixedTwoStageFrameAxis
              (localContinuousQubitFrame b theta) k)
            (mixedTwoStageFrameAxis
              (localContinuousQubitFrame b theta) j) := by
        simp [mixedPolynomialTruthFrameWhiteningDirection,
          blochDot, Fin.sum_univ_succ]
        ring
    _ = Real.sqrt
        (mixedPolynomialTruthFrameDenominator theta b j) * h j := by
      simp_rw [mixedPolynomialTruthFrameAxes_orthogonal
        theta b hTruth hSeed]
      simp

/-- Exact Fisher whitening identity.  In these coordinates the concrete
truth-frame directional information is one third of the Euclidean squared
norm. -/
theorem mixedPolynomialTruthFrameDirectionalInformation_whitened
    (theta b h : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    mixedPolynomialTruthFrameDirectionalInformation theta
        (mixedPolynomialTruthFrameWhiteningDirection theta b h) b =
      (1 / 3 : ℝ) * blochNormSq h := by
  unfold mixedPolynomialTruthFrameDirectionalInformation
    mixedPolynomialFrameDirectionalInformation
  apply congrArg (fun x : ℝ => (1 / 3 : ℝ) * x)
  rw [show blochNormSq h = ∑ k : Fin 3, (h k) ^ 2 by
    rfl]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mixedPolynomialTruthFrameWhiteningDirection_projection
    theta b h hTruth hSeed k]
  change
    (Real.sqrt (mixedPolynomialTruthFrameDenominator theta b k) * h k) ^ 2 /
        mixedPolynomialTruthFrameDenominator theta b k =
      (h k) ^ 2
  have hd := mixedPolynomialTruthFrameDenominator_pos
    theta b hTruth hSeed k
  rw [mul_pow, Real.sq_sqrt (le_of_lt hd)]
  field_simp [ne_of_gt hd]

/-- Matrix form of the same whitening identity. -/
theorem mixedPolynomialTruthFrameInformationMatrix_whitened_quadratic
    (theta b h : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    dotProduct
        (mixedPolynomialTruthFrameWhiteningDirection theta b h)
        ((mixedPolynomialTruthFrameInformationMatrix theta b).mulVec
          (mixedPolynomialTruthFrameWhiteningDirection theta b h)) =
      (1 / 3 : ℝ) * blochNormSq h := by
  rw [mixedPolynomialTruthFrameInformationMatrix_quadratic]
  exact mixedPolynomialTruthFrameDirectionalInformation_whitened
    theta b h hTruth hSeed

end

end QubitOracle.Paper
