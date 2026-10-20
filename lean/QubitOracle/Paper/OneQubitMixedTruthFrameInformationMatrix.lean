import QubitOracle.Paper.OneQubitMixedPolynomialScalarLANClosed

/-!
# Concrete truth-frame Fisher matrix for the polynomial mixed-qubit protocol

This file packages the directional information used by the scalar LAN theorem
as an explicit three-by-three matrix. The quadratic-form identity is finite
algebra and is proved by the Lean kernel; no literature atom is introduced.
-/

open Matrix
open scoped BigOperators

namespace QubitOracle.Paper

noncomputable section

/-- Per-total-observation Fisher matrix of the limiting selected truth frame,
written in Bloch coordinates. -/
def mixedPolynomialTruthFrameInformationMatrix
    (theta b : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j =>
    (1 / 3 : ℝ) * ∑ k : Fin 3,
      mixedTwoStageFrameAxis (localContinuousQubitFrame b theta) k i *
          mixedTwoStageFrameAxis (localContinuousQubitFrame b theta) k j /
        (1 -
          (blochDot theta
            (mixedTwoStageFrameAxis
              (localContinuousQubitFrame b theta) k)) ^ 2)

/-- The concrete truth-frame information matrix is symmetric. -/
theorem mixedPolynomialTruthFrameInformationMatrix_transpose
    (theta b : Fin 3 → ℝ) :
    (mixedPolynomialTruthFrameInformationMatrix theta b).transpose =
      mixedPolynomialTruthFrameInformationMatrix theta b := by
  ext i j
  simp only [Matrix.transpose_apply,
    mixedPolynomialTruthFrameInformationMatrix]
  apply congrArg (fun x : ℝ => (1 / 3 : ℝ) * x)
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Exact matrix representation of the scalar directional information:
the quadratic form h' J h equals the directional Fisher information. -/
theorem mixedPolynomialTruthFrameInformationMatrix_quadratic
    (theta h b : Fin 3 → ℝ) :
    dotProduct h
        ((mixedPolynomialTruthFrameInformationMatrix theta b).mulVec h) =
      mixedPolynomialTruthFrameDirectionalInformation theta h b := by
  simp only [mixedPolynomialTruthFrameInformationMatrix,
    mixedPolynomialTruthFrameDirectionalInformation,
    mixedPolynomialFrameDirectionalInformation,
    Matrix.mulVec, dotProduct, blochDot, Fin.sum_univ_succ]
  ring

/-- Parseval identity for the concrete continuous local frame. -/
theorem mixedPolynomialTruthFrame_parseval
    (theta h b : Fin 3 → ℝ)
    (hDomain : LocalContinuousFrameDomain b theta) :
    (∑ k : Fin 3,
        (blochDot h
          (mixedTwoStageFrameAxis
            (localContinuousQubitFrame b theta) k)) ^ 2) =
      blochNormSq h := by
  let R := localContinuousQubitFrame b theta
  have horth : R * R.transpose = 1 := by
    exact localContinuousQubitFrame_mul_transpose_self hDomain
  have hmatrix :
      dotProduct (R.transpose.mulVec h) (R.transpose.mulVec h) =
        dotProduct h ((R * R.transpose).mulVec h) := by
    simp [Matrix.mulVec, Matrix.mul_apply, dotProduct,
      Fin.sum_univ_succ]
    ring
  rw [horth] at hmatrix
  convert hmatrix using 1 <;>
    simp [R, Matrix.mulVec, dotProduct, blochDot, blochNormSq,
      mixedTwoStageFrameAxis, qubitFrameAxis, Fin.sum_univ_succ] <;>
    ring

/-- Every nonzero physical direction has strictly positive limiting Fisher
information at an interior truth. -/
theorem mixedPolynomialTruthFrameDirectionalInformation_pos_closed
    (theta b : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    {h : Fin 3 → ℝ} (hh : h ≠ 0) :
    0 < mixedPolynomialTruthFrameDirectionalInformation theta h b := by
  have hDomain : LocalContinuousFrameDomain b theta := ⟨hTruth.1, hSeed⟩
  have hden : ∀ k : Fin 3,
      0 < 1 - (blochDot theta
        (mixedTwoStageFrameAxis
          (localContinuousQubitFrame b theta) k)) ^ 2 := by
    intro k
    have hunit :
        blochNormSq
          (mixedTwoStageFrameAxis
            (localContinuousQubitFrame b theta) k) = 1 := by
      change blochNormSq
        (qubitFrameAxis (localContinuousQubitFrame b theta) k) = 1
      exact localContinuousQubitFrame_axis_unit hDomain k
    exact mixedTwoStageAxisFisherDenominator_pos theta _ hTruth.2 hunit
  have hterm : ∀ k : Fin 3,
      (blochDot h
        (mixedTwoStageFrameAxis
          (localContinuousQubitFrame b theta) k)) ^ 2 ≤
        (blochDot h
          (mixedTwoStageFrameAxis
            (localContinuousQubitFrame b theta) k)) ^ 2 /
          (1 - (blochDot theta
            (mixedTwoStageFrameAxis
              (localContinuousQubitFrame b theta) k)) ^ 2) := by
    intro k
    rw [le_div_iff₀ (hden k)]
    nlinarith [sq_nonneg (blochDot h
      (mixedTwoStageFrameAxis
        (localContinuousQubitFrame b theta) k)),
      sq_nonneg (blochDot theta
        (mixedTwoStageFrameAxis
          (localContinuousQubitFrame b theta) k))]
  have hsum := Finset.sum_le_sum fun k (_hk : k ∈ Finset.univ) => hterm k
  have hparseval := mixedPolynomialTruthFrame_parseval theta h b hDomain
  have hnorm_nonnegative : 0 ≤ blochNormSq h := by
    unfold blochNormSq
    positivity
  have hnorm_ne : blochNormSq h ≠ 0 := by
    intro hzero
    apply hh
    funext i
    fin_cases i <;>
      simp [blochNormSq, Fin.sum_univ_succ] at hzero ⊢ <;>
      nlinarith [sq_nonneg (h 0), sq_nonneg (h 1), sq_nonneg (h 2)]
  have hnorm_pos : 0 < blochNormSq h :=
    lt_of_le_of_ne hnorm_nonnegative (Ne.symm hnorm_ne)
  unfold mixedPolynomialTruthFrameDirectionalInformation
    mixedPolynomialFrameDirectionalInformation
  calc
    0 < (1 / 3 : ℝ) * blochNormSq h := mul_pos (by norm_num) hnorm_pos
    _ = (1 / 3 : ℝ) * ∑ k : Fin 3,
        (blochDot h
          (mixedTwoStageFrameAxis
            (localContinuousQubitFrame b theta) k)) ^ 2 := by
          rw [hparseval]
    _ ≤ (1 / 3 : ℝ) * ∑ k : Fin 3,
        (blochDot h
          (mixedTwoStageFrameAxis
            (localContinuousQubitFrame b theta) k)) ^ 2 /
          (1 - (blochDot theta
            (mixedTwoStageFrameAxis
              (localContinuousQubitFrame b theta) k)) ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)

/-- The explicit concrete truth-frame Fisher matrix is positive definite. -/
theorem mixedPolynomialTruthFrameInformationMatrix_posDef
    (theta b : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    (mixedPolynomialTruthFrameInformationMatrix theta b).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · rw [Matrix.isHermitian_iff_isSymm]
    exact mixedPolynomialTruthFrameInformationMatrix_transpose theta b
  · intro h hh
    simp only [star_trivial]
    rw [mixedPolynomialTruthFrameInformationMatrix_quadratic]
    exact mixedPolynomialTruthFrameDirectionalInformation_pos_closed
      theta b hTruth hSeed hh

end

end QubitOracle.Paper
