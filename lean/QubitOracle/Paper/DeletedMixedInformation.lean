import QubitOracle.Paper.RetainedTailSet
import QubitOracle.Paper.MixedInformationBound
import Mathlib.Analysis.Matrix.Normed

noncomputable section

namespace QubitOracle.Paper

open scoped BigOperators

local instance : NormedAddCommGroup OracleMatrix :=
  Matrix.frobeniusNormedAddCommGroup

local instance : NormedSpace ℝ OracleMatrix :=
  Matrix.frobeniusNormedSpace

local instance : NormSMulClass ℝ OracleMatrix :=
  Matrix.frobeniusNormSMulClass

/-- The default finite-matrix norm is bounded by the Frobenius norm used for
the paper's shotwise information bound. -/
theorem oracleMatrix_norm_le_mixedInformationFrobeniusNorm
    (M : OracleMatrix) :
    ‖M‖ ≤ mixedInformationFrobeniusNorm M := by
  rw [Matrix.frobenius_norm_def, mixedInformationFrobeniusNorm,
    frobeniusSq, frobeniusInner, Real.sqrt_eq_rpow]
  simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs]
  simp only [pow_two]
  exact le_rfl

/-- Every unit-axis mixed-qubit Fisher increment obeys the same bound in the
default matrix norm. -/
theorem mixedAxisFisher_norm_le_interiorInverse
    (theta axis : Fin 3 → ℝ)
    (hinterior : QubitOracle.blochNormSq theta < 1)
    (haxis : QubitOracle.blochNormSq axis = 1) :
    ‖QubitOracle.mixedAxisFisher theta axis‖ ≤
      (1 - QubitOracle.blochNormSq theta)⁻¹ :=
  (oracleMatrix_norm_le_mixedInformationFrobeniusNorm
    (QubitOracle.mixedAxisFisher theta axis)).trans
      (mixedAxisInformationFrobeniusNorm_le theta axis hinterior haxis)

/-- Triangle-bound a finite deleted collection of mixed-qubit information
increments by its cardinality. -/
theorem mixedDeletedInformation_sum_norm_le
    (theta : Fin 3 → ℝ)
    (hinterior : QubitOracle.blochNormSq theta < 1)
    (axis : ℕ → Fin 3 → ℝ)
    (haxis : ∀ i, QubitOracle.blochNormSq (axis i) = 1)
    (deleted : Finset ℕ) :
    ‖∑ i ∈ deleted, QubitOracle.mixedAxisFisher theta (axis i)‖ ≤
      (deleted.card : ℝ) *
        (1 - QubitOracle.blochNormSq theta)⁻¹ := by
  calc
    ‖∑ i ∈ deleted, QubitOracle.mixedAxisFisher theta (axis i)‖ ≤
        ∑ i ∈ deleted, ‖QubitOracle.mixedAxisFisher theta (axis i)‖ :=
      norm_sum_le deleted fun i => QubitOracle.mixedAxisFisher theta (axis i)
    _ ≤ ∑ _i ∈ deleted,
        (1 - QubitOracle.blochNormSq theta)⁻¹ := by
      exact Finset.sum_le_sum fun i _ =>
        mixedAxisFisher_norm_le_interiorInverse
          theta (axis i) hinterior (haxis i)
    _ = (deleted.card : ℝ) *
        (1 - QubitOracle.blochNormSq theta)⁻¹ := by simp

namespace Label

/-- `eq:SI_delete_mixed`: once the deleted index count is at most burn-in plus
the number of exploration flags, the paper's deterministic mixed-information
deletion bound follows. -/
theorem eq_SI_delete_mixed_of_card_bound
    (theta : Fin 3 → ℝ)
    (hinterior : QubitOracle.blochNormSq theta < 1)
    (axis : ℕ → Fin 3 → ℝ)
    (haxis : ∀ i, QubitOracle.blochNormSq (axis i) = 1)
    (n qn explorationCount : ℕ) (hn : 0 < n)
    (deleted : Finset ℕ)
    (hdeleted : deleted.card ≤ qn + explorationCount) :
    ‖(n : ℝ)⁻¹ •
        ∑ i ∈ deleted, QubitOracle.mixedAxisFisher theta (axis i)‖ ≤
      ((qn + explorationCount : ℕ) : ℝ) /
        ((n : ℝ) * (1 - QubitOracle.blochNormSq theta)) := by
  have hdelta : 0 < 1 - QubitOracle.blochNormSq theta :=
    sub_pos.mpr hinterior
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcard : (deleted.card : ℝ) ≤ ((qn + explorationCount : ℕ) : ℝ) := by
    exact_mod_cast hdeleted
  have hinvN : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr hnreal.le
  have hinvDelta :
      0 ≤ (1 - QubitOracle.blochNormSq theta)⁻¹ :=
    inv_nonneg.mpr hdelta.le
  calc
    ‖(n : ℝ)⁻¹ •
        ∑ i ∈ deleted, QubitOracle.mixedAxisFisher theta (axis i)‖ =
        (n : ℝ)⁻¹ *
          ‖∑ i ∈ deleted, QubitOracle.mixedAxisFisher theta (axis i)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hinvN]
    _ ≤ (n : ℝ)⁻¹ *
        ((deleted.card : ℝ) *
          (1 - QubitOracle.blochNormSq theta)⁻¹) :=
      mul_le_mul_of_nonneg_left
        (mixedDeletedInformation_sum_norm_le
          theta hinterior axis haxis deleted) hinvN
    _ ≤ (n : ℝ)⁻¹ *
        (((qn + explorationCount : ℕ) : ℝ) *
          (1 - QubitOracle.blochNormSq theta)⁻¹) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hcard hinvDelta) hinvN
    _ = ((qn + explorationCount : ℕ) : ℝ) /
        ((n : ℝ) * (1 - QubitOracle.blochNormSq theta)) := by
      field_simp [ne_of_gt hnreal, ne_of_gt hdelta] <;> ring

end Label

end QubitOracle.Paper
