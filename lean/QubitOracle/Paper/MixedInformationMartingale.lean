import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.MixedAxisFisher
import QubitOracle.Paper.MixedInformationBound
import QubitOracle.Paper.MixedOracleGeometry
import QubitOracle.Paper.MixedOracleMatrix
/-! Supporting definitions and proved lemmas used by the manuscript. -/

namespace QubitOracle.Paper

open Filter MeasureTheory
open scoped BigOperators

noncomputable section

theorem matrix_entry_sq_le_frobeniusSq
    (M : OracleMatrix) (i j : Fin 3) :
    (M i j) ^ 2 ≤ frobeniusSq M := by
  unfold frobeniusSq frobeniusInner
  have hrow : M i j * M i j ≤ ∑ k, M i k * M i k :=
    Finset.single_le_sum
      (fun k _ => mul_self_nonneg (M i k)) (Finset.mem_univ j)
  have hall : (∑ k, M i k * M i k) ≤
      ∑ r, ∑ k, M r k * M r k :=
    Finset.single_le_sum
      (fun r _ => Finset.sum_nonneg fun k _ => mul_self_nonneg (M r k))
      (Finset.mem_univ i)
  simpa [pow_two] using hrow.trans hall

theorem abs_matrix_entry_le_frobeniusNorm
    (M : OracleMatrix) (i j : Fin 3) :
    |M i j| ≤ mixedInformationFrobeniusNorm M := by
  unfold mixedInformationFrobeniusNorm
  apply (Real.le_sqrt (abs_nonneg _) (frobeniusSq_nonneg M)).2
  simpa [sq_abs] using matrix_entry_sq_le_frobeniusSq M i j

theorem mixedAxisInformation_entry_norm_le
    (r u : Fin 3 → ℝ)
    (hr : QubitOracle.blochNormSq r < 1)
    (hu : QubitOracle.blochNormSq u = 1)
    (i j : Fin 3) :
    ‖QubitOracle.mixedAxisFisher r u i j‖ ≤
      (1 - QubitOracle.blochNormSq r)⁻¹ := by
  rw [Real.norm_eq_abs]
  exact (abs_matrix_entry_le_frobeniusNorm
    (QubitOracle.mixedAxisFisher r u) i j).trans
      (mixedAxisInformationFrobeniusNorm_le r u hr hu)







end

end QubitOracle.Paper
