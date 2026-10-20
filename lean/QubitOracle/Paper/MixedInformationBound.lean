import QubitOracle.Paper.MixedAxisFisher
import QubitOracle.Paper.MixedOracleMatrix

/-!
# Uniform information bound for an interior mixed qubit

This module proves the model-specific boundedness input used by the
information-martingale strong law. The norm is the Frobenius norm already
used by the paper's oracle matrix layer.
-/

namespace QubitOracle
namespace Paper

open scoped BigOperators

noncomputable section

theorem frobeniusSq_smul_blochOuter
    (c : Real) (u : Fin 3 -> Real) :
    frobeniusSq (c • blochOuter u) =
      c ^ 2 * (blochNormSq u) ^ 2 := by
  unfold frobeniusSq frobeniusInner
  simp only [Matrix.smul_apply, smul_eq_mul, blochOuter]
  unfold blochNormSq
  calc
    ∑ i, ∑ j, (c * (u i * u j)) * (c * (u i * u j)) =
        ∑ i, ∑ j, c ^ 2 * (u i) ^ 2 * (u j) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i, (c ^ 2 * (u i) ^ 2) * ∑ j, (u j) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ = (∑ i, c ^ 2 * (u i) ^ 2) * ∑ j, (u j) ^ 2 := by
      rw [← Finset.sum_mul]
    _ = (c ^ 2 * ∑ i, (u i) ^ 2) * ∑ j, (u j) ^ 2 := by
      have hfactor :
          (∑ i, c ^ 2 * (u i) ^ 2) = c ^ 2 * ∑ i, (u i) ^ 2 := by
        rw [Finset.mul_sum]
      rw [hfactor]
    _ = c ^ 2 * (∑ i, (u i) ^ 2) ^ 2 := by ring

theorem mixedAxisFisher_frobeniusSq_eq
    (r u : Fin 3 -> Real) (hu : blochNormSq u = 1) :
    frobeniusSq (mixedAxisFisher r u) =
      (1 - (blochDot r u) ^ 2)⁻¹ ^ 2 := by
  rw [mixedAxisFisher, frobeniusSq_smul_blochOuter, hu]
  ring

/-- Frobenius norm of an information matrix. -/
noncomputable def mixedInformationFrobeniusNorm
    (M : OracleMatrix) : Real :=
  Real.sqrt (frobeniusSq M)

theorem mixedAxisFisher_frobeniusNorm_eq
    (r u : Fin 3 -> Real) (hr : blochNormSq r < 1)
    (hu : blochNormSq u = 1) :
    mixedInformationFrobeniusNorm (mixedAxisFisher r u) =
      (1 - (blochDot r u) ^ 2)⁻¹ := by
  have hden := mixedAxisFisher_denominator_pos r u hr hu
  rw [mixedInformationFrobeniusNorm,
    mixedAxisFisher_frobeniusSq_eq r u hu]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos (inv_pos.mpr hden)]

/-- The manuscript's uniform one-shot information bound at an interior
mixed-qubit truth. -/
theorem mixedAxisInformationFrobeniusNorm_le
    (r u : Fin 3 -> Real) (hr : blochNormSq r < 1)
    (hu : blochNormSq u = 1) :
    mixedInformationFrobeniusNorm (mixedAxisFisher r u) <=
      (1 - blochNormSq r)⁻¹ := by
  have hgap : 0 < 1 - blochNormSq r := by linarith
  have hden := mixedAxisFisher_denominator_pos r u hr hu
  have hdot : (blochDot r u) ^ 2 <= blochNormSq r := by
    calc
      (blochDot r u) ^ 2 <= blochNormSq r * blochNormSq u :=
        bloch_cauchy_schwarz r u
      _ = blochNormSq r := by rw [hu, mul_one]
  have hden_ge :
      1 - blochNormSq r <= 1 - (blochDot r u) ^ 2 := by
    linarith
  rw [mixedAxisFisher_frobeniusNorm_eq r u hr hu]
  simpa [one_div] using one_div_le_one_div_of_le hgap hden_ge

end

end Paper
end QubitOracle
