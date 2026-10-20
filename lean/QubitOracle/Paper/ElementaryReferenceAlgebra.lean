import QubitOracle.Paper.ProjectiveStateGeometry
import QubitOracle.Paper.PureStateFoundations
/-! Explicit projector identities and fixed reflection from Appendix S4.1.
These identities are independent of the adaptive statistical proof.
-/
namespace QubitOracle.Paper.ElementaryReferenceAlgebra
open QubitOracle.Paper ProjectiveStateGeometry
open scoped BigOperators ComplexOrder
noncomputable section
set_option maxHeartbeats 1200000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def balanced (u v : ι → ℂ) : ι → ℂ := (Real.sqrt 2 : ℂ)⁻¹ • (u+v)

theorem balanced_density (u v : ι → ℂ) :
    rankOneDensity (balanced u v) = (1/2 : ℂ) • rankOneDensity (u+v) := by
  rw [balanced, density_smul]
  congr 1
  simp only [map_inv₀, Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

theorem real_pair_difference (u v : ι → ℂ) :
    rankOneDensity (balanced u v) - rankOneDensity (balanced u (-v)) =
      Matrix.vecMulVec u (star v) + Matrix.vecMulVec v (star u) := by
  rw [balanced_density, balanced_density]
  ext i j
  simp only [rankOneDensity, Pi.add_apply, Pi.neg_apply, star_add, star_neg,
    Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.add_apply, Matrix.vecMulVec_apply,
    Pi.star_apply]
  ring

theorem imaginary_pair_difference (u v : ι → ℂ) :
    rankOneDensity (balanced u (Complex.I • v)) -
      rankOneDensity (balanced u (-(Complex.I • v))) =
      Complex.I • (Matrix.vecMulVec v (star u) - Matrix.vecMulVec u (star v)) := by
  rw [balanced_density, balanced_density]
  ext i j
  simp only [rankOneDensity, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
    star_add, star_neg, star_mul, Complex.star_def, Complex.conj_I,
    Matrix.smul_apply, Matrix.sub_apply, Matrix.vecMulVec_apply, Pi.star_apply]
  ring

theorem pair_projectors_sum (u v : ι → ℂ) (q : ℂ) (hq : Complex.normSq q = 1) :
    rankOneDensity (balanced u (q • v)) + rankOneDensity (balanced u (-(q • v))) =
      rankOneDensity u + rankOneDensity v := by
  have hqs : star q * q = 1 := by
    simpa only [Complex.normSq_eq_conj_mul_self, Complex.ofReal_one, Complex.star_def] using congrArg Complex.ofReal hq
  rw [balanced_density, balanced_density]
  ext i j
  simp only [rankOneDensity, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
    star_add, star_neg, star_mul, Matrix.smul_apply, Matrix.add_apply]
  linear_combination v i * star (v j) * hqs

def reflection (u : ι → ℂ) : Matrix ι ι ℂ :=
  1 - (2 / (pureStateNormSq u : ℂ)) • rankOneDensity u

theorem reflection_selfadjoint (u : ι → ℂ) : (reflection u).conjTranspose = reflection u := by
  simp only [reflection, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    Matrix.conjTranspose_smul, star_div₀, star_ofNat, Complex.star_def, Complex.conj_ofReal]
  congr 1
  ext i j
  simp [rankOneDensity, Matrix.conjTranspose_apply, mul_comm]

theorem reflection_square (u : ι → ℂ) (hu : u ≠ 0) : reflection u * reflection u = 1 := by
  have hn : (pureStateNormSq u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (normSq_positive u hu))
  simp only [reflection, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_smul, Matrix.smul_mul, smul_smul, density_square]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem reflection_unitary (u : ι → ℂ) (hu : u ≠ 0) :
    reflection u ∈ Matrix.unitaryGroup ι ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  rw [Matrix.star_eq_conjTranspose, reflection_selfadjoint, reflection_square u hu]

theorem pair_count (D : ℕ) :
    (Finset.univ.filter (fun p : Fin D × Fin D => p.1 < p.2)).card = D.choose 2 := by
  simpa only [Finset.univ_product_univ, Finset.card_univ, Fintype.card_fin] using
    Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin D)))

end
end QubitOracle.Paper.ElementaryReferenceAlgebra
