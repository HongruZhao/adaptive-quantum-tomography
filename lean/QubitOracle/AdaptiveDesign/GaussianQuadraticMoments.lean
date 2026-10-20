import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! The mean and square integrability of the chi-square representation
used by the paper's physical-loss limits. -/
namespace QubitOracle.AdaptiveDesign.GaussianQuadraticMoments
open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem norm_sq_memLp : MemLp (fun z : E => ‖z‖^2) 2 (stdGaussian E) := by
  have ht := (IsGaussian.memLp_id (stdGaussian E) 4 (by simp)).norm_rpow_div 2
  norm_num at ht
  have hdiv : (4:ENNReal)/2 = 2 := by
    symm
    apply (ENNReal.eq_div_iff (by norm_num) (by simp)).mpr
    norm_num
  rw [hdiv] at ht
  exact ht

theorem integral_norm_sq : ∫ z : E, ‖z‖^2 ∂stdGaussian E = (Module.finrank ℝ E:ℝ) := by
  let b := stdOrthonormalBasis ℝ E
  have he (i : Fin (Module.finrank ℝ E)) :
      ∫ z : E, ⟪b i,z⟫_ℝ^2 ∂stdGaussian E = 1 := by
    have h := covarianceBilin_apply (μ := stdGaussian E) IsGaussian.memLp_two_id (b i) (b i)
    simp only [id_eq] at h
    rw [covarianceBilin_stdGaussian, innerSL_apply_apply, integral_id_stdGaussian] at h
    simpa only [sub_zero, ← pow_two, real_inner_self_eq_norm_sq, b.norm_eq_one, one_pow] using h.symm
  have hp (z : E) : ‖z‖^2 = ∑ i, ⟪b i,z⟫_ℝ^2 := (b.sum_sq_inner_right z).symm
  simp_rw [hp]
  rw [integral_finsetSum]
  · simp [he]
  · intro i _
    exact (IsGaussian.memLp_two_id (μ:=stdGaussian E) |>.const_inner (b i)).integrable_sq

end
end QubitOracle.AdaptiveDesign.GaussianQuadraticMoments
