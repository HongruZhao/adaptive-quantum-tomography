import QubitOracle.AdaptiveDesign.P1WeightedEndpoints
import QubitOracle.AdaptiveDesign.P1ObservedRidge
import QubitOracle.AdaptiveDesign.P1WeightedBorn
import QubitOracle.FiniteGillMassar
/-! Actual Gaussian quadratic integrals, rather than a formal name for
the covariance contraction. -/
namespace QubitOracle.AdaptiveDesign.P1Weighted
open QubitOracle QubitOracle.Paper MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem quadratic_continuous (W : Mat) : Continuous (fun z : Vector => quadratic W z.ofLp) := by
  unfold quadratic Matrix.mulVec dotProduct
  fun_prop

theorem gaussian_quadratic_memLp (W S : Mat) :
    MemLp (fun z : Vector => quadratic W z.ofLp) 2 (multivariateGaussian 0 S) := by
  have h := (IsGaussian.memLp_id (multivariateGaussian (0:Vector) S) 4 (by simp)).norm_rpow_div 2
  norm_num at h
  have hdiv : (4:ENNReal)/2=2 := by
    symm
    apply (ENNReal.eq_div_iff (by norm_num) (by simp)).mpr
    norm_num
  rw [hdiv] at h
  apply h.of_le_mul (quadratic_continuous W).aestronglyMeasurable (c:=entrySize W)
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_of_nonneg (sq_nonneg ‖z‖)]
  simpa only [Real.norm_eq_abs,EuclideanSpace.real_norm_sq_eq,blochNormSq]
    using quadratic_abs_le W z.ofLp

theorem gaussian_quadratic_mean (W S : Mat) (hS : S.PosSemidef) :
    ∫ z : Vector, quadratic W z.ofLp ∂multivariateGaussian 0 S = (W*S).trace := by
  let μ := multivariateGaussian (0:Vector) S
  have hcoord (i : Fin 3) : MemLp (fun z : Vector => z i) 2 μ := by
    simpa [PiLp.inner_apply] using
      (IsGaussian.memLp_two_id (μ:=μ)).const_inner (𝕜:=ℝ) (EuclideanSpace.basisFun (Fin 3) ℝ i)
  have hmean (i : Fin 3) : ∫ z : Vector, z i ∂μ = 0 := by
    have h := integral_inner (𝕜:=ℝ) (μ:=μ) (IsGaussian.integrable_fun_id (μ:=μ))
      (EuclideanSpace.basisFun (Fin 3) ℝ i)
    simpa [PiLp.inner_apply,μ] using h
  have hprod (i j : Fin 3) : ∫ z : Vector, z i*z j ∂μ = S i j := by
    have h := covariance_eval_multivariateGaussian (μ:=(0:Vector)) hS i j
    rw [covariance_eq_sub (hcoord i) (hcoord j),hmean i,hmean j] at h
    simpa only [zero_mul,sub_zero,Pi.mul_apply] using h
  have he (z : Vector) : quadratic W z.ofLp = ∑ i : Fin 3, ∑ j : Fin 3, W i j*(z j*z i) := by
    simp only [quadratic,Matrix.mulVec,dotProduct,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  have hterm (i j : Fin 3) : Integrable (fun z : Vector => W i j*(z j*z i)) μ := by
    simpa only [Pi.mul_apply] using ((hcoord j).integrable_mul (hcoord i)).const_mul (W i j)
  have hrows (i : Fin 3) : Integrable (fun z : Vector => ∑ j, W i j*(z j*z i)) μ :=
    integrable_finsetSum Finset.univ (fun j _ => hterm i j)
  change (∫ z : Vector, ∑ i, ∑ j, W i j*(z j*z i) ∂μ) = _
  rw [integral_finsetSum Finset.univ (fun i _ => hrows i)]
  simp only [Matrix.trace,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ => hterm i j)]
  change _ = ∑ j, W i j*S j i
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul,hprod]

end
end QubitOracle.AdaptiveDesign.P1Weighted
