import QubitOracle.Paper.EmpiricalCovariance
import QubitOracle.AdaptiveDesign.WeakMeanLossTransfer

/-! The prose deduction from Gaussian limits and fourth moments to
population covariance limits. The theorem derives both first and second
moments; weak convergence alone is never used to assert a covariance limit. -/
namespace QubitOracle.Paper.EmpiricalCovariance
open MeasureTheory ProbabilityTheory Filter
open QubitOracle.AdaptiveDesign AdaptiveResponseMoments
open scoped Topology BigOperators
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem squared_mean_tendsto (X : ℕ → Ω → ℝ) (Z : Ω' → ℝ)
    (hw : TendstoInDistribution X atTop Z (fun _ => μ) ν)
    (h4 : UniformMoment μ X 4) (hZ : MemLp Z 4 ν) :
    Tendsto (fun n => ∫ ω,(X n ω)^2 ∂μ) atTop (𝓝 (∫ ω,(Z ω)^2 ∂ν)) := by
  have hm := h4.norm_sq_of_four
  obtain ⟨K,hK,hKm⟩ := hm
  norm_num only [Nat.cast_ofNat] at hKm
  have hZ2 : MemLp (fun ω => (Z ω)^2) 2 ν := by
    have ht := hZ.norm_rpow_div 2
    norm_num at ht
    have hdiv : (4:ENNReal)/2=2 := by
      symm
      apply (ENNReal.eq_div_iff (by norm_num) (by simp)).mpr
      norm_num
    rw [hdiv] at ht
    simpa only [Real.norm_eq_abs,sq_abs] using ht
  exact WeakMeanLossTransfer.mean_tendsto_of_weak_and_secondMoment _ _
    (hw.continuous_comp (g:=fun x : ℝ => x^2) (by fun_prop))
    (fun n => by simpa only [Real.norm_eq_abs,sq_abs] using (hKm n).1) hZ2
    (fun _ => Eventually.of_forall (fun _ => sq_nonneg _))
    (Eventually.of_forall (fun _ => sq_nonneg _)) K hK
    (fun n => by simpa only [Real.norm_eq_abs,sq_abs] using (hKm n).2)

theorem square_shift_integral (X : Ω → ℝ) (hX : MemLp X 4 μ) :
    (∫ ω,(X ω+1)^2 ∂μ) = (∫ ω,(X ω)^2 ∂μ)+2*(∫ ω,X ω ∂μ)+1 := by
  have hX2 := hX.mono_exponent (by norm_num : (2:ENNReal) ≤ 4)
  have hXi := hX.integrable (by norm_num : (1:ENNReal) ≤ 4)
  simp_rw [show ∀ x : ℝ,(x+1)^2=x^2+2*x+1 by intro x; ring]
  rw [integral_add (show Integrable (fun ω => (X ω)^2+2*X ω) μ from
      hX2.integrable_sq.add (hXi.const_mul 2)) (integrable_const 1),
    integral_add hX2.integrable_sq (hXi.const_mul 2),integral_const_mul]
  simp

theorem first_mean_tendsto (X : ℕ → Ω → ℝ) (Z : Ω' → ℝ)
    (hw : TendstoInDistribution X atTop Z (fun _ => μ) ν)
    (h4 : UniformMoment μ X 4) (hZ : MemLp Z 4 ν) :
    Tendsto (fun n => ∫ ω,X n ω ∂μ) atTop (𝓝 (∫ ω,Z ω ∂ν)) := by
  have hc : UniformMoment μ (fun (_ : ℕ) (_ : Ω) => (1:ℝ)) 4 :=
    uniformMoment_of_bound _ (fun _ => aestronglyMeasurable_const) 1 (by norm_num)
      (fun _ _ => by simp) 4
  have ht := squared_mean_tendsto (fun n ω => X n ω+1) (fun ω => Z ω+1)
    (hw.continuous_comp (g:=fun x : ℝ => x+1) (by fun_prop)) (h4.add hc)
    (hZ.add (memLp_const _))
  have hs := squared_mean_tendsto X Z hw h4 hZ
  have hXm (n : ℕ) := ((Classical.choose_spec h4).2 n).1
  simp_rw [square_shift_integral _ (hXm _)] at ht
  rw [square_shift_integral _ hZ] at ht
  have hh := ((ht.sub hs).sub_const 1).div_const 2
  convert hh using 1 <;>
    first | (funext n; ring) | ring

theorem product_integral_polarization (X Y : Ω → ℝ) (hX : MemLp X 2 μ)
    (hY : MemLp Y 2 μ) :
    (∫ ω,X ω*Y ω ∂μ) =
      ((∫ ω,(X ω+Y ω)^2 ∂μ)-(∫ ω,(X ω)^2 ∂μ)-(∫ ω,(Y ω)^2 ∂μ))/2 := by
  simp_rw [show ∀ x y : ℝ,(x+y)^2=x^2+2*(x*y)+y^2 by intro x y; ring]
  rw [integral_add (show Integrable (fun ω => (X ω)^2+2*(X ω*Y ω)) μ from
      hX.integrable_sq.add ((hX.integrable_mul hY).const_mul 2))
    hY.integrable_sq,integral_add hX.integrable_sq
      (show Integrable (fun ω => 2*(X ω*Y ω)) μ from (hX.integrable_mul hY).const_mul 2),
    integral_const_mul]
  ring

theorem covariance_matrix_tendsto {ι : Type*} [Fintype ι]
    (X : ℕ → Ω → EuclideanSpace ℝ ι) (Z : Ω' → EuclideanSpace ℝ ι)
    (hw : TendstoInDistribution X atTop Z (fun _ => μ) ν)
    (h4 : UniformMoment μ X 4) (hZ : MemLp Z 4 ν) :
    Tendsto (fun n => covarianceMatrix (μ:=μ) (X n)) atTop
      (𝓝 (covarianceMatrix (μ:=ν) Z)) := by
  have hXm (n : ℕ) := ((Classical.choose_spec h4).2 n).1
  have hXi (i : ι) : UniformMoment μ (fun n ω => X n ω i) 4 :=
    h4.of_dominated _ (fun n => (EuclideanSpace.proj i).continuous.comp_aestronglyMeasurable (hXm n).1)
      1 (by norm_num) (fun n ω => by simpa using PiLp.norm_apply_le (X n ω) i)
  have hZi (i : ι) : MemLp (fun ω => Z ω i) 4 ν :=
    hZ.of_le ((EuclideanSpace.proj i).continuous.comp_aestronglyMeasurable hZ.1)
      (Eventually.of_forall (fun ω => PiLp.norm_apply_le (Z ω) i))
  have hwi (i : ι) := hw.continuous_comp
    (g:=fun x : EuclideanSpace ℝ ι => x i) (by fun_prop)
  have hi (i : ι) := first_mean_tendsto _ _ (hwi i) (hXi i) (hZi i)
  have hs (i : ι) := squared_mean_tendsto _ _ (hwi i) (hXi i) (hZi i)
  change Tendsto (fun n i j => covariance (fun ω => X n ω i) (fun ω => X n ω j) μ)
    atTop (𝓝 (fun i j => covariance (fun ω => Z ω i) (fun ω => Z ω j) ν))
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have hij := squared_mean_tendsto (fun n ω => X n ω i+X n ω j)
    (fun ω => Z ω i+Z ω j)
    (hw.continuous_comp (g:=fun x : EuclideanSpace ℝ ι => x i+x j) (by fun_prop))
    ((hXi i).add (hXi j)) ((hZi i).add (hZi j))
  have hp := ((hij.sub (hs i)).sub (hs j)).div_const 2
  have hXm2 (k : ι) (n : ℕ) : MemLp (fun ω => X n ω k) 2 μ :=
    (((Classical.choose_spec (hXi k)).2 n).1).mono_exponent (by norm_num)
  have hZm2 (k : ι) : MemLp (fun ω => Z ω k) 2 ν :=
    (hZi k).mono_exponent (by norm_num)
  have hprod : Tendsto (fun n => ∫ ω,X n ω i*X n ω j ∂μ) atTop
      (𝓝 (∫ ω,Z ω i*Z ω j ∂ν)) := by
    convert hp using 1
    · funext n
      exact product_integral_polarization _ _ (hXm2 i n) (hXm2 j n)
    · exact congrArg (fun x : ℝ => 𝓝 x)
        (product_integral_polarization _ _ (hZm2 i) (hZm2 j))
  have ht := hprod.sub ((hi i).mul (hi j))
  convert ht using 1
  · funext n
    rw [covariance_eq_sub (hXm2 i n) (hXm2 j n)]
    rfl
  · rw [covariance_eq_sub (hZm2 i) (hZm2 j)]
    rfl

end
end QubitOracle.Paper.EmpiricalCovariance
