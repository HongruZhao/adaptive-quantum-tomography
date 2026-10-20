import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import QubitOracle.AdaptiveDesign.BoundedMartingaleSecondMoment
import QubitOracle.AdaptiveDesign.BoundedVarianceMGF
/-! The sharp bounded-increment exponential bound on arbitrary probability
spaces. Convexity of the exponential and conditional centering replace any
regular-conditional-distribution assumption. -/
namespace QubitOracle.AdaptiveDesign.BoundedMartingaleHoeffding
open MeasureTheory ProbabilityTheory Filter BoundedMartingaleSecondMoment BoundedVarianceMGF
open scoped BigOperators Topology ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem exp_chord (C : ℝ) (hC : 0 < C) (x t : ℝ) (hx : |x| ≤ C) :
    Real.exp (t*x) ≤ Real.cosh (t*C)+(Real.sinh (t*C)/C)*x := by
  have hsmall : |x/C| ≤ 1 := by
    rw [abs_div,abs_of_pos hC]
    exact (div_le_one hC).mpr hx
  have h := Real.exp_mul_le_cosh_add_mul_sinh hsmall (t*C)
  convert h using 1 <;> congr 1 <;> field_simp <;> ring

theorem mgf_partialSum_le
    (F : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hc : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
    (C : ℝ) (hC : 0 < C) (hb : ∀ n ω, ‖X n ω‖ ≤ C) (t : ℝ) (n : ℕ) :
    (∫ ω, Real.exp (t*partialSum X n ω) ∂μ) ≤ Real.exp ((n:ℝ)*C^2*t^2/2) := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
    let S := partialSum X n
    let W := fun ω => Real.exp (t*S ω)
    let D := Real.sinh (t*C)/C
    have hS : StronglyMeasurable[F n] S := partialSum_adapted F X ha n
    have hSbound (ω : Ω) : ‖S ω‖ ≤ (n:ℝ)*C := by
      simpa using partialSum_bound X (fun _ => C) hb n ω
    have hW : MemLp W 2 μ := exp_memLp S (hS.mono (F.le n)).aestronglyMeasurable _ hSbound t 2
    have hWmeas : StronglyMeasurable[F n] W :=
      Real.continuous_exp.comp_stronglyMeasurable (hS.const_mul t)
    have hX : MemLp (X n) 2 μ := MemLp.of_bound
      ((ha n).mono (F.le (n+1))).aestronglyMeasurable C (Eventually.of_forall (hb n))
    have hiW := hW.integrable (by norm_num : (1:ENNReal) ≤ 2)
    have hiX := hX.integrable (by norm_num : (1:ENNReal) ≤ 2)
    have hiz : ∫ ω, W ω*X n ω ∂μ = 0 := by
      rw [weighted_conditional_integral (F.le n) W (X n) hWmeas (hW.integrable_mul hX) hiX]
      have hh : (fun ω => W ω*μ[X n | F n] ω) =ᵐ[μ] 0 := by
        filter_upwards [hc n] with ω hω
        simp only [hω, Pi.zero_apply, mul_zero]
      rw [integral_congr_ae hh]
      simp
    have hpoint (ω : Ω) : Real.exp (t*partialSum X (n+1) ω) ≤
        Real.cosh (t*C)*W ω+D*(W ω*X n ω) := by
      have he := exp_chord C hC (X n ω) t (hb n ω)
      have hh := mul_le_mul_of_nonneg_left he (Real.exp_pos (t*S ω)).le
      rw [partialSum_succ]
      simp only [Pi.add_apply,mul_add,Real.exp_add]
      change Real.exp (t*S ω)*Real.exp (t*X n ω) ≤ _
      dsimp only [W,D] at *
      nlinarith
    calc
      _ ≤ ∫ ω, Real.cosh (t*C)*W ω+D*(W ω*X n ω) ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall (fun _ => (Real.exp_pos _).le))
          ((hiW.const_mul _).add ((hW.integrable_mul hX).const_mul D))
          (Eventually.of_forall hpoint)
      _ = Real.cosh (t*C)*(∫ ω, W ω ∂μ) := by
        rw [integral_add (f:=fun ω => Real.cosh (t*C)*W ω)
          (g:=fun ω => D*(W ω*X n ω)) (hiW.const_mul _)
          ((hW.integrable_mul hX).const_mul D), integral_const_mul, integral_const_mul, hiz]
        ring
      _ ≤ Real.exp ((t*C)^2/2)*(∫ ω, W ω ∂μ) :=
        mul_le_mul_of_nonneg_right (Real.cosh_le_exp_half_sq _)
          (integral_nonneg (fun _ => (Real.exp_pos _).le))
      _ ≤ Real.exp ((t*C)^2/2)*Real.exp ((n:ℝ)*C^2*t^2/2) :=
        mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; push_cast; ring

theorem partialSum_subGaussian
    (F : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hc : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
    (C : ℝ) (hC : 0 < C) (hb : ∀ n ω, ‖X n ω‖ ≤ C) (n : ℕ) :
    HasSubgaussianMGF (partialSum X n) ⟨(n:ℝ)*C^2, by positivity⟩ μ where
  integrable_exp_mul t := by
    apply (exp_memLp _ ((partialSum_adapted F X ha n).mono (F.le n)).aestronglyMeasurable
      ((n:ℝ)*C) (fun ω => by simpa using partialSum_bound X (fun _ => C) hb n ω) t 1).integrable
    rfl
  mgf_le t := mgf_partialSum_le F X ha hc C hC hb t n

end
end QubitOracle.AdaptiveDesign.BoundedMartingaleHoeffding
