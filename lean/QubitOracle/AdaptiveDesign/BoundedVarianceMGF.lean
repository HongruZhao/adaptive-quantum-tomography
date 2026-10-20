import QubitOracle.AdaptiveDesign.L2MartingaleBudget
import Mathlib.Analysis.Complex.Exponential
import QubitOracle.AdaptiveDesign.AdaptiveResponseMoments
import QubitOracle.AdaptiveDesign.BoundedMartingaleSecondMoment
import QubitOracle.AdaptiveDesign.SubGaussianPowerMoments
/-! A variance-sensitive exponential bound for bounded martingale sums.
The argument uses elementary Taylor bounds and conditional expectation;
it works on an arbitrary probability space. -/
namespace QubitOracle.AdaptiveDesign.BoundedVarianceMGF
open MeasureTheory ProbabilityTheory Filter BoundedMartingaleSecondMoment
open scoped BigOperators Topology ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem exp_bound (X : Ω → ℝ) (C : ℝ) (hb : ∀ ω, ‖X ω‖ ≤ C) (t : ℝ) (ω : Ω) :
    ‖Real.exp (t*X ω)‖ ≤ Real.exp (|t| * C) := by
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  exact (le_abs_self (t*X ω)).trans (by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hb ω) (abs_nonneg t))

theorem exp_memLp (X : Ω → ℝ) (hm : AEStronglyMeasurable X μ)
    (C : ℝ) (hb : ∀ ω, ‖X ω‖ ≤ C) (t : ℝ) (p : ENNReal) :
    MemLp (fun ω => Real.exp (t*X ω)) p μ :=
  MemLp.of_bound (Real.continuous_exp.comp_aestronglyMeasurable (hm.const_mul t)) (Real.exp (|t| * C))
    (Eventually.of_forall (exp_bound X C hb t))

theorem weighted_conditional_integral {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (W X : Ω → ℝ) (hW : StronglyMeasurable[m] W)
    (hi : Integrable (W*X) μ) (hX : Integrable X μ) :
    (∫ ω, W ω*X ω ∂μ) = ∫ ω, W ω*μ[X | m] ω ∂μ := by
  have h := condExp_mul_of_stronglyMeasurable_left hW hi hX
  calc
    _ = ∫ ω, μ[W*X | m] ω ∂μ := (integral_condExp hm).symm
    _ = _ := integral_congr_ae h

theorem mgf_partialSum_le
    (F : Filtration ℕ ‹MeasurableSpace Ω›) (X : ℕ → Ω → ℝ)
    (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hc : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n ω, ‖X n ω‖ ≤ C)
    (v : ℕ → ℝ) (hv : ∀ n, ∀ᵐ ω ∂μ, μ[fun ω => X n ω^2 | F n] ω ≤ v n)
    (t : ℝ) (ht : |t| * C ≤ 1) (n : ℕ) :
    (∫ ω, Real.exp (t*partialSum X n ω) ∂μ) ≤
      Real.exp (t^2 * ∑ k ∈ Finset.range n, v k) := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
    let S := partialSum X n
    let W := fun ω => Real.exp (t*S ω)
    have hS : StronglyMeasurable[F n] S := partialSum_adapted F X ha n
    have hWmeas : StronglyMeasurable[F n] W :=
      Real.continuous_exp.comp_stronglyMeasurable (hS.const_mul t)
    have hSbound (ω : Ω) : ‖S ω‖ ≤ (n:ℝ)*C := by
      simpa using partialSum_bound X (fun _ => C) hb n ω
    have hW : MemLp W 2 μ := exp_memLp S (hS.mono (F.le n)).aestronglyMeasurable _ hSbound t 2
    have hX : MemLp (X n) 2 μ := MemLp.of_bound
      ((ha n).mono (F.le (n+1))).aestronglyMeasurable C (Eventually.of_forall (hb n))
    have hXsq : MemLp (fun ω => X n ω^2) 2 μ := MemLp.of_bound
      (((ha n).mono (F.le (n+1))).pow 2).aestronglyMeasurable (C^2)
      (Eventually.of_forall (fun ω => by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hb n ω) 2))
    have hiW := hW.integrable (by norm_num : (1:ENNReal) ≤ 2)
    have hiX := hX.integrable (by norm_num : (1:ENNReal) ≤ 2)
    have hiXsq := hXsq.integrable (by norm_num : (1:ENNReal) ≤ 2)
    have hiz : ∫ ω, W ω*X n ω ∂μ = 0 := by
      rw [weighted_conditional_integral (F.le n) W (X n) hWmeas (hW.integrable_mul hX) hiX]
      have hh : (fun ω => W ω*μ[X n | F n] ω) =ᵐ[μ] 0 := by
        filter_upwards [hc n] with ω hω
        simp only [hω, Pi.zero_apply, mul_zero]
      rw [integral_congr_ae hh]
      simp
    have hiv : (∫ ω, W ω*X n ω^2 ∂μ) ≤ v n*(∫ ω, W ω ∂μ) := by
      have he := condExp_mul_of_stronglyMeasurable_left hWmeas
        (hW.integrable_mul hXsq) hiXsq
      have hic : Integrable (fun ω => W ω*μ[fun ω => X n ω^2 | F n] ω) μ :=
        integrable_condExp.congr he
      rw [weighted_conditional_integral (F.le n) W (fun ω => X n ω^2)
        hWmeas (hW.integrable_mul hXsq) hiXsq]
      calc
        _ ≤ ∫ ω, v n*W ω ∂μ := integral_mono_ae hic (hiW.const_mul (v n)) (by
          filter_upwards [hv n] with ω hω
          nlinarith [mul_le_mul_of_nonneg_left hω (Real.exp_pos (t*S ω)).le])
        _ = _ := integral_const_mul _ _
    have hipoly : Integrable (fun ω => W ω+t*(W ω*X n ω)+t^2*(W ω*X n ω^2)) μ :=
      (hiW.add ((hW.integrable_mul hX).const_mul t)).add ((hW.integrable_mul hXsq).const_mul (t^2))
    have hpoint (ω : Ω) : Real.exp (t*partialSum X (n+1) ω) ≤
        W ω+t*(W ω*X n ω)+t^2*(W ω*X n ω^2) := by
      have hsmall : |t*X n ω| ≤ 1 := by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left (hb n ω) (abs_nonneg t)).trans ht
      have he := Real.abs_exp_sub_one_sub_id_le hsmall
      have he' : Real.exp (t*X n ω) ≤ 1+t*X n ω+t^2*X n ω^2 := by
        nlinarith [le_abs_self (Real.exp (t*X n ω)-1-t*X n ω)]
      rw [partialSum_succ]
      simp only [Pi.add_apply, mul_add, Real.exp_add]
      have hh := mul_le_mul_of_nonneg_left he' (Real.exp_pos (t*S ω)).le
      change Real.exp (t*S ω)*Real.exp (t*X n ω) ≤ _
      dsimp only [W] at *
      nlinarith
    calc
      _ ≤ ∫ ω, W ω+t*(W ω*X n ω)+t^2*(W ω*X n ω^2) ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall (fun _ => (Real.exp_pos _).le))
          hipoly (Eventually.of_forall hpoint)
      _ = (∫ ω, W ω ∂μ)+t^2*(∫ ω, W ω*X n ω^2 ∂μ) := by
        rw [integral_add (f := fun ω => W ω+t*(W ω*X n ω))
          (g := fun ω => t^2*(W ω*X n ω^2)) (hiW.add ((hW.integrable_mul hX).const_mul t))
          ((hW.integrable_mul hXsq).const_mul (t^2)),
          integral_add (f := W) (g := fun ω => t*(W ω*X n ω)) hiW ((hW.integrable_mul hX).const_mul t),
          integral_const_mul, integral_const_mul, hiz]
        ring
      _ ≤ (∫ ω, W ω ∂μ)*(1+t^2*v n) := by
        nlinarith [mul_le_mul_of_nonneg_left hiv (sq_nonneg t)]
      _ ≤ (∫ ω, W ω ∂μ)*Real.exp (t^2*v n) :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (t^2*v n)])
          (integral_nonneg (fun _ => (Real.exp_pos _).le))
      _ ≤ Real.exp (t^2*∑ k ∈ Finset.range n, v k)*Real.exp (t^2*v n) :=
        mul_le_mul_of_nonneg_right ih (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, Finset.sum_range_succ]; congr 1; ring

/-- A deterministic conditional-variance budget controls every fixed
polynomial moment. The normalizing scale need only dominate the increment
bound and the square root of the accumulated conditional variance. -/
theorem normalized_moment_le
    (F : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hc : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n ω, ‖X n ω‖ ≤ C)
    (v : ℕ → ℝ) (hv : ∀ n, ∀ᵐ ω ∂μ, μ[fun ω => X n ω^2 | F n] ω ≤ v n)
    (n : ℕ) (R : ℝ) (hR : 0 < R) (hCR : C ≤ R)
    (hVR : (∑ k ∈ Finset.range n, v k) ≤ R^2) (p : ℕ) :
    ∫ ω, |R⁻¹ * partialSum X n ω|^p ∂μ ≤ 2*(p:ℝ)^p*Real.exp 1 := by
  have hscale : |R⁻¹| * C ≤ 1 := by
    rw [abs_of_pos (inv_pos.mpr hR), ← div_eq_inv_mul]
    exact (div_le_one hR).mpr hCR
  have hscale' : |-(R⁻¹)| * C ≤ 1 := by simpa using hscale
  have hexp : R⁻¹^2*(∑ k ∈ Finset.range n, v k) ≤ 1 := by
    rw [inv_pow, ← div_eq_inv_mul]
    exact (div_le_one (sq_pos_of_pos hR)).mpr hVR
  have bp := (mgf_partialSum_le F X ha hc C hC hb v hv R⁻¹ hscale n).trans
    (Real.exp_le_exp.mpr hexp)
  have bn := (mgf_partialSum_le F X ha hc C hC hb v hv (-(R⁻¹)) hscale' n).trans
    (Real.exp_le_exp.mpr (by simpa only [neg_sq] using hexp))
  have hm : AEStronglyMeasurable (partialSum X n) μ :=
    ((partialSum_adapted F X ha n).mono (F.le n)).aestronglyMeasurable
  have hbS (ω : Ω) : ‖partialSum X n ω‖ ≤ (n:ℝ)*C := by
    simpa using partialSum_bound X (fun _ => C) hb n ω
  have hp := (exp_memLp _ hm _ hbS R⁻¹ 1).integrable (by rfl)
  have hn := (exp_memLp _ hm _ hbS (-(R⁻¹)) 1).integrable (by rfl)
  have hi : Integrable (fun ω => |R⁻¹ * partialSum X n ω|^p) μ := by
    apply integrable_pow_abs_of_integrable_exp_mul (by norm_num : (1:ℝ) ≠ 0)
    · simpa only [one_mul] using hp
    · simpa only [neg_one_mul, neg_mul, one_mul] using hn
  calc
    _ ≤ ∫ ω, (p:ℝ)^p * (Real.exp (R⁻¹ * partialSum X n ω)+
        Real.exp (-(R⁻¹ * partialSum X n ω))) ∂μ := by
      apply integral_mono hi
      · exact (hp.add (by simpa only [neg_mul] using hn)).const_mul _
      · intro ω
        exact SubGaussianPowerMoments.abs_pow_le_exponentials _ p
    _ = (p:ℝ)^p*((∫ ω, Real.exp (R⁻¹ * partialSum X n ω) ∂μ)+
        ∫ ω, Real.exp (-(R⁻¹) * partialSum X n ω) ∂μ) := by
      simp_rw [neg_mul]
      rw [integral_const_mul, integral_add hp (by simpa only [neg_mul] using hn)]
    _ ≤ _ := by
      nlinarith [mul_le_mul_of_nonneg_left (add_le_add bp bn) (show 0 ≤ (p:ℝ)^p by positivity)]

theorem uniformMoment
    (F : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hc : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n ω, ‖X n ω‖ ≤ C)
    (v : ℕ → ℝ) (hv : ∀ n, ∀ᵐ ω ∂μ, μ[fun ω => X n ω^2 | F n] ω ≤ v n)
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n) (hCR : ∀ n, C ≤ R n)
    (hVR : ∀ n, (∑ k ∈ Finset.range n, v k) ≤ (R n)^2) (p : ℕ) :
    AdaptiveResponseMoments.UniformMoment μ
      (fun n ω => (R n)⁻¹ * partialSum X n ω) p := by
  refine ⟨2*(p:ℝ)^p*Real.exp 1, by positivity, fun n => ⟨?_, ?_⟩⟩
  · apply MemLp.of_bound
      ((((partialSum_adapted F X ha n).mono (F.le n)).const_mul ((R n)⁻¹)).aestronglyMeasurable)
      (|((R n)⁻¹)| * ((n:ℝ)*C))
    apply Eventually.of_forall
    intro ω
    rw [norm_mul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    simpa using partialSum_bound X (fun _ => C) hb n ω
  · simpa only [Real.norm_eq_abs] using
      normalized_moment_le F X ha hc C hC hb v hv n (R n) (hR n) (hCR n) (hVR n) p

/-- A Chernoff tail with a deterministic conditional-variance budget.
Choosing a fixed positive `t` gives exponential localization when the
threshold and variance budget are proportional to the exploration mass. -/
theorem upper_tail
    (F : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hc : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n ω, ‖X n ω‖ ≤ C)
    (v : ℕ → ℝ) (hv : ∀ n, ∀ᵐ ω ∂μ, μ[fun ω => X n ω^2 | F n] ω ≤ v n)
    (n : ℕ) (a t : ℝ) (ht : 0 ≤ t) (htC : t*C ≤ 1) :
    μ.real {ω | a ≤ partialSum X n ω} ≤
      Real.exp (-t*a+t^2*∑ k ∈ Finset.range n, v k) := by
  have hm : AEStronglyMeasurable (partialSum X n) μ :=
    ((partialSum_adapted F X ha n).mono (F.le n)).aestronglyMeasurable
  have hbS (ω : Ω) : ‖partialSum X n ω‖ ≤ (n:ℝ)*C := by
    simpa using partialSum_bound X (fun _ => C) hb n ω
  have h := measure_ge_le_exp_mul_mgf (μ:=μ) (X:=partialSum X n) a ht
    ((exp_memLp _ hm _ hbS t 1).integrable le_rfl)
  have hbmgf := mgf_partialSum_le F X ha hc C hC hb v hv t
    (by simpa only [abs_of_nonneg ht] using htC) n
  calc
    _ ≤ Real.exp (-t*a)*(∫ ω, Real.exp (t*partialSum X n ω) ∂μ) := h
    _ ≤ Real.exp (-t*a)*Real.exp (t^2*∑ k ∈ Finset.range n, v k) :=
      mul_le_mul_of_nonneg_left hbmgf (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

end
end QubitOracle.AdaptiveDesign.BoundedVarianceMGF
