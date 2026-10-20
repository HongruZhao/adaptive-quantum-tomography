import Mathlib.Analysis.PSeries
import QubitOracle.AdaptiveDesign.BoundedMartingaleHoeffding
import QubitOracle.AdaptiveDesign.BoundedMartingaleSecondMoment
import QubitOracle.AdaptiveDesign.BoundedResponseQuarterRate
import QubitOracle.AdaptiveDesign.ExplorationBudgetStrongLaw
import QubitOracle.AdaptiveDesign.L2MartingaleBudget
/-! The square-root n log n almost-sure bound in the supplement, proved
on arbitrary probability spaces. The bound is at every sufficiently large
positive horizon, not only along a selected subsequence. -/
namespace QubitOracle.AdaptiveDesign.BoundedMartingaleLogRate
open MeasureTheory ProbabilityTheory Filter BoundedMartingaleSecondMoment
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem logarithmic_tail
    (F : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hc : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
    (C : ℝ) (hC : 0 < C) (hb : ∀ n ω, ‖X n ω‖ ≤ C) (n : ℕ) :
    μ.real {ω | C*Real.sqrt (6*((n+1:ℕ):ℝ)*Real.log ((n+2:ℕ):ℝ)) ≤ ‖partialSum X (n+1) ω‖} ≤
      2*((((n+2:ℕ):ℝ))^3)⁻¹ := by
  have hl : 0 ≤ Real.log ((n+2:ℕ):ℝ) := Real.log_nonneg (by push_cast; linarith [Nat.cast_nonneg (α:=ℝ) n])
  have h := BoundedResponseQuarterRate.subGaussian_twoSided μ (partialSum X (n+1))
    ⟨((n+1:ℕ):ℝ)*C^2, by positivity⟩
    (BoundedMartingaleHoeffding.partialSum_subGaussian F X ha hc C hC hb (n+1))
    (C*Real.sqrt (6*((n+1:ℕ):ℝ)*Real.log ((n+2:ℕ):ℝ))) (by positivity)
  change _ ≤ 2*Real.exp (-(C*Real.sqrt (6*((n+1:ℕ):ℝ)*Real.log ((n+2:ℕ):ℝ)))^2 /
    (2*(((n+1:ℕ):ℝ)*C^2))) at h
  have he : -(C*Real.sqrt (6*((n+1:ℕ):ℝ)*Real.log ((n+2:ℕ):ℝ)))^2 /
      (2*(((n+1:ℕ):ℝ)*C^2)) = -(3*Real.log ((n+2:ℕ):ℝ)) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
    ring
  have he' : Real.exp (-(3*Real.log ((n+2:ℕ):ℝ))) = ((((n+2:ℕ):ℝ))^3)⁻¹ := by
    rw [Real.exp_neg]
    congr 1
    rw [show (3:ℝ)=((3:ℕ):ℝ) by norm_num,Real.exp_nat_mul,Real.exp_log (by positivity)]
  exact h.trans_eq (by rw [he,he'])

theorem logarithmic_rate_ae
    (F : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hc : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
    (C : ℝ) (hC : 0 < C) (hb : ∀ n ω, ‖X n ω‖ ≤ C) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop,
      ‖partialSum X (n+1) ω‖ ≤ C*Real.sqrt (6*((n+1:ℕ):ℝ)*Real.log ((n+2:ℕ):ℝ)) := by
  let bad := fun n => {ω | C*Real.sqrt (6*((n+1:ℕ):ℝ)*Real.log ((n+2:ℕ):ℝ)) ≤ ‖partialSum X (n+1) ω‖}
  have hs : Summable (fun n : ℕ => 2*((((n+2:ℕ):ℝ))^3)⁻¹) :=
    ((summable_nat_add_iff 2).mpr (Real.summable_nat_pow_inv.mpr (by norm_num : 1<(3:ℕ)))).mul_left 2
  have hm : Summable (fun n => μ.real (bad n)) :=
    hs.of_nonneg_of_le (fun _ => measureReal_nonneg) (logarithmic_tail F X ha hc C hC hb)
  have hBC : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ω ∉ bad n := by
    apply ae_eventually_notMem
    have hh := hm.tsum_ofReal_lt_top
    convert hh.ne using 1
    congr 1
    funext n
    exact (ofReal_measureReal (μ:=μ) (s:=bad n)).symm
  filter_upwards [hBC] with ω hω
  filter_upwards [hω] with n hn
  exact (not_le.mp hn).le

theorem strong_law (F : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hc : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n ω, ‖X n ω‖ ≤ C) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => partialSum X n ω/(n:ℝ)) atTop (𝓝 0) := by
  have hL2 (n : ℕ) : MemLp (X n) 2 μ := MemLp.of_bound
    ((ha n).mono (F.le (n+1))).aestronglyMeasurable C (Eventually.of_forall (hb n))
  have hmass (n : ℕ) : ExplorationBudgetStrongLaw.mass (fun _ => 1) n = 1+(n:ℝ) := by
    simp [ExplorationBudgetStrongLaw.mass]
  have hmasslim : Tendsto (ExplorationBudgetStrongLaw.mass (fun _ => 1)) atTop atTop := by
    change Tendsto (fun n => ExplorationBudgetStrongLaw.mass (fun _ => 1) n) atTop atTop
    simp_rw [hmass]
    exact tendsto_atTop_add_const_left atTop 1 tendsto_natCast_atTop_atTop
  have hv (n : ℕ) : ∫ ω, X n ω^2 ∂μ ≤ C^2*1 := by
    calc
      _ ≤ ∫ _ : Ω, C^2 ∂μ := integral_mono (hL2 n).integrable_sq (integrable_const _) (fun ω => by
        have h := hb n ω
        rw [Real.norm_eq_abs] at h
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (X n ω)) h 2)
      _ = _ := by simp
  have hs := L2MartingaleBudget.normalized_sum_ae μ F X ha hc hL2
    (fun _ => 1) (fun _ => zero_le_one) hmasslim (C^2) (sq_nonneg C) hv
  filter_upwards [hs] with ω hω
  have hlim : Tendsto (fun n : ℕ => 2*|partialSum X n ω/(1+(n:ℝ))|) atTop (𝓝 0) := by
    simpa only [hmass,partialSum,abs_zero,mul_zero] using hω.abs.const_mul 2
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.norm_eq_abs,abs_div,abs_of_pos (by linarith : (0:ℝ)<n),
    abs_div,abs_of_pos (by positivity : 0<1+(n:ℝ))]
  apply (div_le_iff₀ (by linarith : (0:ℝ)<n)).mpr
  have hmul : |partialSum X n ω| * (1+(n:ℝ)) ≤ 2*|partialSum X n ω| * (n:ℝ) := by
    nlinarith [abs_nonneg (partialSum X n ω)]
  calc
    _ ≤ (2*|partialSum X n ω| * (n:ℝ))/(1+(n:ℝ)) :=
      (le_div_iff₀ (by positivity : 0<1+(n:ℝ))).mpr hmul
    _ = _ := by ring

theorem logarithmic_rate_of_ae_bounded
    (F : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hc : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
    (C : ℝ) (hC : 0 < C) (hb : ∀ n, ∀ᵐ ω ∂μ, ‖X n ω‖ ≤ C) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop,
      ‖partialSum X (n+1) ω‖ ≤ C*Real.sqrt (6*((n+1:ℕ):ℝ)*Real.log ((n+2:ℕ):ℝ)) := by
  classical
  let Y := fun n ω => if ‖X n ω‖ ≤ C then X n ω else 0
  have hYa (n : ℕ) : StronglyMeasurable[F (n+1)] (Y n) :=
    StronglyMeasurable.ite (measurableSet_le (ha n).norm.measurable measurable_const)
      (ha n) stronglyMeasurable_const
  have he (n : ℕ) : Y n =ᵐ[μ] X n := by
    filter_upwards [hb n] with ω hω
    exact if_pos hω
  have hYb (n : ℕ) (ω : Ω) : ‖Y n ω‖ ≤ C := by
    dsimp [Y]
    split_ifs with h
    · exact h
    · simpa using hC.le
  have hYc (n : ℕ) : μ[Y n | F n] =ᵐ[μ] 0 := (condExp_congr_ae (he n)).trans (hc n)
  filter_upwards [logarithmic_rate_ae F Y hYa hYc C hC hYb,ae_all_iff.mpr he] with ω hω heω
  simpa only [partialSum,heω] using hω

end
end QubitOracle.AdaptiveDesign.BoundedMartingaleLogRate
