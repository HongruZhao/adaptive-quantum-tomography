import QubitOracle.AdaptiveDesign.AdaptiveResponseMoments
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-! Passing from weak convergence of a nonnegative loss to its expectation.
Fixed bounded continuous truncations are derived from weak convergence.
There is no assumed diagonal truncated-risk limit. -/
namespace QubitOracle.AdaptiveDesign.WeakMeanLossTransfer
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

def cap (R : ℝ) (hR : 0 ≤ R) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => min (max x 0) R)
    (by fun_prop) R (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (le_max_right _ _) hR)]
      exact min_le_right _ _)

theorem cap_error (R x : ℝ) (hR : 0 < R) (hx : 0 ≤ x) :
    |x-cap R hR.le x| ≤ x^2/R := by
  change |x-min (max x 0) R| ≤ _
  rw [max_eq_left hx]
  by_cases h : x ≤ R
  · rw [min_eq_left h, sub_self, abs_zero]; positivity
  · have hRx := le_of_not_ge h
    rw [min_eq_right hRx, abs_of_nonneg (sub_nonneg.mpr hRx)]
    apply (le_div_iff₀ hR).mpr
    nlinarith [sq_nonneg (x-R)]

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem expected_cap_error {X : Ω → ℝ} (hX : MemLp X 2 μ)
    (hx : ∀ᵐ ω ∂μ, 0 ≤ X ω) (R : ℝ) (hR : 0 < R) :
    |(∫ ω, X ω ∂μ)-(∫ ω, cap R hR.le (X ω) ∂μ)| ≤ (∫ ω, X ω^2 ∂μ)/R := by
  have hi := hX.integrable (by norm_num : (1:ENNReal) ≤ 2)
  have hc : Integrable (fun ω => cap R hR.le (X ω)) μ :=
    Integrable.of_bound ((cap R hR.le).continuous.comp_aestronglyMeasurable hX.1) R
      (Eventually.of_forall (fun ω => by
        change |min (max (X ω) 0) R| ≤ R
        rw [abs_of_nonneg (le_min (le_max_right _ _) hR.le)]
        exact min_le_right _ _))
  rw [← integral_sub hi hc]
  calc
    _ ≤ ∫ ω, |X ω-cap R hR.le (X ω)| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun ω => X ω-cap R hR.le (X ω))
    _ ≤ ∫ ω, X ω^2/R ∂μ := integral_mono_ae (hi.sub hc).norm
      (hX.integrable_sq.div_const R) (hx.mono (fun ω hω => cap_error R (X ω) hR hω))
    _ = _ := by simp only [div_eq_mul_inv, integral_mul_const]

theorem capped_mean_tendsto_of_weak (X : ℕ → Ω → ℝ) (Z : Ω' → ℝ)
    (hw : TendstoInDistribution X atTop Z (fun _ => μ) ν)
    (R : ℝ) (hR : 0 ≤ R) :
    Tendsto (fun n => ∫ ω, cap R hR (X n ω) ∂μ) atTop
      (𝓝 (∫ ω, cap R hR (Z ω) ∂ν)) := by
  have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hw.tendsto (cap R hR)
  simp only [ProbabilityMeasure.coe_mk] at h
  simpa only [integral_map (hw.forall_aemeasurable _) (cap R hR).continuous.aestronglyMeasurable,
    integral_map hw.aemeasurable_limit (cap R hR).continuous.aestronglyMeasurable] using h

/-- Weak convergence and a uniform second moment imply convergence of the
mean of a nonnegative normalized loss. Different probability spaces are allowed. -/
theorem mean_tendsto_of_weak_and_secondMoment
    (X : ℕ → Ω → ℝ) (Z : Ω' → ℝ)
    (hw : TendstoInDistribution X atTop Z (fun _ => μ) ν)
    (hX : ∀ n, MemLp (X n) 2 μ) (hZ : MemLp Z 2 ν)
    (hx : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ X n ω) (hz : ∀ᵐ ω ∂ν, 0 ≤ Z ω)
    (M : ℝ) (hM : 0 ≤ M) (hm : ∀ n, ∫ ω, X n ω^2 ∂μ ≤ M) :
    Tendsto (fun n => ∫ ω, X n ω ∂μ) atTop (𝓝 (∫ ω, Z ω ∂ν)) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  let K := ∫ ω, Z ω^2 ∂ν
  have hK : 0 ≤ K := integral_nonneg (fun _ => sq_nonneg _)
  let R := 3*(M+K+1)/ε
  have hR : 0 < R := by dsimp [R]; positivity
  have htail : (M+K)/R < ε/3 := by
    apply (div_lt_iff₀ hR).mpr
    dsimp [R]
    have he : ε/3*(3*(M+K+1)/ε) = M+K+1 := by field_simp <;> ring
    rw [he]
    linarith
  have hc := Metric.tendsto_nhds.mp (capped_mean_tendsto_of_weak X Z hw R hR.le)
    (ε/3) (by positivity)
  filter_upwards [hc] with n hn
  rw [Real.dist_eq] at hn ⊢
  have hbX := (expected_cap_error (hX n) (hx n) R hR).trans
    (div_le_div_of_nonneg_right (hm n) hR.le)
  have hbZ := expected_cap_error hZ hz R hR
  have ht := abs_add_three
    ((∫ ω, X n ω ∂μ)-(∫ ω, cap R hR.le (X n ω) ∂μ))
    ((∫ ω, cap R hR.le (X n ω) ∂μ)-(∫ ω, cap R hR.le (Z ω) ∂ν))
    ((∫ ω, cap R hR.le (Z ω) ∂ν)-(∫ ω, Z ω ∂ν))
  rw [abs_sub_comm (∫ ω, cap R hR.le (Z ω) ∂ν) (∫ ω, Z ω ∂ν)] at ht
  have he : (∫ ω, X n ω ∂μ)-(∫ ω, cap R hR.le (X n ω) ∂μ)+
      ((∫ ω, cap R hR.le (X n ω) ∂μ)-(∫ ω, cap R hR.le (Z ω) ∂ν))+
      ((∫ ω, cap R hR.le (Z ω) ∂ν)-(∫ ω, Z ω ∂ν)) =
      (∫ ω, X n ω ∂μ)-(∫ ω, Z ω ∂ν) := by ring
  rw [he] at ht
  have hsum : M/R+K/R = (M+K)/R := by ring
  dsimp only [K] at hsum htail
  linarith

end
end QubitOracle.AdaptiveDesign.WeakMeanLossTransfer
