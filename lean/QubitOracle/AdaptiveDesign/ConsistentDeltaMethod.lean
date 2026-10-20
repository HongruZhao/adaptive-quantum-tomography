import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-! A vector delta method for consistent statistics. The proof uses the
normalized Frechet remainder and Slutsky, not independence of observations.
It permits arbitrary measurable extensions of a local coordinate map. -/
namespace QubitOracle.AdaptiveDesign.ConsistentDeltaMethod
open Filter MeasureTheory Asymptotics
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

variable {Ω Ω' E F : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology E] [SecondCountableTopology F]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ν : Measure Ω'} [IsProbabilityMeasure ν]

def normalizedRemainder (g : E → F) (L : E →L[ℝ] F) (θ : E) (x : E) : F :=
  ‖x-θ‖⁻¹ • (g x-g θ-L (x-θ))

theorem normalizedRemainder_tendsto {g : E → F} {L : E →L[ℝ] F} {θ : E}
    (hg : HasFDerivAt g L θ) :
    Tendsto (normalizedRemainder g L θ) (𝓝 θ) (𝓝 0) := by
  exact hg.isLittleO.norm_right.tendsto_inv_smul_nhds_zero

theorem reconstruction (g : E → F) (L : E →L[ℝ] F) (θ x : E) (a : ℝ) (ha : 0 ≤ a) :
    L (a • (x-θ)) + ‖a • (x-θ)‖ • normalizedRemainder g L θ x = a • (g x-g θ) := by
  by_cases hx : x = θ
  · subst x; simp [normalizedRemainder]
  · have hnorm : ‖x-θ‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)
    rw [normalizedRemainder, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha,
      smul_smul, mul_inv_cancel_right₀ hnorm, map_smul, smul_sub, smul_sub]
    abel

/-- Multivariate delta method from consistency and the original weak limit.
The limit probability space may differ from the observation space. -/
theorem delta_method
    (X : ℕ → Ω → E) (Z : Ω' → E) (a : ℕ → ℝ) (θ : E)
    (ha : ∀ n, 0 ≤ a n) (hX : ∀ n, AEMeasurable (X n) μ)
    (hc : ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 θ))
    (hclt : TendstoInDistribution (fun n ω => a n • (X n ω-θ)) atTop Z (fun _ => μ) ν)
    (g : E → F) (hgmeas : Measurable g) (L : E →L[ℝ] F) (hg : HasFDerivAt g L θ) :
    TendstoInDistribution (fun n ω => a n • (g (X n ω)-g θ))
      atTop (fun ω => L (Z ω)) (fun _ => μ) ν := by
  have hrmeas : Measurable (normalizedRemainder g L θ) := by
    unfold normalizedRemainder
    fun_prop
  have hr : TendstoInMeasure μ (fun n ω => normalizedRemainder g L θ (X n ω))
      atTop (fun _ => 0) := by
    apply tendstoInMeasure_of_tendsto_ae
      (fun n => (hrmeas.comp_aemeasurable (hX n)).aestronglyMeasurable)
    filter_upwards [hc] with ω hω
    exact (normalizedRemainder_tendsto hg).comp hω
  have hh := hclt.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun z : E × F => L z.1 + ‖z.1‖ • z.2) (by fun_prop) hr
    (fun n => hrmeas.comp_aemeasurable (hX n))
  exact hh.congr (fun n => Eventually.of_forall (fun ω => reconstruction g L θ (X n ω) (a n) (ha n)))
    (Eventually.of_forall (fun ω => by simp))

end
end QubitOracle.AdaptiveDesign.ConsistentDeltaMethod
