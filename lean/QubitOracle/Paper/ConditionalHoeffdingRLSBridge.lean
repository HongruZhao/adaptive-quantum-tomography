import Mathlib.Probability.Moments.SubGaussian
import QubitOracle.Paper.SourceFaithfulRLSConfidenceEllipsoid

namespace QubitOracle.Paper

open MeasureTheory ProbabilityTheory Real Set

noncomputable section

/-- A bounded conditionally centered real variable is conditionally sub-Gaussian. -/
theorem hasCondSubgaussianMGF_of_mem_Icc_of_condExp_eq_zero
    {Omega : Type*}
    [mOmega : MeasurableSpace Omega]
    [StandardBorelSpace Omega]
    {mu : Measure Omega}
    [IsProbabilityMeasure mu]
    {m : MeasurableSpace Omega}
    (hm : m ≤ mOmega)
    {X : Omega → ℝ}
    {a b : ℝ}
    (hX : Measurable[mOmega] X)
    (hBound : ∀ᵐ omega ∂mu, X omega ∈ Set.Icc a b)
    (hCenter : mu[X | m] =ᵐ[mu] 0) :
    HasCondSubgaussianMGF m hm X ((‖b - a‖₊ / 2) ^ 2) (μ := mu) := by
  change @Kernel.HasSubgaussianMGF Omega Omega mOmega m X ((‖b - a‖₊ / 2) ^ 2)
    (condExpKernel (mΩ := mOmega) mu m) (mu.trim hm)
  have hXIntegrable : Integrable X mu :=
    Integrable.of_mem_Icc a b hX.aemeasurable hBound
  have hBoundKernel :
      ∀ᵐ omega' ∂(mu.trim hm),
        ∀ᵐ omega ∂condExpKernel (mΩ := mOmega) mu m omega',
          X omega ∈ Set.Icc a b := by
    apply Measure.ae_ae_of_ae_comp
    simpa only [condExpKernel_comp_trim (mΩ := mOmega) hm] using hBound
  have hCondIntegral :=
    condExp_ae_eq_trim_integral_condExpKernel (mΩ := mOmega) hm hXIntegrable
  have hCenterTrim : mu[X | m] =ᵐ[mu.trim hm] 0 := by
    apply StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm
    · exact stronglyMeasurable_condExp
    · fun_prop
    · exact hCenter
  constructor
  · intro t
    rw [condExpKernel_comp_trim (mΩ := mOmega) hm]
    exact integrable_exp_mul_of_mem_Icc hX.aemeasurable hBound
  · filter_upwards [hBoundKernel, hCondIntegral, hCenterTrim] with omega hBK hCI hCZ
    intro t
    have hIntegralZero :
        ∫ x, X x ∂condExpKernel (mΩ := mOmega) mu m omega = 0 :=
      hCI.symm.trans hCZ
    exact (hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (μ := condExpKernel (mΩ := mOmega) mu m omega)
      hX.aemeasurable hBK hIntegralZero).mgf_le t

/--
Build the exact source-faithful self-normalized martingale data from measurable,
adapted, bounded, conditionally centered noise.  The width-four interval
`[-2, 2]` gives the APS noise scale `R = 2`.
-/
def selfNormalizedMartingaleData_of_boundedCenteredNoise
    {Omega : Type*}
    [mOmega : MeasurableSpace Omega]
    [StandardBorelSpace Omega]
    {d : ℕ}
    {mu : Measure Omega}
    [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ mOmega)
    (regressor : ℕ → Omega → Fin d → ℝ)
    (noise : ℕ → Omega → ℝ)
    (regressorAdapted : Adapted filtration regressor)
    (noiseAdapted : Adapted filtration noise)
    (hNoiseMeasurable : ∀ k, Measurable[mOmega] (noise k))
    (hNoiseBound : ∀ k, ∀ᵐ omega ∂mu, noise k omega ∈ Set.Icc (-2 : ℝ) 2)
    (hCenter : ∀ k, mu[noise (k + 1) | filtration k] =ᵐ[mu] 0) :
    SourceFaithfulSelfNormalized.SelfNormalizedMartingaleData Omega d mu 2 where
  filtration := filtration
  regressor := regressor
  noise := noise
  regressorAdapted := regressorAdapted
  noiseAdapted := noiseAdapted
  noiseIntegrable k :=
    Integrable.of_mem_Icc (-2) 2 (hNoiseMeasurable k).aemeasurable (hNoiseBound k)
  exponentialIntegrable k gamma :=
    (hasCondSubgaussianMGF_of_mem_Icc_of_condExp_eq_zero
      (filtration.le k) (hNoiseMeasurable (k + 1))
      (hNoiseBound (k + 1)) (hCenter k)).integrable_exp_mul gamma
  martingaleDifference := hCenter
  conditionallySubGaussian k gamma := by
    have h :=
      (hasCondSubgaussianMGF_of_mem_Icc_of_condExp_eq_zero
        (filtration.le k) (hNoiseMeasurable (k + 1))
        (hNoiseBound (k + 1)) (hCenter k)).ae_condExp_le gamma
    filter_upwards [h] with omega hOmega
    convert hOmega using 1 <;> norm_num <;> ring

end

end QubitOracle.Paper
