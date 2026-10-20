import Mathlib.Probability.Moments.SubGaussian

/-!
# Bounded conditionally centered variables are conditionally sub-Gaussian

This is the source-free bridge needed to apply Mathlib's formalized
Azuma--Hoeffding inequality to adaptive information innovations.
-/

noncomputable section

namespace QubitOracle.Paper

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

/-- A globally bounded, conditionally centered real random variable satisfies
Mathlib's conditional sub-Gaussian interface.  This is Hoeffding's lemma
applied pointwise to the conditional-expectation kernel. -/
theorem hasCondSubgaussianMGF_of_mem_Icc_of_condExp_zero
    {Omega : Type*} {m mOmega : MeasurableSpace Omega}
    [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X : Omega -> Real} {a b : Real}
    (hm : m <= mOmega)
    (hX : StronglyMeasurable X)
    (hbound : forall omega, X omega ∈ Set.Icc a b)
    (hcenter : mu[X | m] =ᵐ[mu] 0) :
    HasCondSubgaussianMGF m hm X ((‖b - a‖₊ / 2) ^ 2) mu := by
  have hbound_ae : ∀ᵐ omega ∂mu, X omega ∈ Set.Icc a b :=
    ae_of_all mu hbound
  have hX_integrable : Integrable X mu :=
    Integrable.of_mem_Icc a b hX.measurable.aemeasurable hbound_ae
  have hbound_kernel :
      ∀ᵐ omega ∂mu.trim hm,
        ∀ᵐ y ∂condExpKernel mu m omega, X y ∈ Set.Icc a b := by
    apply Measure.ae_ae_of_ae_comp
    rw [condExpKernel_comp_trim hm]
    exact hbound_ae
  have hcenter_trim : mu[X | m] =ᵐ[mu.trim hm] 0 :=
    stronglyMeasurable_condExp.ae_eq_trim_of_stronglyMeasurable
      hm stronglyMeasurable_zero hcenter
  have hkernel_zero :
      (fun omega => ∫ y, X y ∂condExpKernel mu m omega) =ᵐ[mu.trim hm] 0 :=
    (condExp_ae_eq_trim_integral_condExpKernel hm hX_integrable).symm.trans hcenter_trim
  show Kernel.HasSubgaussianMGF X ((‖b - a‖₊ / 2) ^ 2)
    (condExpKernel mu m) (mu.trim hm)
  refine ⟨?_, ?_⟩
  · intro t
    rw [condExpKernel_comp_trim hm]
    exact integrable_exp_mul_of_mem_Icc hX.measurable.aemeasurable hbound_ae
  · filter_upwards [hbound_kernel, hkernel_zero] with omega homega hzero
    intro t
    exact (hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      hX.measurable.aemeasurable homega hzero).mgf_le t

end QubitOracle.Paper
