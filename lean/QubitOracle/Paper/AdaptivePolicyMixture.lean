import QubitOracle.Paper.SequentialMartingale

noncomputable section

namespace QubitOracle.Paper

open scoped BigOperators

/-- History-dependent convex mixture of an exploitation policy and an
exploration policy. -/
def adaptivePolicyMixture
    {M Y : Type*} [Fintype M]
    (epsilon : SequentialHistory M Y → ℝ)
    (exploit explore : AdaptivePolicy M Y)
    (hepsilon_nonneg : ∀ h, 0 ≤ epsilon h)
    (hepsilon_le_one : ∀ h, epsilon h ≤ 1) : AdaptivePolicy M Y where
  mass h m :=
    (1 - epsilon h) * exploit.mass h m + epsilon h * explore.mass h m
  mass_nonneg h m :=
    add_nonneg
      (mul_nonneg (sub_nonneg.mpr (hepsilon_le_one h))
        (exploit.mass_nonneg h m))
      (mul_nonneg (hepsilon_nonneg h) (explore.mass_nonneg h m))
  sum_mass h := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      exploit.sum_mass, explore.sum_mass]
    ring

/-- Conditional expectation under the adaptive mixture decomposes into the
exploitation and exploration conditional expectations. -/
theorem finitePolicyExpectation_adaptivePolicyMixture
    {M Y E : Type*} [Fintype M] [AddCommMonoid E] [Module ℝ E]
    (epsilon : SequentialHistory M Y → ℝ)
    (exploit explore : AdaptivePolicy M Y)
    (hepsilon_nonneg : ∀ h, 0 ≤ epsilon h)
    (hepsilon_le_one : ∀ h, epsilon h ≤ 1)
    (h : SequentialHistory M Y) (information : M → E) :
    finitePolicyExpectation
        (adaptivePolicyMixture epsilon exploit explore
          hepsilon_nonneg hepsilon_le_one) h information =
      (1 - epsilon h) • finitePolicyExpectation exploit h information +
        epsilon h • finitePolicyExpectation explore h information := by
  unfold finitePolicyExpectation adaptivePolicyMixture
  simp_rw [add_smul, mul_smul]
  rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum]

namespace Label

/-- Supplement equation `SI_predictable_decompose`: the predictable
information of an exploitation/exploration mixture is its convex-mixture
information. -/
theorem eq_SI_predictable_decompose
    {M Y E : Type*} [Fintype M] [AddCommMonoid E] [Module ℝ E]
    (epsilon : SequentialHistory M Y → ℝ)
    (exploit explore : AdaptivePolicy M Y)
    (hepsilon_nonneg : ∀ h, 0 ≤ epsilon h)
    (hepsilon_le_one : ∀ h, epsilon h ≤ 1)
    (h : SequentialHistory M Y) (information : M → E) :
    finitePolicyExpectation
        (adaptivePolicyMixture epsilon exploit explore
          hepsilon_nonneg hepsilon_le_one) h information =
      (1 - epsilon h) • finitePolicyExpectation exploit h information +
        epsilon h • finitePolicyExpectation explore h information :=
  finitePolicyExpectation_adaptivePolicyMixture
    epsilon exploit explore hepsilon_nonneg hepsilon_le_one h information

end Label
end QubitOracle.Paper
