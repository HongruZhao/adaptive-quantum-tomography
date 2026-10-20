import QubitOracle.Paper.HistoryDependentInformationConvergence
import QubitOracle.Paper.MixedInformationConvergence
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Predictable exploitation/exploration mixtures

This module lifts the weighted Cesaro argument to information matrices that
depend on the realized adaptive history.  The proof is pathwise: at each
history the policy conditional mean is exactly the convex mixture of the
exploitation and exploration conditional means.
-/

noncomputable section

namespace QubitOracle.Paper

open scoped BigOperators Matrix.Norms.L2Operator
open Filter

/-- Conditional mean information under the adaptive policy mixture. -/
theorem historyPolicyMeanInformation_adaptivePolicyMixture
    {M Y D : Type*} [Fintype M]
    (epsilon : SequentialHistory M Y → ℝ)
    (exploit explore : AdaptivePolicy M Y)
    (hepsilon_nonneg : ∀ h, 0 ≤ epsilon h)
    (hepsilon_le_one : ∀ h, epsilon h ≤ 1)
    (information : SequentialHistory M Y → M → Matrix D D ℝ)
    (history : SequentialHistory M Y) :
    historyPolicyMeanInformation
        (adaptivePolicyMixture epsilon exploit explore
          hepsilon_nonneg hepsilon_le_one) information history =
      (1 - epsilon history) •
          historyPolicyMeanInformation exploit information history +
        epsilon history •
          historyPolicyMeanInformation explore information history := by
  simpa only [historyPolicyMeanInformation, finitePolicyExpectation] using
    finitePolicyExpectation_adaptivePolicyMixture
      epsilon exploit explore hepsilon_nonneg hepsilon_le_one
      history (information history)

/-- Pathwise form of the conditional information mixture identity. -/
theorem historyPathPredictableInformation_adaptivePolicyMixture
    {M Y D : Type*} [Fintype M]
    (epsilon : SequentialHistory M Y → ℝ)
    (exploit explore : AdaptivePolicy M Y)
    (hepsilon_nonneg : ∀ h, 0 ≤ epsilon h)
    (hepsilon_le_one : ∀ h, epsilon h ≤ 1)
    (information : SequentialHistory M Y → M → Matrix D D ℝ)
    (omega : ℕ → M × Y) (k : ℕ) :
    historyPathPredictableInformation
        (adaptivePolicyMixture epsilon exploit explore
          hepsilon_nonneg hepsilon_le_one) information k omega =
      informationMixture
        (fun t => epsilon
          (trajectoryPrefixHistory (Preorder.frestrictLe t omega)))
        (fun t => historyPolicyMeanInformation exploit information
          (trajectoryPrefixHistory (Preorder.frestrictLe t omega)))
        (fun t => historyPolicyMeanInformation explore information
          (trajectoryPrefixHistory (Preorder.frestrictLe t omega))) k := by
  unfold historyPathPredictableInformation informationMixture
  exact historyPolicyMeanInformation_adaptivePolicyMixture
    epsilon exploit explore hepsilon_nonneg hepsilon_le_one information
    (trajectoryPrefixHistory (Preorder.frestrictLe k omega))

/-- Along any realized path, stage convergence and a vanishing average
exploration weight imply convergence of the predictable information average. -/
theorem historyPathPredictableInformation_mixture_tendsto
    {M Y D : Type*} [Fintype M] [Fintype D] [DecidableEq D]
    (epsilon : SequentialHistory M Y → ℝ)
    (exploit explore : AdaptivePolicy M Y)
    (hepsilon_nonneg : ∀ h, 0 ≤ epsilon h)
    (hepsilon_le_one : ∀ h, epsilon h ≤ 1)
    (information : SequentialHistory M Y → M → Matrix D D ℝ)
    (omega : ℕ → M × Y) (target : Matrix D D ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hexploit : Tendsto
      (fun k => historyPolicyMeanInformation exploit information
        (trajectoryPrefixHistory (Preorder.frestrictLe k omega)))
      atTop (nhds target))
    (hdifference : ∀ k,
      ‖historyPolicyMeanInformation explore information
          (trajectoryPrefixHistory (Preorder.frestrictLe k omega)) -
        historyPolicyMeanInformation exploit information
          (trajectoryPrefixHistory (Preorder.frestrictLe k omega))‖ ≤ C)
    (hschedule : Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N,
        epsilon (trajectoryPrefixHistory (Preorder.frestrictLe k omega)))
      atTop (nhds 0)) :
    Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ • ∑ k ∈ Finset.range N,
        historyPathPredictableInformation
          (adaptivePolicyMixture epsilon exploit explore
            hepsilon_nonneg hepsilon_le_one) information k omega)
      atTop (nhds target) := by
  let epsilonPath : ℕ → ℝ := fun k =>
    epsilon (trajectoryPrefixHistory (Preorder.frestrictLe k omega))
  let exploitPath : ℕ → Matrix D D ℝ := fun k =>
    historyPolicyMeanInformation exploit information
      (trajectoryPrefixHistory (Preorder.frestrictLe k omega))
  let explorePath : ℕ → Matrix D D ℝ := fun k =>
    historyPolicyMeanInformation explore information
      (trajectoryPrefixHistory (Preorder.frestrictLe k omega))
  have hmixture := informationMixture_cesaro_tendsto
    epsilonPath exploitPath explorePath target C hC
    (fun k => hepsilon_nonneg _) hexploit hdifference hschedule
  have hpoint : ∀ k,
      historyPathPredictableInformation
          (adaptivePolicyMixture epsilon exploit explore
            hepsilon_nonneg hepsilon_le_one) information k omega =
        informationMixture epsilonPath exploitPath explorePath k := by
    intro k
    exact historyPathPredictableInformation_adaptivePolicyMixture
      epsilon exploit explore hepsilon_nonneg hepsilon_le_one
      information omega k
  simpa only [hpoint] using hmixture

end QubitOracle.Paper
