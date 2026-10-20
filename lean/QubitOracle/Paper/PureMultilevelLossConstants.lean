import QubitOracle.Paper.PureMultilevelDeterministicGeometryClosed
import QubitOracle.Paper.PureMultilevelProjectorGeometry
import QubitOracle.Paper.PureStateFoundations
/-!
# Exact loss constants for finite-dimensional pure states

This module connects the squared overlap of two pure states to the physical
losses used in the multilevel theorem.  It first records exact identities for
rank-one density matrices.  It then starts from one explicit local-overlap
expansion and derives, rather than assumes, the local coefficients `1 / 4`
for squared Bures loss and `1 / 2` for squared Frobenius loss.

No probabilistic limit theorem or external scientific result is used here.
-/

namespace QubitOracle.Paper
namespace PureMultilevelLossConstants

open Filter Topology
open PureMultilevelDeterministicGeometry
open PureMultilevelProjectorGeometry

noncomputable section

/-- Squared overlap is exactly the trace of the product of the two rank-one
projectors. -/
theorem pureProjectorFidelity_eq_trace
    {d : ℕ} (psi phi : Fin (d + 1) → ℂ) :
    (pureMultilevelFidelity psi phi : ℂ) =
      (rankOneDensity phi * rankOneDensity psi).trace :=
  pureMultilevelFidelity_eq_rankOneTrace psi phi

/-- For normalized pure vectors, the entrywise squared Frobenius distance of
their rank-one projectors is exactly `2 - 2 F`, where `F` is squared-overlap
fidelity. -/
theorem pureProjectorFrobeniusSq_eq_two_sub_two_fidelity
    {d : ℕ} (psi phi : Fin (d + 1) → ℂ)
    (hPsi : pureStateNormSq psi = 1)
    (hPhi : pureStateNormSq phi = 1) :
    pureRankOneDensityFrobeniusSq psi phi =
      2 - 2 * pureMultilevelFidelity psi phi := by
  rw [pureRankOneDensityFrobeniusSq_eq_two_infidelity
    psi phi hPsi hPhi]
  unfold pureMultilevelInfidelity
  ring

/-- Squared Bures distance between pure states is exactly
`2 - 2 * sqrt F`. -/
theorem pureProjectorSquaredBures_eq_two_sub_two_sqrt_fidelity
    {d : ℕ} (psi phi : Fin (d + 1) → ℂ) :
    pureMultilevelBuresSq psi phi =
      2 - 2 * Real.sqrt (pureMultilevelFidelity psi phi) := by
  unfold pureMultilevelBuresSq pureMultilevelRootFidelity
  ring

/-- Rationalized exact Bures identity.  This is the algebraic bridge showing
that Bures loss and infidelity have the same local quadratic coefficient. -/
theorem pureProjectorSquaredBures_eq_two_infidelity_div_one_add_rootFidelity
    {d : ℕ} (psi phi : Fin (d + 1) → ℂ) :
    pureMultilevelBuresSq psi phi =
      2 * pureMultilevelInfidelity psi phi /
        (1 + pureMultilevelRootFidelity psi phi) := by
  have hFidelityNonnegative :
      0 ≤ pureMultilevelFidelity psi phi := by
    unfold pureMultilevelFidelity basisBornProbability
    exact Complex.normSq_nonneg _
  have hRootSquare :
      Real.sqrt (pureMultilevelFidelity psi phi) ^ 2 =
        pureMultilevelFidelity psi phi :=
    Real.sq_sqrt hFidelityNonnegative
  have hDenominator :
      1 + Real.sqrt (pureMultilevelFidelity psi phi) ≠ 0 := by
    positivity
  unfold pureMultilevelBuresSq pureMultilevelRootFidelity
    pureMultilevelInfidelity
  field_simp [hDenominator]
  nlinarith [hRootSquare]

/-- Complete exact projector-loss package for two normalized pure vectors. -/
theorem normalizedPureProjector_exactLossIdentities
    {d : ℕ} (psi phi : Fin (d + 1) → ℂ)
    (hPsi : pureStateNormSq psi = 1)
    (hPhi : pureStateNormSq phi = 1) :
    (pureMultilevelFidelity psi phi : ℂ) =
        (rankOneDensity phi * rankOneDensity psi).trace ∧
    pureRankOneDensityFrobeniusSq psi phi =
        2 - 2 * pureMultilevelFidelity psi phi ∧
    pureMultilevelBuresSq psi phi =
        2 - 2 * Real.sqrt (pureMultilevelFidelity psi phi) := by
  exact ⟨pureProjectorFidelity_eq_trace psi phi,
    pureProjectorFrobeniusSq_eq_two_sub_two_fidelity
      psi phi hPsi hPhi,
    pureProjectorSquaredBures_eq_two_sub_two_sqrt_fidelity psi phi⟩

/-- A scaled local-overlap expansion.  The first clause says that the
estimated ray approaches the true ray.  The second is the supplied overlap
expansion: after multiplication by `scale`, ordinary infidelity converges to
`q / 4`.  The following theorems transfer this one hypothesis to physical
Frobenius and Bures losses. -/
def HasScaledLocalOverlapExpansion
    {d : ℕ} (estimate : ℕ → Fin (d + 1) → ℂ)
    (truth : Fin (d + 1) → ℂ) (scale : ℕ → ℝ) (q : ℝ) : Prop :=
  Tendsto (fun n => pureMultilevelFidelity (estimate n) truth)
      atTop (𝓝 1) ∧
    Tendsto (fun n => scale n *
      (1 - pureMultilevelFidelity (estimate n) truth))
      atTop (𝓝 (q / 4))

theorem HasScaledLocalOverlapExpansion.fidelity_tendsto_one
    {d : ℕ} {estimate : ℕ → Fin (d + 1) → ℂ}
    {truth : Fin (d + 1) → ℂ} {scale : ℕ → ℝ} {q : ℝ}
    (h : HasScaledLocalOverlapExpansion estimate truth scale q) :
    Tendsto (fun n => pureMultilevelFidelity (estimate n) truth)
      atTop (𝓝 1) := by
  exact h.1

/-- The supplied overlap expansion is exactly the local infidelity
coefficient `1 / 4`. -/
theorem HasScaledLocalOverlapExpansion.scaled_infidelity_tendsto_quarter
    {d : ℕ} {estimate : ℕ → Fin (d + 1) → ℂ}
    {truth : Fin (d + 1) → ℂ} {scale : ℕ → ℝ} {q : ℝ}
    (h : HasScaledLocalOverlapExpansion estimate truth scale q) :
    Tendsto (fun n => scale n *
      pureMultilevelInfidelity (estimate n) truth)
      atTop (𝓝 (q / 4)) := by
  simpa [HasScaledLocalOverlapExpansion, pureMultilevelInfidelity] using h.2

/-- The exact projector identity doubles the overlap defect, yielding the
local squared-Frobenius coefficient `1 / 2`. -/
theorem HasScaledLocalOverlapExpansion.scaled_frobeniusSq_tendsto_half
    {d : ℕ} {estimate : ℕ → Fin (d + 1) → ℂ}
    {truth : Fin (d + 1) → ℂ} {scale : ℕ → ℝ} {q : ℝ}
    (h : HasScaledLocalOverlapExpansion estimate truth scale q)
    (hEstimate : ∀ n, pureStateNormSq (estimate n) = 1)
    (hTruth : pureStateNormSq truth = 1) :
    Tendsto (fun n => scale n *
      pureRankOneDensityFrobeniusSq (estimate n) truth)
      atTop (𝓝 (q / 2)) := by
  have hTwo : Tendsto (fun _n : ℕ => (2 : ℝ)) atTop (𝓝 2) :=
    tendsto_const_nhds
  have hLimit := hTwo.mul h.scaled_infidelity_tendsto_quarter
  convert hLimit using 1
  · funext n
    rw [pureProjectorFrobeniusSq_eq_two_sub_two_fidelity
      (estimate n) truth (hEstimate n) hTruth]
    unfold pureMultilevelInfidelity
    ring_nf
  · congr 1
    ring

/-- Rationalization of the exact Bures formula gives a factor converging to
one, hence squared Bures loss inherits the local coefficient `1 / 4`. -/
theorem HasScaledLocalOverlapExpansion.scaled_squaredBures_tendsto_quarter
    {d : ℕ} {estimate : ℕ → Fin (d + 1) → ℂ}
    {truth : Fin (d + 1) → ℂ} {scale : ℕ → ℝ} {q : ℝ}
    (h : HasScaledLocalOverlapExpansion estimate truth scale q) :
    Tendsto (fun n => scale n *
      pureMultilevelBuresSq (estimate n) truth)
      atTop (𝓝 (q / 4)) := by
  have hRoot : Tendsto
      (fun n => pureMultilevelRootFidelity (estimate n) truth)
      atTop (𝓝 1) := by
    have hSqrt := Real.continuous_sqrt.continuousAt.tendsto.comp
      h.fidelity_tendsto_one
    simpa [pureMultilevelRootFidelity, Function.comp_def] using hSqrt
  have hOne : Tendsto (fun _n : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hDenominator : Tendsto
      (fun n => 1 + pureMultilevelRootFidelity (estimate n) truth)
      atTop (𝓝 2) := by
    convert hOne.add hRoot using 1 <;> norm_num
  have hTwo : Tendsto (fun _n : ℕ => (2 : ℝ)) atTop (𝓝 2) :=
    tendsto_const_nhds
  have hFactor : Tendsto
      (fun n => 2 /
        (1 + pureMultilevelRootFidelity (estimate n) truth))
      atTop (𝓝 1) := by
    convert hTwo.div hDenominator
      (by norm_num : (2 : ℝ) ≠ 0) using 1
    · funext n
      rfl
    · norm_num
  have hLimit := h.scaled_infidelity_tendsto_quarter.mul hFactor
  convert hLimit using 1
  · funext n
    rw [pureProjectorSquaredBures_eq_two_infidelity_div_one_add_rootFidelity]
    ring_nf
  · congr 1
    ring

/-- Both physical local loss constants derived from one overlap expansion:
`1 / 4` for squared Bures loss and `1 / 2` for squared Frobenius loss. -/
theorem HasScaledLocalOverlapExpansion.physicalLossConstants
    {d : ℕ} {estimate : ℕ → Fin (d + 1) → ℂ}
    {truth : Fin (d + 1) → ℂ} {scale : ℕ → ℝ} {q : ℝ}
    (h : HasScaledLocalOverlapExpansion estimate truth scale q)
    (hEstimate : ∀ n, pureStateNormSq (estimate n) = 1)
    (hTruth : pureStateNormSq truth = 1) :
    Tendsto (fun n => scale n *
      pureMultilevelBuresSq (estimate n) truth)
        atTop (𝓝 (q / 4)) ∧
    Tendsto (fun n => scale n *
      pureRankOneDensityFrobeniusSq (estimate n) truth)
        atTop (𝓝 (q / 2)) := by
  exact ⟨h.scaled_squaredBures_tendsto_quarter,
    h.scaled_frobeniusSq_tendsto_half hEstimate hTruth⟩

end

end PureMultilevelLossConstants
end QubitOracle.Paper
