import QubitOracle.AdaptiveDesign.GlobalPFSICFisher
import QubitOracle.GillMassarBridge

/-!
# Global finite-POVM optimality of the constructed P2 measurement

The comparison class consists of all finite-outcome single-copy POVMs with
positive-definite Fisher information at the pure reference state. Their
Gill--Massar trace bound is proved from positivity and completeness of their
actual effects in `FiniteGillMassar`; no statistical or optimization
certificate is a premise of the result below.

The criterion is the local inverse-information design criterion. These
results do not assert efficiency or risk attainment by the ridge estimator.
-/

namespace QubitOracle.AdaptiveDesign.GlobalPFSIC

noncomputable section

/-- The constructed globally identifying POVM is regular at its design ray. -/
theorem measurementPOVM_referenceFisher_posDef (d : ℕ) (hd : 0 < d) :
    (referenceFisher (measurementPOVM d hd)).PosDef := by
  rw [measurementPOVM_referenceFisher]
  exact Matrix.PosDef.one.smul (by norm_num)

/-- Its exact inverse-information criterion for every isotropic loss weight. -/
theorem measurementPOVM_isotropicRisk (d : ℕ) (hd : 0 < d) (g : ℝ) :
    isotropicRisk g (referenceFisher (measurementPOVM d hd)) = 4*g*d := by
  rw [measurementPOVM_referenceFisher, isotropicRisk_half_identity, tangentIndex_card]
  push_cast
  ring

/-- Global design optimality over actual finite-outcome POVMs, with the
competitor trace-budget inequality discharged by the finite Gill--Massar
proof. -/
theorem measurementPOVM_optimal_over_finitePOVM
    (d : ℕ) (hd : 0 < d) {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O)
    (hP : (referenceFisher P).PosDef) (g : ℝ) (hg : 0 ≤ g) :
    isotropicRisk g (referenceFisher (measurementPOVM d hd)) ≤
      isotropicRisk g (referenceFisher P) := by
  rw [measurementPOVM_isotropicRisk]
  exact finitePOVM_risk_lower_bound g P hg hP

/-- For a strictly positive isotropic weight, precisely the half-identity
information matrices tie the constructed measurement. -/
theorem finitePOVM_ties_measurementPOVM_iff
    (d : ℕ) (hd : 0 < d) {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O)
    (hP : (referenceFisher P).PosDef) (g : ℝ) (hg : 0 < g) :
    isotropicRisk g (referenceFisher P) =
      isotropicRisk g (referenceFisher (measurementPOVM d hd)) ↔
      referenceFisher P = (1/2 : ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ) := by
  rw [measurementPOVM_isotropicRisk]
  exact gillMassarBudget_risk_eq_iff g (referenceFisher P) hg hP
    (referenceFisher_satisfies_gillMassarTraceBudget P)

/-- The local infidelity/Bures criterion is `D-1`, attained by the actual
constructed measurement and bounded below for every regular finite POVM. -/
theorem measurementPOVM_infidelity_optimality
    (d : ℕ) (hd : 0 < d) {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (hP : (referenceFisher P).PosDef) :
    isotropicRisk (1/4 : ℝ) (referenceFisher (measurementPOVM d hd)) = d ∧
      (d : ℝ) ≤ isotropicRisk (1/4 : ℝ) (referenceFisher P) := by
  constructor
  · rw [measurementPOVM_isotropicRisk]
    ring
  · exact finitePOVM_buresQuadraticRisk_lower_bound P hP

/-- Squared Frobenius loss on pure projectors has twice the infidelity
quadratic weight and hence the sharp design criterion `2(D-1)`. -/
theorem measurementPOVM_frobenius_optimality
    (d : ℕ) (hd : 0 < d) {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (hP : (referenceFisher P).PosDef) :
    isotropicRisk (1/2 : ℝ) (referenceFisher (measurementPOVM d hd)) = 2*d ∧
      2*(d : ℝ) ≤ isotropicRisk (1/2 : ℝ) (referenceFisher P) := by
  constructor
  · rw [measurementPOVM_isotropicRisk]
    ring
  · exact finitePOVM_frobeniusRisk_lower_bound P hP

end
end QubitOracle.AdaptiveDesign.GlobalPFSIC
