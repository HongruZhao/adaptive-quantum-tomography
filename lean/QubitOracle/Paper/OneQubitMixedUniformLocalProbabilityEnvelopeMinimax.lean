import QubitOracle.Paper.OneQubitMixedUniformLocalProbabilityEnvelopeClosed
import QubitOracle.Paper.OneQubitMixedUniformLocalRiskUpperBound

/-!
# Deferred exact-cycle LAN/local-minimax reduction

The finite-law probability and uniform-risk layer is isolated in the imported
non-LAN module.  This file contains only the explicitly deferred minimax tail.
-/

namespace QubitOracle.Paper

/-- Exact-cycle model conditions supplied to the preceding upper-bound module. -/
def mixedUniformLocalExactCyclePolynomialConditions
    (theta b : RLSVector 3) (H : ℝ)
    (hBase : MixedFrozenPolynomialEndpointConditions theta b)
    (hH : 0 ≤ H) :
    MixedUniformLocalPolynomialConditions theta b
      mixedUniformLocalExactCycleN H mixedUniformLocalExactCycleQFinal where
  toMixedFrozenPolynomialEndpointConditions := hBase
  radius_nonnegative := hH
  local_scale_tendsto_zero := mixedUniformLocalExactCycleScale_tendsto_zero
  final_allocation_positive := mixedUniformLocalExactCycleQFinal_pos

/-- Conditional exact-cycle minimax upper reduction.  The lower bound is not
weakened: it is still exactly `ExactLANLocalMinimaxQuadraticTransfer`. -/
theorem mixedConcreteExactCycleConditionalLocalMinimaxEquality_reduction
    {E : HajekExperimentSequence (Fin 3)}
    {truth : HajekParameter (Fin 3)}
    (C : FrozenMixedQubitLANConclusion E truth)
    (transfer : ExactLANLocalMinimaxQuadraticTransfer E truth C.lan)
    (theta b : RLSVector 3) (H : ℝ)
    (hBase : MixedFrozenPolynomialEndpointConditions theta b)
    (hH : 0 ≤ H)
    (hBridge : MixedExactCycleUniformExactLossAveragingBridge theta b H) :
    MixedConcreteConditionalLocalMinimaxEqualityReduction
      C theta b mixedUniformLocalExactCycleN H
      mixedUniformLocalExactCycleQFinal := by
  exact mixedConcreteBuresFidelityConditionalLocalMinimaxEquality_reduction
    C transfer theta b mixedUniformLocalExactCycleN H
    mixedUniformLocalExactCycleQFinal
    (mixedUniformLocalExactCyclePolynomialConditions
      theta b H hBase hH)
    (mixedUniformLocalProbabilityEnvelope_exactCycle_reduction
      theta b H hH hBase.positive hBase.interior hBase.seed hBridge)

namespace Label

/-- Honest paper-facing exact-cycle reduction.  It is not named `_closed`
because the finite exact-loss averaging bridge remains explicit. -/
theorem thm_mixed_exact_cycle_uniform_local_minimax_qubit_reduction
    {E : HajekExperimentSequence (Fin 3)}
    {truth : HajekParameter (Fin 3)}
    (C : FrozenMixedQubitLANConclusion E truth)
    (transfer : ExactLANLocalMinimaxQuadraticTransfer E truth C.lan)
    (theta b : RLSVector 3) (H : ℝ)
    (hBase : MixedFrozenPolynomialEndpointConditions theta b)
    (hH : 0 ≤ H)
    (hBridge : MixedExactCycleUniformExactLossAveragingBridge theta b H) :
    MixedConcreteConditionalLocalMinimaxEqualityReduction
      C theta b mixedUniformLocalExactCycleN H
      mixedUniformLocalExactCycleQFinal :=
  mixedConcreteExactCycleConditionalLocalMinimaxEquality_reduction
    C transfer theta b H hBase hH hBridge

end Label

end QubitOracle.Paper
