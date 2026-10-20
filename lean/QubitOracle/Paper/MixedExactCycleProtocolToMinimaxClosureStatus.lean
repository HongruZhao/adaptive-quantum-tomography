import QubitOracle.Paper.MathlibHoeffding1963Bridge
import QubitOracle.Paper.OneQubitMixedUniformLocalProbabilityEnvelopeMinimax
import QubitOracle.Paper.OneQubitMixedUniformLocalExactLossAveraging

/-!
# Mixed exact-cycle protocol-to-minimax closure status

This module records the current trust boundary without claiming an unavailable
end-to-end theorem.

The exact-cycle protocol's finite-law and uniform-local upper-risk arguments
are kernel-proved below.  The current minimax reduction still requires two
inputs that are not constructed here:

* a `FrozenMixedQubitLANConclusion` for the same concrete experiment; and
* the vector LAN-to-local-minimax transfer for that LAN certificate.

Thus the second theorem is deliberately conditional on
`MixedExactCycleLANMinimaxBoundary`.  This is a machine-checked reduction of
the remaining gap, not a proof that no future Lean term can inhabit it.
-/

namespace QubitOracle.Paper

noncomputable section

/-- The two unresolved LAN/minimax inputs in the current exact-cycle endpoint.
No field hides a protocol concentration or physical-loss upper-bound premise. -/
structure MixedExactCycleLANMinimaxBoundary
    {E : HajekExperimentSequence (Fin 3)}
    {truth : HajekParameter (Fin 3)} where
  lanCertificate : FrozenMixedQubitLANConclusion E truth
  lanToMinimax :
    ExactLANLocalMinimaxQuadraticTransfer
      E truth lanCertificate.lan

/-- The exact-loss averaging bridge is fully discharged from the concrete
qubit assumptions and Mathlib's finite Hoeffding argument. -/
theorem mixedExactCycle_exactLossAveragingBridge_kernel
    (theta b : RLSVector 3) (H : ℝ)
    (hBase : MixedFrozenPolynomialEndpointConditions theta b)
    (hH : 0 ≤ H) :
    MixedExactCycleUniformExactLossAveragingBridge theta b H := by
  exact mixedExactCycleUniformExactLossAveragingBridge_closed
    b theta H hH hBase.positive hBase.interior hBase.seed
    (mixedExactCycleUniformFiniteHoeffdingContract_mathlib
      theta H hBase.interior)

/-- The concrete exact-cycle protocol has the required uniform local upper
bounds for squared Bures loss and ordinary infidelity.  This theorem uses no
LAN or minimax-transfer premise. -/
theorem mixedExactCycle_uniformPhysicalLossUpper_kernel
    (theta b : RLSVector 3) (H : ℝ)
    (hBase : MixedFrozenPolynomialEndpointConditions theta b)
    (hH : 0 ≤ H) :
    MixedUniformLocalRiskLimsupLE
        MixedUniformLocalExactLoss.squaredBures theta b
        mixedUniformLocalExactCycleN H (9 / 4) ∧
      MixedUniformLocalRiskLimsupLE
        MixedUniformLocalExactLoss.ordinaryInfidelity theta b
        mixedUniformLocalExactCycleN H (9 / 4) := by
  let hConditions :=
    mixedUniformLocalExactCyclePolynomialConditions theta b H hBase hH
  let hEnvelope :=
    mixedUniformLocalProbabilityEnvelope_exactCycle_mathlib
      theta b H hH hBase.positive hBase.interior hBase.seed
  exact
    ⟨mixedUniformLocalSquaredBuresRisk_limsup_le_nine_fourths
        theta b mixedUniformLocalExactCycleN H
        mixedUniformLocalExactCycleQFinal hConditions hEnvelope,
      mixedUniformLocalOrdinaryInfidelityRisk_limsup_le_nine_fourths
        theta b mixedUniformLocalExactCycleN H
        mixedUniformLocalExactCycleQFinal hConditions hEnvelope⟩

/-- Current strongest assembly theorem: every non-LAN exact-cycle obligation
is discharged internally, and the final result is reduced exactly to the
explicit LAN certificate and LAN-to-minimax transfer boundary above. -/
theorem mixedExactCycle_protocolToMinimax_reduced_to_LAN_boundary
    {E : HajekExperimentSequence (Fin 3)}
    {truth : HajekParameter (Fin 3)}
    (boundary : MixedExactCycleLANMinimaxBoundary
      (E := E) (truth := truth))
    (theta b : RLSVector 3) (H : ℝ)
    (hBase : MixedFrozenPolynomialEndpointConditions theta b)
    (hH : 0 ≤ H) :
    MixedConcreteConditionalLocalMinimaxEqualityReduction
      boundary.lanCertificate theta b
      mixedUniformLocalExactCycleN H
      mixedUniformLocalExactCycleQFinal := by
  exact mixedConcreteExactCycleConditionalLocalMinimaxEquality_reduction
    boundary.lanCertificate boundary.lanToMinimax
    theta b H hBase hH
    (mixedExactCycle_exactLossAveragingBridge_kernel
      theta b H hBase hH)

#print axioms mixedExactCycle_exactLossAveragingBridge_kernel
#print axioms mixedExactCycle_uniformPhysicalLossUpper_kernel
#print axioms mixedExactCycle_protocolToMinimax_reduced_to_LAN_boundary

end

end QubitOracle.Paper
