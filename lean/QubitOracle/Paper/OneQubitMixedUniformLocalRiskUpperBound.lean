import QubitOracle.Paper.OneQubitMixedUniformLocalRiskCore
import QubitOracle.Paper.OneQubitConcreteLocalMinimaxReduction

/-!
# Conditional mixed-qubit local-minimax reduction

The non-LAN local-risk and probability-envelope layer is isolated in
`OneQubitMixedUniformLocalRiskCore`.  This module contains only the explicitly
deferred LAN/local-minimax transfer and its paper-facing reduction.
-/

namespace QubitOracle.Paper

/-! ## Conditional frozen-qubit minimax equality reduction -/

/-- Lower bound plus the new uniform local upper bounds.  The lower-bound fields
are exactly those supplied by `ExactLANLocalMinimaxQuadraticTransfer`; no MLE
efficiency premise is present. -/
structure MixedConcreteConditionalLocalMinimaxEqualityReduction
    {E : HajekExperimentSequence (Fin 3)}
    {truth : HajekParameter (Fin 3)}
    (C : FrozenMixedQubitLANConclusion E truth)
    (theta b : RLSVector 3) (N : ℕ → ℕ) (H : ℝ)
    (qFinal : ℕ → ℕ) : Prop where
  squaredBures_lower_and_fixed_attainment :
    FrozenTwoStageConditionalLocalMinimaxBenchmarkReduction
      E truth C.lan (buresQuadraticLimitLossData (Fin 3))
      (mixedFrozenSquaredBuresRisk theta b) (9 / 4)
  ordinaryInfidelity_lower_and_fixed_attainment :
    FrozenTwoStageConditionalLocalMinimaxBenchmarkReduction
      E truth C.lan (ordinaryInfidelityQuadraticLimitLossData (Fin 3))
      (mixedFrozenOrdinaryInfidelityRisk theta b) (9 / 4)
  squaredBures_uniform_local_upper :
    MixedUniformLocalRiskLimsupLE .squaredBures theta b N H (9 / 4)
  ordinaryInfidelity_uniform_local_upper :
    MixedUniformLocalRiskLimsupLE .ordinaryInfidelity theta b N H (9 / 4)

/-- Conditional minimax-equality reduction for the concrete frozen mixed-qubit
protocol.  Its only scientific residuals are the corresponding LAN conclusion,
the exact external local-minimax transfer, and the single explicit finite-law
uniform probability envelope. -/
theorem mixedConcreteBuresFidelityConditionalLocalMinimaxEquality_reduction
    {E : HajekExperimentSequence (Fin 3)}
    {truth : HajekParameter (Fin 3)}
    (C : FrozenMixedQubitLANConclusion E truth)
    (transfer : ExactLANLocalMinimaxQuadraticTransfer E truth C.lan)
    (theta b : RLSVector 3) (N : ℕ → ℕ) (H : ℝ)
    (qFinal : ℕ → ℕ)
    (h : MixedUniformLocalPolynomialConditions theta b N H qFinal)
    (probabilityEnvelope :
      MixedUniformLocalProbabilityEnvelope theta b N H qFinal) :
    MixedConcreteConditionalLocalMinimaxEqualityReduction
      C theta b N H qFinal := by
  refine
    { squaredBures_lower_and_fixed_attainment := ?_
      ordinaryInfidelity_lower_and_fixed_attainment := ?_
      squaredBures_uniform_local_upper := ?_
      ordinaryInfidelity_uniform_local_upper := ?_ }
  · exact mixedConcreteSquaredBuresConditionalLocalMinimaxReduction
      C transfer theta b h.toMixedFrozenPolynomialEndpointConditions
  · exact mixedConcreteOrdinaryInfidelityConditionalLocalMinimaxReduction
      C transfer theta b h.toMixedFrozenPolynomialEndpointConditions
  · exact mixedUniformLocalSquaredBuresRisk_limsup_le_nine_fourths
      theta b N H qFinal h probabilityEnvelope
  · exact mixedUniformLocalOrdinaryInfidelityRisk_limsup_le_nine_fourths
      theta b N H qFinal h probabilityEnvelope

namespace Label

/-- Paper-facing honest label for the frozen mixed-qubit local-minimax equality
reduction.  It retains the exact LAN/literature/probability boundaries. -/
theorem thm_mixed_concrete_local_minimax_equality_qubit_reduction
    {E : HajekExperimentSequence (Fin 3)}
    {truth : HajekParameter (Fin 3)}
    (C : FrozenMixedQubitLANConclusion E truth)
    (transfer : ExactLANLocalMinimaxQuadraticTransfer E truth C.lan)
    (theta b : RLSVector 3) (N : ℕ → ℕ) (H : ℝ)
    (qFinal : ℕ → ℕ)
    (h : MixedUniformLocalPolynomialConditions theta b N H qFinal)
    (probabilityEnvelope :
      MixedUniformLocalProbabilityEnvelope theta b N H qFinal) :
    MixedConcreteConditionalLocalMinimaxEqualityReduction
      C theta b N H qFinal :=
  mixedConcreteBuresFidelityConditionalLocalMinimaxEquality_reduction
    C transfer theta b N H qFinal h probabilityEnvelope

end Label

end QubitOracle.Paper
