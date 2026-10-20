import QubitOracle.AdaptiveDesign.TangentGLSOptimalVariance

/-! Exact endpoint audit for the final all-record estimator covariance.
The principal queries below audit proofs, not merely the proposition's type.
Every queried endpoint now uses only Lean foundational axioms; the bounded
adaptive CLT is proved by characteristic functions. -/
open QubitOracle QubitOracle.Paper QubitOracle.AdaptiveDesign
open PureMatrixController
open scoped BigOperators Topology
noncomputable section

#print axioms TangentGLS.recordCorrection_minimizes
#print axioms TangentGLS.actualEstimatedState_physical
#print axioms TangentGLS.fittedScore_exact_expansion
#print axioms TangentGLS.updatedState_remainder_bound_global
#print axioms TangentGLS.tangentProjector_lipschitz
#print axioms TangentGLS.recordInformation_difference
#print axioms ProbabilityCalculus.of_eventual_ae_bound
#print axioms FiniteHistoryStatistics.actualStatistic_stronglyMeasurable
#print axioms TangentGLS.actualPreliminaryError_quarterRate
#print axioms TangentGLS.actual_ambientScore_rootTight
#print axioms TangentGLS.actual_ambientDerivative_error_rootRate
#print axioms TangentGLS.actualWeightRemainder_rootRate
#print axioms TangentGLS.actual_fittedInformation_tendsto
#print axioms TangentGLS.actualInformationError_zero
#print axioms TangentGLS.actual_score_eq_sum
#print axioms TangentGLS.actual_derivative_eq_sum
#print axioms TangentGLS.actualLinearError_bound
#print axioms TangentGLS.actualLinearError_rootRate
#print axioms TangentGLS.actualDelta_quarterRate
#print axioms TangentGLS.actualProjectorError_linearization
#print axioms EfficientBornScoreCLT.fullScore_clt
#print axioms TangentGLS.actual_coordinates_minus_score_zero
#print axioms TangentGLS.optimalVariance
#print axioms TangentGLS.phasePair_optimalVariance
#print axioms TangentGLS.limitingCovariance_optimal

#check TangentGLS.optimalVariance
#check TangentGLS.phasePair_optimalVariance

namespace TangentGLSOptimalVarianceAudit
variable {O : Type} [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]

/-- A dimension-three specialization of the actual phase-pair estimator,
with a unit-shot batch schedule and explicit positive ridge constants. -/
theorem qutrit_final_estimator_optimalVariance
    (P : FinitePOVM (Fin 3) O) (hI : GeneralPOVM.Identifying P) (hp : GeneralPOVM.Regular P)
    (hR : PhasePair.RankOne P) (truth : PureVector 2) :
    TangentGLS.OptimalVarianceStatement (PhasePair.paired P) (PhasePair.paired_identifying P hI)
      (PhasePair.paired_regular P hp) 2 1 (by norm_num) (by norm_num) (fun _ => 1) truth :=
  TangentGLS.phasePair_optimalVariance P hI hp hR truth 2 1 (by norm_num) (by norm_num)
    (fun _ => 1) (fun _ => by norm_num)

#print axioms qutrit_final_estimator_optimalVariance
#check qutrit_final_estimator_optimalVariance
end TangentGLSOptimalVarianceAudit
end
