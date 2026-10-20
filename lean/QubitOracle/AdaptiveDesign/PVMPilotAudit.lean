-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMOptimalVariance
import QubitOracle.AdaptiveDesign.PVMPilotPureMeanSquare
import QubitOracle.AdaptiveDesign.PVMPilotBornFisherIdentification
import QubitOracle.AdaptiveDesign.PVMWeakPowerSchedule

/-! Audit of the two improved-budget PVM theorems. Assertions query actual
proofs and their transitive axioms. Every queried endpoint,
including the direct CLT and Gaussian estimator limit, must use foundations only. -/
open QubitOracle QubitOracle.Paper QubitOracle.AdaptiveDesign
open PureMatrixController
open scoped BigOperators Topology
noncomputable section

#print axioms FiniteAdaptiveCharacteristic.bounded_response_scalar_clt
#print axioms FiniteAdaptiveCharacteristic.vector_clt_of_secondMoment_limit
#print axioms PVMGeneralGeometry.identifies_of_spanning_generators
#print axioms PVMPilotSchedule.powerSchedule
#print axioms PVMPilotSchedule.powerSchedule_oneStep
#print axioms PVMPilotAdaptive.rawEstimator_consistent
#print axioms PVMPilotAdaptive.rawEstimator_meanSquare
#print axioms PVMPilotGLS.preliminary_meanSquare
#print axioms PVMPilotGLS.actualPreliminaryError_quarterRate
#print axioms PVMPilotAdaptive.pureState_PVM_actualBorn_information
#print axioms PVMPilotAdaptive.frozenController_ray_consistent
#print axioms PVMPilotAdaptive.pureState_PVM_completedBatches
#print axioms PVMPilotGLS.actualDelta_minimizes
#print axioms PVMPilotGLS.actualEstimatedState_physical
#print axioms PVMPilotGLS.one_step_error_equation
#print axioms PVMPilotGLS.updated_error_bound
#print axioms PVMPilotGLS.actual_moment_limits
#print axioms PVMPilotGLS.fittedGram_limit
#print axioms PVMPilotGLS.corrected_consistent
#print axioms PVMPilotGLS.projectorError_linearization
#print axioms PVMPilotGLS.fullScore_clt
#print axioms PVMPilotGLS.optimalVariance
#print axioms TangentGLS.limitingCovariance_optimal

#check PVMPilotAdaptive.pureState_PVM_actualBorn_information
#check PVMPilotAdaptive.rawEstimator_meanSquare
#check PVMPilotGLS.corrected_consistent
#check PVMPilotGLS.optimalVariance

namespace PVMPilotAudit
/-- A concrete exponent excluded by the earlier alpha < 1/4 sufficient
condition, but included in the new efficiency theorem. -/
theorem thirdPower_budget :
    @PVMPilotSchedule.OneStepBudget
      (PVMPilotSchedule.powerSchedule (1/3) (by norm_num) (by norm_num)) :=
  PVMPilotSchedule.powerSchedule_oneStep (1/3) (by norm_num) (by norm_num)
#print axioms thirdPower_budget
end PVMPilotAudit
end

-/
