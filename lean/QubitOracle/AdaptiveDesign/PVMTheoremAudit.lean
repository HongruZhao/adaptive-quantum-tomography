-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMBornFisherIdentification

#print axioms QubitOracle.AdaptiveDesign.ExplorationRate.bounded_sum_threeQuarter_ae
#print axioms QubitOracle.AdaptiveDesign.ExplorationRidge.scheduled_estimate_consistent
#print axioms QubitOracle.AdaptiveDesign.PVMGeometry.exists_oracleFrame
#print axioms QubitOracle.AdaptiveDesign.PVMGeometry.basisEffect_orthogonal
#print axioms QubitOracle.AdaptiveDesign.PVMGeometry.basisEffect_sum
#print axioms QubitOracle.AdaptiveDesign.PVMGeometry.explorationFrame_coercive
#print axioms QubitOracle.AdaptiveDesign.PVMAdaptive.rawEstimator_consistent
#print axioms QubitOracle.AdaptiveDesign.PVMAdaptive.pureState_PVM_consistency_and_information
#print axioms QubitOracle.AdaptiveDesign.PVMAdaptive.pureState_PVM_completedBatches
#print axioms QubitOracle.AdaptiveDesign.PVMAdaptive.stateEstimator_physical
#print axioms QubitOracle.AdaptiveDesign.PVMAdaptive.labChartProbability_eq_bornProbability
#print axioms QubitOracle.AdaptiveDesign.PVMAdaptive.labChartProbability_hasDerivAt
#print axioms QubitOracle.AdaptiveDesign.PVMAdaptive.actualBornFisher_eq_mixtureFisher
#print axioms QubitOracle.AdaptiveDesign.PVMAdaptive.pureState_PVM_actualBorn_information
#print axioms QubitOracle.AdaptiveDesign.PVMAdaptive.frozenController_ray_consistent

-- D=3 is not a power of two. The result elaborates at this dimension.
#check QubitOracle.AdaptiveDesign.PVMAdaptive.pureState_PVM_actualBorn_information 2 (by decide)
#check QubitOracle.AdaptiveDesign.SequentialRidgeController.unitBatch_refresh

-- Explicitly specialize the actual PVM theorem to one shot per batch.
example (truth : QubitOracle.AdaptiveDesign.PureMatrixController.PureVector 2) :=
  QubitOracle.AdaptiveDesign.PVMAdaptive.pureState_PVM_actualBorn_information
    2 (by decide) truth (fun _ => 1) (fun _ => by decide)

-/
