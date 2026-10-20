import QubitOracle.AdaptiveDesign.P2AdaptiveTheorem
import QubitOracle.AdaptiveDesign.GlobalPFSICBorn

#print axioms QubitOracle.AdaptiveDesign.P2Adaptive.stateEstimator_physical
#print axioms QubitOracle.AdaptiveDesign.P2Adaptive.rawEstimator_consistent
#print axioms QubitOracle.AdaptiveDesign.P2Adaptive.pureState_adaptive_consistency_and_information
#print axioms QubitOracle.AdaptiveDesign.P2Adaptive.pureState_adaptive_completedBatches
#print axioms QubitOracle.AdaptiveDesign.GlobalPFSICBorn.bornProbability_eq_trace
#print axioms QubitOracle.AdaptiveDesign.GlobalPFSIC.genericBornProbability_hasDerivAt_zero

-- Explicit qutrit specialization: the theorem is not confined to qubits.
#check QubitOracle.AdaptiveDesign.P2Adaptive.pureState_adaptive_consistency_and_information 2 (by decide)
-- Explicit one-shot-per-batch schedule.
#check QubitOracle.AdaptiveDesign.SequentialRidgeController.unitBatch_refresh
