import QubitOracle.AdaptiveDesign.GeneralPOVMBorn
import QubitOracle.AdaptiveDesign.GeneralPOVMExample

-- Actual general hypotheses and conclusion, including the physical probability law.
#print QubitOracle.AdaptiveDesign.GeneralPOVM.Identifying
#print QubitOracle.AdaptiveDesign.GeneralPOVM.Regular
#print QubitOracle.AdaptiveDesign.GeneralPOVM.FisherSymmetric
#check QubitOracle.AdaptiveDesign.GeneralPOVM.adaptive_consistency
#check QubitOracle.AdaptiveDesign.GeneralPOVM.adaptive_actualBorn_information
#check QubitOracle.AdaptiveDesign.GeneralPOVM.adaptive_completedBatches

#print axioms QubitOracle.AdaptiveDesign.GeneralPOVM.effect_complete
#print axioms QubitOracle.AdaptiveDesign.GeneralPOVM.bornProbability_nonnegative
#print axioms QubitOracle.AdaptiveDesign.GeneralPOVM.bornProbability_sum
#print axioms QubitOracle.AdaptiveDesign.GeneralPOVM.responseVector_mean
#print axioms QubitOracle.AdaptiveDesign.GeneralPOVM.responseInnovation_bound
#print axioms QubitOracle.AdaptiveDesign.GeneralPOVM.exists_uniform_regression_coercivity
#print axioms QubitOracle.AdaptiveDesign.GeneralPOVM.realify_orthogonal
#print axioms QubitOracle.AdaptiveDesign.GeneralPOVM.gradient_of_overlap_one
#print axioms QubitOracle.AdaptiveDesign.GeneralPOVM.fisher_of_overlap_one
#print axioms QubitOracle.AdaptiveDesign.GeneralPOVM.fisher_generalTruth_tendsto
#print axioms QubitOracle.AdaptiveDesign.GeneralPOVM.stateEstimator_physical
#print axioms QubitOracle.AdaptiveDesign.GeneralPOVM.measurementFrame_eq_frozenController
#print axioms QubitOracle.AdaptiveDesign.GeneralPOVM.rawEstimator_consistent
#print axioms QubitOracle.AdaptiveDesign.GeneralPOVM.adaptive_consistency
#print axioms QubitOracle.AdaptiveDesign.GeneralPOVM.adaptive_consistency_and_information
#print axioms QubitOracle.AdaptiveDesign.GeneralPOVM.adaptive_completedBatches
#print axioms QubitOracle.AdaptiveDesign.GeneralPOVM.quadratic_directionalState_hasDerivAt_zero
#print axioms QubitOracle.AdaptiveDesign.GeneralPOVM.labChartProbability_eq_bornProbability
#print axioms QubitOracle.AdaptiveDesign.GeneralPOVM.labChartProbability_hasDerivAt_zero
#print axioms QubitOracle.AdaptiveDesign.GeneralPOVM.actualBornFisher_eq_fisher
#print axioms QubitOracle.AdaptiveDesign.GeneralPOVM.designFisher_eq_actualBornFisher
#print axioms QubitOracle.AdaptiveDesign.GeneralPOVM.adaptive_actualBorn_information
#print axioms QubitOracle.AdaptiveDesign.GeneralPOVM.explicit_satisfies_conditions

-- A non-qubit D=3 example, with a ridge parameter different from the old value one.
#check QubitOracle.AdaptiveDesign.GeneralPOVM.adaptive_actualBorn_information
  (QubitOracle.AdaptiveDesign.GlobalPFSIC.measurementPOVM 2 (by decide))
  (QubitOracle.AdaptiveDesign.GeneralPOVM.explicit_identifying 2 (by decide))
  2 (by norm_num)
  (QubitOracle.AdaptiveDesign.GeneralPOVM.explicit_regular 2 (by decide))
  (QubitOracle.AdaptiveDesign.GeneralPOVM.explicit_fisherSymmetric 2 (by decide))

-- Instantiate the physical result itself with one observation per batch.
#check fun truth : QubitOracle.AdaptiveDesign.PureMatrixController.PureVector 2 =>
  QubitOracle.AdaptiveDesign.GeneralPOVM.adaptive_actualBorn_information
    (QubitOracle.AdaptiveDesign.GlobalPFSIC.measurementPOVM 2 (by decide))
    (QubitOracle.AdaptiveDesign.GeneralPOVM.explicit_identifying 2 (by decide))
    2 (by norm_num)
    (QubitOracle.AdaptiveDesign.GeneralPOVM.explicit_regular 2 (by decide))
    (QubitOracle.AdaptiveDesign.GeneralPOVM.explicit_fisherSymmetric 2 (by decide))
    truth (fun _ => 1) (by intro j; norm_num)
