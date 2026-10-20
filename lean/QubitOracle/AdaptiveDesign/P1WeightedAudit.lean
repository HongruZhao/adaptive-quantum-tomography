import QubitOracle.AdaptiveDesign.P1WeightedEndpoints

/-! Public P1 audit. These commands inspect the transitive dependencies of
the actual estimator theorems, not just the absence of holes in their wrappers. -/
namespace QubitOracle.AdaptiveDesign.P1Weighted

#check p1_main Loss.bures
#check p1_main Loss.frobenius
#check positive_batches_consistency_information
#check positive_batches_normal
#check controller_normal
#check completed_batches_normal
#check informationTarget_optimal

#print axioms probability_sum
#print axioms pathState_gram
#print axioms pathState_rhs
#print axioms actual_weight_floor
#print axioms normal_error
#print axioms estimate_consistent
#print axioms positive_batches_consistency_information
#print axioms physical_state_consistent
#print axioms noise_current_tendsto
#print axioms observedGram_tendsto
#print axioms covariance_eq_information_inv
#print axioms inverse_sandwich
#print axioms informationTarget_optimal
#print axioms optimal_criterion_value
#print axioms covariance_at_center
#print axioms frobeniusTarget_value
#print axioms P1.mixedBuresTarget_optimal_over_finite_qubitPOVM
#print axioms characteristicSum_succ
#print axioms characteristicSum_bound
#print axioms bounded_response_scalar_clt
#print axioms bounded_response_vector_clt
#print axioms influenceSum_clt
#print axioms estimate_normal
#print axioms positive_batches_normal
#print axioms controller_normal
#print axioms completed_batches_normal
#print axioms p1_main

end QubitOracle.AdaptiveDesign.P1Weighted
