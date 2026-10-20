import QubitOracle.AdaptiveDesign.GeneralWeightedOracle

/-! Exact theorem and transitive dependency audit for the general oracle
bound. Protocol-specific fourth moments and expected physical loss are
separate from this finite-record statistical theorem. -/

open QubitOracle.AdaptiveDesign.FiniteRegularOracle

#check RegularModel
#check RegularModel.ofNeighborhood
#check RegularModel.LocallyUnbiased
#check adaptiveExperiment
#check general_adaptive_oracle_qfi
#print axioms RegularModel.derivative_eq_zero_of_mass_eq_zero
#print axioms RegularModel.score_centered
#print axioms RegularModel.score_identity
#print axioms RegularModel.weighted_score_bound
#print axioms RegularModel.bind_scoreEnergy
#print axioms adaptive_scoreEnergy_le
#print axioms RegularModel.general_weighted_oracle
#print axioms general_adaptive_oracle_qfi
