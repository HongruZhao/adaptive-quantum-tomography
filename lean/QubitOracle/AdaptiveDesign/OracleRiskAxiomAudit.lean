import QubitOracle.AdaptiveDesign.OracleRiskEndpoints

/-!
Audit of the oracle-risk components already checked in Lean.
This is deliberately not an audit of a completed expected-risk theorem
for the literal three protocols: the protocol moment estimates are
proved in the revised supplement but are not yet formalized.
The general finite-record statistical bound, including adaptive score
composition, is now audited separately in GeneralOracleAxiomAudit.
-/

#print axioms QubitOracle.AdaptiveDesign.OracleMeanLoss.expectedLoss_tendsto_of_capped_and_secondMoment
#print axioms QubitOracle.AdaptiveDesign.OracleRisk.mixed_oracle_criterion
#print axioms QubitOracle.AdaptiveDesign.OracleRisk.pure_bures_covariance_constant
#print axioms QubitOracle.AdaptiveDesign.OracleRisk.pure_frobenius_covariance_constant
#print axioms QubitOracle.AdaptiveDesign.OracleRisk.pure_bures_oracle_lower
#print axioms QubitOracle.AdaptiveDesign.OracleRisk.pure_frobenius_oracle_lower
#print axioms QubitOracle.AdaptiveDesign.P1Weighted.optimal_criterion_value
#print axioms QubitOracle.AdaptiveDesign.P1Weighted.informationTarget_optimal
#print axioms QubitOracle.AdaptiveDesign.P1Weighted.p1_main
#print axioms QubitOracle.AdaptiveDesign.TangentGLS.phasePair_optimalVariance
#print axioms QubitOracle.AdaptiveDesign.TangentGLS.limitingCovariance_optimal
-- #print axioms QubitOracle.AdaptiveDesign.PVMPilotGLS.optimalVariance -- Section 5 disabled
