import QubitOracle.Paper.OneQubitMixedPolynomialOrdinaryInfidelityEndpoint

/-!
# Mixed-qubit frozen polynomial endpoint conditions

This five-field structure is a model/concentration interface.  It contains no
LAN or minimax statement and is kept in a separate module so concrete risk
upper bounds can be checked without importing the deferred lower-bound chain.
-/

namespace QubitOracle.Paper

/-- Physical and concentration hypotheses discharged by the concrete mixed
polynomial two-stage endpoint.  These are model hypotheses, not literature
lower-bound assumptions. -/
structure MixedFrozenPolynomialEndpointConditions
    (theta b : RLSVector 3) : Prop where
  positive : 0 < QubitOracle.blochNormSq theta
  interior : QubitOracle.blochNormSq theta < 1
  seed : LocalFrameSeedNonparallelAt b theta
  physical : PauliPilotPhysicalBloch theta
  hoeffding : PauliPilotConsistencyHoeffdingContracts theta physical

end QubitOracle.Paper
