import QubitOracle.Paper.OneQubitMixedPolynomialFiniteRNClosure
import QubitOracle.Paper.MixedExactCycleProtocolToMinimaxClosureStatus
import QubitOracle.Paper.MathlibHoeffding1963Bridge
import QubitOracle.Paper.Beran1995UnifiedTransfer

/-!
# Concrete mixed-qubit protocol-to-minimax assembly

This module reduces the exact two-stage mixed-qubit theorem from the concrete
finite Born experiment to one explicit vector local-minimax transfer premise.

Every model-specific or computational ingredient is proved in Lean.  The
legacy shrinking-neighborhood functional used by
`ExactLANLocalMinimaxQuadraticTransfer` is not identified here with Beran's
source-faithful growing-ball minimax functional; consequently the transfer is
an explicit theorem argument rather than a field hidden in the Beran atom.

Citation: Rudolf Beran, "The Role of Hajek's Convolution Theorem in
Statistical Theory", Kybernetika 31 (1995), Theorem 4.1, pp. 221--237,
https://www.kybernetika.cz/content/1995/3/221/paper.pdf

The active headline lower bounds instead use the source-faithful Beran wrapper
in `AdaptivePolicyBeranTransfer`.  The concrete upper-bound calculations in
this module remain kernel-proved.
-/

namespace QubitOracle.Paper

noncomputable section

/-! ## Kernel-checked concrete constructors -/

/-- The concrete mixed-qubit endpoint assumptions, with both Hoeffding
contracts discharged from Mathlib rather than postulated. -/
def mixedPolynomialConcreteEndpointConditions_mathlib
    (theta b : RLSVector 3)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    MixedFrozenPolynomialEndpointConditions theta b where
  positive := hTruth.1
  interior := hTruth.2
  seed := hSeed
  physical := mixedNonzeroInterior_pauliPilotPhysical theta hTruth
  hoeffding := pauliPilotConsistencyHoeffdingContracts_mathlib theta
    (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)

/-- Concrete polynomial two-stage LAN certificate with its finite pilot
Hoeffding premise discharged by Mathlib. -/
noncomputable def constructConcreteFrozenMixedQubitLANConclusion_mathlib
    (theta b : Fin 3 -> Real)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    FrozenMixedQubitLANConclusion
      (mixedPolynomialHajekExperiment theta b hTruth) 0 :=
  constructConcreteFrozenMixedQubitLANConclusion theta b hTruth hSeed
    (mixedPolynomialFinitePilotHoeffdingContracts_mathlib theta
      (mixedNonzeroInterior_pauliPilotPhysical theta hTruth))

/-- The exact remaining LAN/minimax boundary is inhabited for the concrete
mixed-qubit experiment.  The LAN field is the proved protocol theorem; only
the `lanToMinimax` field uses Beran's cited transfer. -/
noncomputable def mixedPolynomialConcreteExactCycleLANMinimaxBoundary
    (theta b : Fin 3 -> Real)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (transfer : ExactLANLocalMinimaxQuadraticTransfer
      (mixedPolynomialHajekExperiment theta b hTruth) 0
      (constructConcreteFrozenMixedQubitLANConclusion_mathlib
        theta b hTruth hSeed).lan) :
    MixedExactCycleLANMinimaxBoundary
      (E := mixedPolynomialHajekExperiment theta b hTruth)
      (truth := 0) := by
  let C := constructConcreteFrozenMixedQubitLANConclusion_mathlib
    theta b hTruth hSeed
  exact
    { lanCertificate := C
      lanToMinimax := transfer }

/-- End-to-end concrete mixed-qubit exact-cycle theorem.

For every finite local radius `H`, the same concrete two-stage protocol has
the all-estimator LAN lower bound and the matching uniform local upper bounds
for squared Bures loss and ordinary infidelity, both with constant `9/4`.
The result is conditional only on the cited Hall--Heyde martingale CLT and
Beran LAN-to-minimax theorem, besides Lean's foundational axioms. -/
theorem mixedPolynomialConcrete_protocolToMinimax
    (theta b : RLSVector 3) (H : Real)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (transfer : ExactLANLocalMinimaxQuadraticTransfer
      (mixedPolynomialHajekExperiment theta b hTruth) 0
      (constructConcreteFrozenMixedQubitLANConclusion_mathlib
        theta b hTruth hSeed).lan)
    (hH : 0 <= H) :
    MixedConcreteConditionalLocalMinimaxEqualityReduction
      (constructConcreteFrozenMixedQubitLANConclusion_mathlib
        theta b hTruth hSeed)
      theta b mixedUniformLocalExactCycleN H
      mixedUniformLocalExactCycleQFinal := by
  exact mixedExactCycle_protocolToMinimax_reduced_to_LAN_boundary
    (mixedPolynomialConcreteExactCycleLANMinimaxBoundary
      theta b hTruth hSeed transfer)
    theta b H
    (mixedPolynomialConcreteEndpointConditions_mathlib
      theta b hTruth hSeed)
    hH

end

end QubitOracle.Paper
