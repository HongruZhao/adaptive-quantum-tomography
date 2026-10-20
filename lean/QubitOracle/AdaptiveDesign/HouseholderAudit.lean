-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMBornFisherIdentification

#print axioms QubitOracle.AdaptiveDesign.ExactHouseholder.matrix_unitary
#print axioms QubitOracle.AdaptiveDesign.ExactHouseholder.matrix_firstColumn
#print axioms QubitOracle.AdaptiveDesign.ExactHouseholder.denominator_lower
#print axioms QubitOracle.AdaptiveDesign.ExactHouseholder.denominator_upper
#print axioms QubitOracle.AdaptiveDesign.PureMatrixController.controllerFrame_unitary
#print axioms QubitOracle.AdaptiveDesign.P2Adaptive.pureState_adaptive_consistency_and_information
#print axioms QubitOracle.AdaptiveDesign.PVMAdaptive.pureState_PVM_actualBorn_information

-- The actual shared controller is the displayed formula, by definition.
example (d : ℕ) (raw : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    QubitOracle.AdaptiveDesign.PureMatrixController.controllerFrame d raw =
      QubitOracle.AdaptiveDesign.ExactHouseholder.matrix
        (QubitOracle.AdaptiveDesign.PureMatrixController.nearestVector d raw).val := rfl

-/
