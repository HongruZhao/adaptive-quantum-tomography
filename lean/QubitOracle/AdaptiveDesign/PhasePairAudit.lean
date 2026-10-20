import QubitOracle.AdaptiveDesign.PhasePairAdaptive

#print QubitOracle.AdaptiveDesign.PhasePair.RankOne
#check QubitOracle.AdaptiveDesign.PhasePair.paired_conditions
#check QubitOracle.AdaptiveDesign.PhasePair.adaptive_actualBorn_information

#print axioms QubitOracle.AdaptiveDesign.PhasePair.gate_unitary
#print axioms QubitOracle.AdaptiveDesign.PhasePair.gate_adjoint_unitary
#print axioms QubitOracle.AdaptiveDesign.PhasePair.gate_adjoint_eq_globalPhase_complement
#print axioms QubitOracle.AdaptiveDesign.PhasePair.gate_adjoint_effect_entry
#print axioms QubitOracle.AdaptiveDesign.PhasePair.paired
#print axioms QubitOracle.AdaptiveDesign.PhasePair.paired_effect_false
#print axioms QubitOracle.AdaptiveDesign.PhasePair.paired_effect_true
#print axioms QubitOracle.AdaptiveDesign.PhasePair.paired_referenceProbability
#print axioms QubitOracle.AdaptiveDesign.PhasePair.paired_identifying
#print axioms QubitOracle.AdaptiveDesign.PhasePair.paired_regular
#print axioms QubitOracle.AdaptiveDesign.PhasePair.paired_fisher_term
#print axioms QubitOracle.AdaptiveDesign.PhasePair.tail_projector_sum
#print axioms QubitOracle.AdaptiveDesign.PhasePair.paired_fisher_of_rankOne
#print axioms QubitOracle.AdaptiveDesign.PhasePair.paired_conditions
#print axioms QubitOracle.AdaptiveDesign.PhasePair.adaptive_actualBorn_information

-- Elaborate the physical theorem in D=3, with an arbitrary rank-one reference POVM,
-- ridge two, and one observation per batch. No special library is supplied.
open QubitOracle QubitOracle.Paper QubitOracle.AdaptiveDesign
open GeneralPOVM PhasePair PureMatrixController
#check fun {O : Type} [Fintype O] [MeasurableSpace O]
    [MeasurableSingletonClass O] [Nonempty O]
    (P : FinitePOVM (Fin 3) O) (hI : Identifying P) (hp : Regular P)
    (hR : PhasePair.RankOne P) (truth : PureVector 2) =>
  PhasePair.adaptive_actualBorn_information P hI hp hR 2 (by norm_num)
    truth (fun _ => 1) (by intro j; norm_num)
