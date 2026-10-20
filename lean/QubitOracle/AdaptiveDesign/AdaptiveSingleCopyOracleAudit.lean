import QubitOracle.AdaptiveDesign.AdaptiveSingleCopyOracleCharts

/-! Native statement and transitive-axiom audit for revised Theorem 5.1.
The general classical helper can retain a budget argument; the quantum
endpoints below derive that argument from the physical POVM policy. -/

open QubitOracle.AdaptiveDesign.AdaptiveSingleCopyOracle
open QubitOracle.AdaptiveDesign.FiniteRegularOracle

#print QuantumModel
#print PureChartData
#print RegularModel
#print RegularModel.LocallyUnbiased
#print RegularModel.quadraticRisk
#print oracleConstant
#check theorem_5_1_mixed
#check theorem_5_1_pure_normalized
#check theorem_5_1_pure
#check theorem_5_1

#print axioms mixedModel_information
#print axioms mixedModel_gillMassar
#print axioms mixed_quantumInformation
#print axioms pureModel_derivative
#print axioms pureModel_information
#print axioms pureModel_gillMassar
#print axioms PureChartData.quantumInformation_entry
#print axioms PureChartData.quantumInformation_from_derivative
#print axioms PureChartData.quantumInformation_posDef
#print axioms PureChartData.model_information
#print axioms PureChartData.model_gillMassar
#print axioms normalizedPureChart
#print axioms theorem_5_1_mixed
#print axioms theorem_5_1_pure_normalized
#print axioms theorem_5_1_pure
#print axioms theorem_5_1

open Lean Elab Command Meta in
elab "#audit_theorem_5_1_declarations" : command => do
  let env ← getEnv
  let names := env.constants.toList.map Prod.fst |>.filter fun n =>
    n.toString.startsWith "QubitOracle.AdaptiveDesign.AdaptiveSingleCopyOracle."
  let names := names.toArray.qsort Name.quickLt
  let statementNames : List Name := [
    `QubitOracle.AdaptiveDesign.AdaptiveSingleCopyOracle.theorem_5_1,
    `QubitOracle.AdaptiveDesign.AdaptiveSingleCopyOracle.theorem_5_1_mixed,
    `QubitOracle.AdaptiveDesign.AdaptiveSingleCopyOracle.theorem_5_1_pure,
    `QubitOracle.AdaptiveDesign.AdaptiveSingleCopyOracle.theorem_5_1_pure_normalized,
    `QubitOracle.AdaptiveDesign.AdaptiveSingleCopyOracle.mixedModel_information,
    `QubitOracle.AdaptiveDesign.AdaptiveSingleCopyOracle.mixedModel_gillMassar,
    `QubitOracle.AdaptiveDesign.AdaptiveSingleCopyOracle.mixed_quantumInformation,
    `QubitOracle.AdaptiveDesign.AdaptiveSingleCopyOracle.pureModel_information,
    `QubitOracle.AdaptiveDesign.AdaptiveSingleCopyOracle.pureModel_gillMassar,
    `QubitOracle.AdaptiveDesign.AdaptiveSingleCopyOracle.PureChartData.quantumInformation_from_derivative,
    `QubitOracle.AdaptiveDesign.AdaptiveSingleCopyOracle.PureChartData.quantumInformation_posDef,
    `QubitOracle.AdaptiveDesign.AdaptiveSingleCopyOracle.PureChartData.model_information,
    `QubitOracle.AdaptiveDesign.AdaptiveSingleCopyOracle.PureChartData.model_gillMassar]
  for n in names do
    match env.find? n with
    | none => throwError m!"MISSING_THEOREM_51_DECLARATION {n}"
    | some c =>
      if n ∈ statementNames then
        let t ← liftTermElabM <| withOptions (fun opts =>
          opts.setBool `pp.universes true |>.setBool `pp.explicit true |>.setBool `pp.fullNames true
            |>.set `pp.maxSteps (200000 : Nat)) <| ppExpr c.type
        logInfo m!"THEOREM_51_STATEMENT_BEGIN {n}\n{t}\nTHEOREM_51_STATEMENT_END"
      let axioms ← Lean.collectAxioms n
      logInfo m!"THEOREM_51_AXIOMS {n} {axioms.toList}"
      let unsupported := axioms.filter fun ax =>
        ax != `propext && ax != `Classical.choice && ax != `Quot.sound
      unless unsupported.isEmpty do
        throwError m!"UNSUPPORTED_THEOREM_51_AXIOMS {n} {unsupported.toList}"
  logInfo m!"THEOREM_51_DECLARATION_TOTAL {names.size}"
  logInfo m!"THEOREM_51_STATEMENT_TOTAL {statementNames.length}"

#audit_theorem_5_1_declarations
