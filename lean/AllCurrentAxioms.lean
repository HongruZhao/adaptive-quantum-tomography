import AdaptiveTomography
import CurrentPaperStatementAudit
import QubitOracle.Paper.ProjectiveStateGeometry
import QubitOracle.AdaptiveDesign.ProjectiveProjectorEquivalence
import QubitOracle.Paper.InformationDefinitions
import QubitOracle.Paper.InformationSmoothness
import QubitOracle.Paper.SLDLinearAlgebra
import QubitOracle.Paper.LiteralMatrixCalculus
import QubitOracle.AdaptiveDesign.InformationGeometryBridge

/-! Fresh transitive axiom receipts for every current project declaration.
This includes support results, not only hand-selected paper endpoints.
The three standard logical axioms are the only permitted dependencies.
-/
open Lean Elab Command in
elab "#audit_current_project_axioms" : command => do
  let env ← getEnv
  let names := env.constants.toList.map Prod.fst |>.filter fun n =>
    n.toString.startsWith "QubitOracle." || n.toString.contains ".QubitOracle."
  let names := names.toArray.qsort Name.quickLt
  for n in names do
    let axioms ← Lean.collectAxioms n
    logInfo m!"AXIOM_RECEIPT {n} {axioms.toList}"
    let unsupported := axioms.filter fun a =>
      a != `propext && a != `Classical.choice && a != `Quot.sound
    unless unsupported.isEmpty do
      logInfo m!"EXTERNAL_AXIOM_DEPENDENCY {n} {unsupported.toList}"
  logInfo m!"AXIOM_RECEIPT_TOTAL {names.size}"

#audit_current_project_axioms
