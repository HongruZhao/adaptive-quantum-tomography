# Lean formalization and verification scope

The [lean/](lean/) directory contains the proof modules needed by the checked main results and the documented supplementary results, together with their dependency closure. Its default build checks `MainPaperAudit` and `SupplementAudit`. The distributed tree contains no scientific input axioms or unfinished proof placeholders.

## Main endpoints

| Printed result | Lean endpoint | Source |
|---|---|---|
| Proposition 2.1 | `PureQuantumInformation.proposition_2_1` | [PureQuantumInformationProposition.lean](lean/QubitOracle/Paper/PureQuantumInformationProposition.lean) |
| Theorems 3.1 and 3.2 | `MainPaperTheorem31.theorem_3_1` | [MainPaperTheorem31.lean](lean/MainPaperTheorem31.lean) |
| Proposition 4.1 | `PhasePair.paired_conditions`, `paired_fisher_of_rankOne` | [PhasePairPOVM.lean](lean/QubitOracle/AdaptiveDesign/PhasePairPOVM.lean) |
| Theorems 4.2 and 4.3 | `MainPaperTheorem42.theorem_4_2` | [MainPaperTheorem42.lean](lean/QubitOracle/Paper/MainPaperTheorem42.lean) |
| Theorem 5.1 | `AdaptiveSingleCopyOracle.theorem_5_1` | [AdaptiveSingleCopyOracleCharts.lean](lean/QubitOracle/AdaptiveDesign/AdaptiveSingleCopyOracleCharts.lean) |
| Corollaries 5.2 and 5.3 | `MainPaperMeanLosses.corollary_5_2`, `corollary_5_3` | [MainPaperMeanLosses.lean](lean/QubitOracle/Paper/MainPaperMeanLosses.lean) |

Namespace prefixes are given in [MAIN_RESULTS.md](MAIN_RESULTS.md), which reproduces all nine printed statements. Two endpoints each combine a pair of printed theorems. Their `Inputs` structures contain assumptions; their `Conclusions` structures are constructed by the proved theorem. The [correspondence ledger](lean/docs/MAIN_PAPER_CORRESPONDENCE.json) gives 43 claim groups and 211 mapped declarations, all included in the 498-entry main audit.

## Assumptions and representation

The interfaces retain fixed finite dimension, an interior mixed or pure truth, positive ridge parameters and predetermined positive finite batches. The preliminary pure-state fit and corrected estimate are distinct. The adaptive lower bound uses finite complete outcome labels, a parameter-independent history policy and local unbiasedness of a coordinate estimator.

The policy maps the past outcome list to a POVM. A fixed policy determines the selected measurement from the history; finite setting randomization is incorporated in the complete outcome label. Lean uses finite decision trees, sums and chain rules for this result. The paper's sigma-fields are not introduced as separate objects in that finite-record proof. No Gaussian limit, expected-loss limit or desired information conclusion is supplied as an assumption of the main combined endpoints.

## Current evidence

The official checks are in the [20 October 2026 report](lean/verification/20261020/README.md). They record every distributed project module's source compilation, 498 main and 138 supplementary declaration checks (overlapping inventories), the transitive axiom audit of all retained mathematical declarations, and the exact module list independently replayed with `leanchecker`. Upstream pinned package objects are reused; rebuilding Mathlib is not claimed.

All retained mathematical declarations have only `propext`, `Classical.choice` and `Quot.sound` in their transitive axiom dependencies. The audit rejects `sorryAx` and any scientific axiom. Main declaration types match the saved reference exactly; supporting declaration types and retained proof blocks are checked separately.

The [supplementary coverage table](SUPPLEMENT_RESULTS.md) records the current statement scope. Lemmas S4.1, S4.2 and S6.2 are specialized to the fixed selection, almost-sure consistency and actual adaptive procedure already represented by Lean. S6.2 uses normalized normal-operator convergence and direct score linearization. The [scope audit](lean/verification/20261020/SUPPLEMENT_SCOPE_ALIGNMENT.md) checks their applications and seven existing declaration types/axiom sets. No Lean code, main theorem statement or algorithm changed. Component-based correspondence is distinguished from a single combined endpoint; complete mechanical verification of the entire supplementary text is not claimed.

## Reproduce

```sh
cd lean
python3 -B scripts/check_release.py
LAKE_ARTIFACT_CACHE=false python3 -B scripts/verify.py --cache --replay
```

A fresh run rejects existing project proof objects. `--incremental` permits their reuse and records that choice. The verifier checks the exact dependency revisions, declaration types, whole retained mathematical axiom set, and requested replay list. It writes timestamped evidence under `verification/reproduction/`.

The toolchain is Lean **v4.33.0-rc2**, with Mathlib commit **641fbd329d4ffb62bef83c51f54088469056bd36**. The theorem statements and hypotheses are preserved. Import cleanup and removal of unused declarations do not establish additional mathematical claims.

Lean verification does not cover the Python implementation, random-number generators, physical apparatus, runtime, bibliography or priority claims. The repository and prepared Lean-only Zenodo archive require explicit author approval before public release.
