# Lean formalization and verification scope

The [lean/](lean/) directory contains **all 633 canonical Lean source files**, unchanged, together with the original toolchain and dependency pins. It includes the current-paper development and retained historical material. A source file being present does not by itself establish that its results match the paper, were freshly built in the latest round, or have no scientific axiom dependencies.

## Main result endpoints

| Current paper result | Lean endpoint | Source file |
|---|---|---|
| Proposition 2.1 | `QubitOracle.Paper.PureQuantumInformation.proposition_2_1` | [PureQuantumInformationProposition.lean](lean/QubitOracle/Paper/PureQuantumInformationProposition.lean) |
| Theorems 3.1 and 3.2 | `QubitOracle.Paper.MainPaperTheorem31.theorem_3_1` | [MainPaperTheorem31.lean](lean/MainPaperTheorem31.lean) |
| Proposition 4.1 | `QubitOracle.AdaptiveDesign.PhasePair.paired_conditions` and `paired_fisher_of_rankOne` | [PhasePairPOVM.lean](lean/QubitOracle/AdaptiveDesign/PhasePairPOVM.lean) |
| Theorems 4.2 and 4.3 | `QubitOracle.Paper.MainPaperTheorem42.theorem_4_2` | [MainPaperTheorem42.lean](lean/QubitOracle/Paper/MainPaperTheorem42.lean) |
| Theorem 5.1 | `QubitOracle.AdaptiveDesign.AdaptiveSingleCopyOracle.theorem_5_1` | [AdaptiveSingleCopyOracleCharts.lean](lean/QubitOracle/AdaptiveDesign/AdaptiveSingleCopyOracleCharts.lean) |
| Corollaries 5.2 and 5.3 | `QubitOracle.Paper.MainPaperMeanLosses.corollary_5_2` and `corollary_5_3` | [MainPaperMeanLosses.lean](lean/QubitOracle/Paper/MainPaperMeanLosses.lean) |

The current paper separates some conclusions that older Lean identifiers bundle together. The mixed endpoint combines consistency, information convergence, and Gaussian limits; the pure endpoint similarly contains the conclusions of both current theorems. An `Inputs` structure records assumptions, while the theorem that constructs its `Conclusions` supplies the proof. Do not infer current theorem numbering from an old filename alone.

The [paper-to-Lean guide](lean/docs/PAPER_TO_LEAN.md) and [43-group correspondence ledger](lean/docs/MAIN_PAPER_CORRESPONDENCE.json) explain the hypotheses, coordinate conventions, current labels, geometry definitions, and 211 mapped endpoints. The correspondence is not a claim that every supplementary-only lemma has its own separately audited combined endpoint.

## Preserved assumptions

The formal interfaces retain fixed finite dimension, the relevant interior mixed or pure truth, positive ridge parameters, and predetermined positive finite batches. The preliminary pure-state fit and reported corrected estimator are distinct. The adaptive lower bound uses finite complete outcome labels, parameter-independent history policies, and local unbiasedness of a coordinate estimator. Its policy is a function from the past outcome list to a POVM; finite setting randomization is represented by complete setting–readout labels.

Lean's finite-record lower-bound proof uses finite sums and decision-tree chain rules. It proves the scalar whitened-information consequence needed for the risk bound; it does not introduce the paper's sigma-field notation as a separate formal object. This is a difference of representation, not an extra hidden randomness assumption.

## Dated evidence

**The fresh 20 October 2026 run passed.** See the [new report](lean/verification/20261020/README.md), [summary](lean/verification/20261020/SUMMARY.json), [main endpoint checks](lean/verification/20261020/MAIN_ENDPOINT_CHECKS.json), and [independent statement review](lean/verification/20261020/ENDPOINT_INDEPENDENT_REVIEW.md).

| Evidence, 20 October 2026 | What passed | Boundary |
|---|---|---|
| Fresh source build | 508 project modules, the exact `MainPaper` / `MainPaperAudit` import closure; both explicit roots passed | Upstream pinned package objects reused; remaining historical sources and upstream Mathlib not rebuilt |
| Statement and axiom audit | 498 elaborated types match the saved reference exactly; all transitive sets standard-only; nine main results / seven groups / 17 mapped declarations checked | Paper-to-Lean semantic correspondence is separately reviewed |
| Kernel replay | 17 selected modules replayed successfully with `leanchecker` | Whole dependency closure not replayed |
| Freshness and preservation | Empty initial project build; source compiler traces and current project-import bindings checked; all 633 source hashes and pins unchanged | Reusing upstream caches is explicitly distinguished from project source compilation |

The [freshness receipt](lean/verification/20261020/FRESHNESS_CHECKS.json) checks actual compiler actions rather than relying only on object timestamps. A stale expected `lakefile.toml` digest first caused a local preflight stop before Lean execution. [Verification metadata alone was corrected](lean/verification/20261020/VERIFICATION_METADATA_REPAIR.json); the original failure and both hashes are retained. The build definition, Lean sources, toolchain and dependency pins were not changed.

Historical evidence remains separately dated: the [17 October native build](lean/verification/VERIFICATION_SUMMARY.json) covered 567 modules in its larger workspace; the [19 October focused check](lean/verification/theorem51_review_20261019/EXECUTION_CHECKS.json) replayed seven existing modules and inspected sixteen declarations. The inherited summary's older result grouping must not replace the current nine-result count. Neither historical receipt has been redated.

For the freshly audited selected endpoints, transitive axioms are limited to `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or scientific input axiom occurs in those selected dependency sets. The [legacy inventory](lean/verification/LEGACY_AXIOM_INVENTORY.json) lists twelve scientific axiom leaves in retained historical material outside the selected endpoint dependencies. This is not a blanket assertion about every declaration in the full source tree. Raw build logs, compiler traces, caches and proof objects remain in the local audit; portable hashes and command receipts are published.

## Reproduce the selected checks

Install [elan](https://github.com/leanprover/elan) and Git. From `lean/`:

```sh
python3 -B scripts/check_release.py
LAKE_ARTIFACT_CACHE=false python3 -B scripts/verify.py --cache --replay
```

`LAKE_ARTIFACT_CACHE=false` disables Lake artifact restoration for a new clean run; pinned upstream library objects remain usable. The actual October 20 invocation is recorded in its command receipt, and compiler traces independently establish that every project module was compiled.

The first command checks packaged file hashes only. The second fetches pinned upstream caches if requested, compiles the 508-module current-result closure, builds the explicit `MainPaper` and `MainPaperAudit` roots, inspects the 498 selected declarations and axiom sets, verifies dependency revisions, and requests replay of the 17 selected modules. It writes new timestamped results under `lean/verification/reproduction/`. A clean run rejects existing project proof objects; `--incremental` expressly permits their reuse.

For ordinary development after dependencies are installed:

```sh
lake build MainPaper MainPaperAudit
lake env lean MainPaperAudit.lean
```

The canonical `lakefile.toml` is preserved; plain `lake build` selects its original broader defaults, `AdaptiveTomography` and `MainPaperAudit`. The portable selected runner uses the explicit main-paper roots so its scope is unambiguous. It is not a command to compile every retained historical source.

The toolchain is Lean **v4.33.0-rc2**, with Mathlib commit **641fbd329d4ffb62bef83c51f54088469056bd36**. Neither caches nor compiled proof objects are shipped. First-run dependency acquisition requires network access. The [canonical source-hash inventory](lean/verification/CANONICAL_SOURCE_SHA256.json) identifies all 633 unchanged sources.

## Boundaries

The formal sources support the mapped mathematical results under their explicit hypotheses. They do not mechanically verify the Python implementation, random-number generators, empirical Monte Carlo summaries, physical hardware, runtime, bibliography, or claims of historical priority. Paper compilation and archive hashes are not substitutes for theorem correspondence or proof checking.
