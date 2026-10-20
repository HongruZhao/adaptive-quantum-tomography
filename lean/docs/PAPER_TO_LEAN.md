# Current paper-to-Lean map

This guide uses the current main paper and its Appendices A-B, together with the two-part supplement. The nine main results below are supported by existing combined endpoints; no Lean proof was renamed or changed.

## Main results

| Current paper result | Existing Lean endpoint or clauses | Written proof |
|---|---|---|
| Proposition 2.1 | `QubitOracle.Paper.PureQuantumInformation.proposition_2_1`; proposition_2_1 | Supplement S2.1 |
| Theorem 3.1 | `QubitOracle.Paper.MainPaperTheorem31.theorem_3_1`; theorem_3_1: consistency and information clauses | Supplement S1.2 |
| Theorem 3.2 | `QubitOracle.Paper.MainPaperTheorem31.theorem_3_1`; theorem_3_1: Gaussian-limit clauses | Supplement S1.2 |
| Proposition 4.1 | `QubitOracle.AdaptiveDesign.PhasePair.paired_conditions`; paired_conditions and paired_fisher_of_rankOne | Supplement S2.4 |
| Theorem 4.2 | `QubitOracle.Paper.MainPaperTheorem42.theorem_4_2`; theorem_4_2: consistency, alignment and information fields | Supplement S1.3 |
| Theorem 4.3 | `QubitOracle.Paper.MainPaperTheorem42.theorem_4_2`; theorem_4_2: rate and Gaussian-limit fields | Supplement S1.3 |
| Theorem 5.1 | `QubitOracle.AdaptiveDesign.AdaptiveSingleCopyOracle.theorem_5_1`; theorem_5_1 | Supplement S1.1 |
| Corollary 5.2 | `QubitOracle.Paper.MainPaperMeanLosses.corollary_5_2`; corollary_5_2 | Supplement S1.4 |
| Corollary 5.3 | `QubitOracle.Paper.MainPaperMeanLosses.corollary_5_3`; corollary_5_3 | Supplement S1.4 |

## How the combined statements split

- **Theorems 3.1 and 3.2:** the first conjunction of `MainPaperTheorem31.theorem_3_1` gives consistency and information convergence; the following distributional clauses give the raw and physical-output Gaussian limits. The same theorem treats both specified allocations and positive finite predetermined batches.
- **Theorem 4.2:** `MainPaperTheorem42.theorem_4_2` proves `Conclusions.raw_consistent`, `preliminary_consistent`, `corrected_consistent`, `alignment_consistent`, `conditional_information` and `average_information`.
- **Theorem 4.3:** the same endpoint proves `raw_root_rate`, `preliminary_root_rate`, `chart_normality`, `chart_covariance`, `chart_sld_information` and the ambient Gaussian, centering, tangent-support and covariance fields. `Inputs` contains apparatus, positive ridge parameters and batch assumptions; the limit statements are proved output fields.

The public namespace of the mixed endpoint is `QubitOracle.Paper.MainPaperTheorem31`, although its file is [MainPaperTheorem31.lean](../MainPaperTheorem31.lean). The pure combined endpoint is in [MainPaperTheorem42.lean](../QubitOracle/Paper/MainPaperTheorem42.lean).

## Definitions and supporting material

The six definitions in main Appendix A retain their A.1-A.6 numbering. Their construction and bridge endpoints are listed in [CURRENT_RESULT_MAP.json](CURRENT_RESULT_MAP.json) and in claim groups A01-A06 of the [full correspondence ledger](MAIN_PAPER_CORRESPONDENCE.json). Example 4.1 is represented by the elementary identifying reference-POVM construction (group D07).

The former appendices have moved into the supplement without changing the mathematical proof code. Main-result proofs are in Part I (S1-S2); supporting lemmas and constructions are in Part II (S3-S8), followed by computational and numerical notes (S9-S10). The selected former Corollary C.1 is now **Corollary S1.1**, represented by `QubitOracle.AdaptiveDesign.PureLossDistributions.phasePair`. This selected correspondence does not imply that every supplementary-only result has its own audited combined endpoint.

## Assumptions and conventions

- Fixed finite dimension; `D=d+1` and `d>0` for pure states.
- Interior mixed truth or pure truth, as appropriate.
- Positive ridge parameters and arbitrary predetermined positive finite batch sizes.
- Mixed labels use an explicit radial/tangent reindexing bridge; Lean shot indices start at zero.
- Normalized amplitude coordinates have SLD matrix `I`; Frobenius-orthonormal tangent coordinates have SLD matrix `2I`.
- The adaptive bound uses finite single-copy POVMs, parameter-independent history policies and coordinate local unbiasedness. Zero outcome probabilities use the positive-support score convention.
- The physical expected-loss results use the actual reported estimators and their proved moment bounds; they are distinct from the finite-record locally unbiased lower bound.

## Evidence and navigation

The [43-group ledger](MAIN_PAPER_CORRESPONDENCE.json) retains the 17 October semantic analysis and 211 selected endpoints, with every paper label rebound to its current main/supplement location. All 211 endpoints occur in the saved 498-declaration inventory. Its `documentation_rebound_utc` is distinct from the original `reviewed_utc`. This is a documentation rebind, not a new semantic proof audit.

The [CSV ledger](MAIN_PAPER_CORRESPONDENCE.csv) is a compact index. [Current labels](CURRENT_MAIN_LABEL_INVENTORY.json) and [label coverage](MAIN_LABEL_COVERAGE.json) use the current main article. Dated source-working-archive histories are not bundled here; the maps in this folder use current result numbering.

[Verification instructions](VERIFICATION.md) distinguish saved proof evidence, new integrity checks and a future clean rebuild.
