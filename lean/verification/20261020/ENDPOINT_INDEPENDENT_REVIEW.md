# Independent main-result correspondence review — 20 October 2026

Review completed: 2026-10-20T07:14:43.713584+00:00 (UTC); 2026-10-20T02:14:43.713584-05:00 (America/Chicago).

**Verdict: all nine printed main results match the stated Lean endpoint scope, with the explicit representation conventions below.** Seven principal correspondence groups contain seventeen mapped declarations. This was a read-only review of the actual current LaTeX statements, Lean source declarations and constructors, and `MAIN_RESULTS.md`; it is not a fresh build or kernel replay. The separate October 20 build was still running at review completion.

## Clause and hypothesis review

### Proposition 2.1 — T01

All four conjunction components cover arbitrary SLD pairing independence, complex trace identity (hence its real form), 4-norm-squared horizontal identity, and finite-family coordinate entry/contraction formulas. Any chart tangent basis is a permitted finite family.

Unit PureVector; Hermitian tangent arguments; actual directional SLD equations. No information identity supplied as hypothesis.

### Theorem 3.1 — T02

First almost-sure conjunction proves raw and physical consistency, conditional Fisher convergence and both conditional/realized information averages; last almost-sure clause proves eventual safeguard equality. action_in_batch and label_order establish held-batch and axis-order conventions.

Positive ridge, arbitrary predetermined positive integer batches, either specified loss, fixed interior truth. Gaussian and consistency limits are conclusions.

### Theorem 3.2 — T02

Second and third conjunctions of the same theorem_3_1 prove both Gaussian limits with inverse-information covariance. covariance_eq_information_inv identifies explicit loss-specific matrices. Full-copy limits imply all completed-batch subsequences.

Exactly the mixed-model assumptions of Theorem 3.1. Zero truth and singleton batches are permitted. No independent theorem_3_2 export is claimed.

### Proposition 4.1 — T03

paired_conditions proves identifying, regular and FisherSymmetric for the actual paired effects; paired_fisher_of_rankOne separately supplies the Fisher component. Normalized reference amplitude metric and information bridges give intrinsic half-QFI form.

Finite POVM; ambient Identifying, reference Regular, and RankOne. Strict reference positivity excludes a zero rank-one factor. Fisher symmetry is not an input.

### Theorem 4.2 — T04

Six Conclusions fields prove the three completed-batch consistency limits, all-copy aligned-ray and conditional information limits, and completed-batch average information. Inputs constructs actual estimators/protocol and adds no convergence assumptions.

Inputs has d>0, reference POVM with C1/C2/rank-one, positive lambda/eta and prescribed positive integer batches; truth is unit. D=d+1.

### Theorem 4.3 — T04

The same theorem_4_2 produces TightNorm root-rate fields, chart CLT/covariance/SLD fields, and ambient Gaussian, centering, support and Frobenius covariance fields. Rates are proved for all positive sample sizes, stronger than the printed completed-batch restriction; CLTs explicitly use batch horizons.

Same Inputs and truth as Theorem 4.2. SmoothCoordinates is a smooth local homeomorphism with smooth inverse; derivative invertibility is proved. No independent theorem_4_3 export is claimed.

### Theorem 5.1 — T05

Combined QuantumModel theorem and mixed/pure alternatives prove oracleConstant <= n * quadraticRisk for actual adaptive Born products. The matrix-square-root oracleConstant equals printed C_GM. Information, score and Gill-Massar inequalities are derived, not scientific assumptions.

Finite Y, fixed parameter-independent history policy, PSD W, n>=1 and actual finite-model LocallyUnbiased. PureChartData supplies locally physical chart and invertible derivative; not an information bound. No rank-one/positive-probability restriction on measurement.

### Corollary 5.2 — T06

Both actual physical expected-loss limits are present in corollary_5_2. mixedOutput uses the designated safeguard/projection; qubit_bures_comm bridges estimate-first Bures order. Frobenius Bloch formula is the density-matrix loss.

Positive ridge, prescribed positive batches, interior truth only; moment/uniform-integrability bounds are proved elsewhere, not added premises. Physical output need not be locally unbiased.

### Corollary 5.3 — T07

corollary_5_3 contains actual corrected-projector physical Bures and squared Hermitian Frobenius limits at batch horizons with constants d and 2d. pure_bures_comm bridges Bures argument order.

Exactly same pure Inputs/truth; no moment or unbiasedness premise added.

## Exact endpoint inventory

- `QubitOracle.Paper.PureQuantumInformation.proposition_2_1` (T01).
- `QubitOracle.Paper.MainPaperTheorem31.theorem_3_1` (T02).
- `QubitOracle.Paper.MainPaperTheorem31.action_in_batch` (T02).
- `QubitOracle.Paper.MainPaperTheorem31.label_order` (T02).
- `QubitOracle.AdaptiveDesign.P1Weighted.covariance_eq_information_inv` (T02).
- `QubitOracle.AdaptiveDesign.PhasePair.paired_conditions` (T03).
- `QubitOracle.AdaptiveDesign.PhasePair.paired_fisher_of_rankOne` (T03).
- `QubitOracle.Paper.MainPaperTheorem42.Inputs` (T04).
- `QubitOracle.Paper.MainPaperTheorem42.Conclusions` (T04).
- `QubitOracle.Paper.MainPaperTheorem42.theorem_4_2` (T04).
- `QubitOracle.AdaptiveDesign.AdaptiveSingleCopyOracle.theorem_5_1` (T05).
- `QubitOracle.AdaptiveDesign.AdaptiveSingleCopyOracle.theorem_5_1_mixed` (T05).
- `QubitOracle.AdaptiveDesign.AdaptiveSingleCopyOracle.theorem_5_1_pure` (T05).
- `QubitOracle.Paper.MainPaperMeanLosses.corollary_5_2` (T06).
- `QubitOracle.Paper.MainPaperMeanLosses.qubit_bures_comm` (T06).
- `QubitOracle.Paper.MainPaperMeanLosses.corollary_5_3` (T07).
- `QubitOracle.Paper.MainPaperMeanLosses.pure_bures_comm` (T07).

## Evidence and semantic boundaries

- Mixed copy indices are zero based in Lean; internal axes transverse/transverse/radial vs paper radial/transverse/transverse. Explicit bridge endpoints are mapped.
- A single theorem_3_1 proves current Theorems 3.1 and 3.2; a single theorem_4_2 proves current Theorems 4.2 and 4.3. These are not four separately named endpoint declarations.
- Theorem 5.1 uses finite fixed Y. Appendix B explicitly permits zero-probability padding at any fixed horizon, giving the same finite decision-tree experiment. This representation correspondence is manual, not a new formally checked LaTex-to-Lean translation.
- Lean history lists put the newest observation first and encode time by list length. The paper uses chronological records. A fixed reversal translates the arbitrary policy; both representations retain the complete record.
- Lean proves finite conditional product models and score-energy consequences directly; it has no separate sigma-field object matching the papers filtration notation.
- For arbitrary charts, a smooth local change from normalized true-state coordinates represents the chart; extension outside its open domain does not alter local limits.
- Physical Bures means are genuine matrix-square-root losses, not quadratic approximations; density/Hermitian norm and Bloch-coordinate conventions are explicit.

All seventeen mapped declarations are present in the inherited 498-type inventory. Their inherited transitive axiom sets contain only `propext`, `Classical.choice` and `Quot.sound`; this review does not replace the separately requested October 20 recomputation. Twelve documented legacy scientific axiom leaves occur elsewhere in the retained tree and must not be described as absent from all 633 source files. Lean compilation verifies Lean terms; matching those terms to printed statements remains an independently reviewed semantic correspondence, not a mechanized LaTeX parser.

No missing printed hypothesis or conclusion was found in this review. No additional stochastic convergence, Gaussian-limit, moment-bound, information-bound, or score-identity assumption was found in the exported principal endpoint interfaces. The quantum hardware, Python implementation, Monte Carlo values and historical-priority claims are outside this endpoint review.

## Statement preservation

All nine exact `### Paper statement` blocks match Git HEAD `8893cf286113ef1acbe91e4e6d2252b7c40c1ccc`. Their complete baseline text and SHA-256 hashes are recorded in `PAPER_STATEMENT_BLOCKS_BASELINE.json`. Parent verification-report edits should be tested against these hashes after completion. The current paper theorem source fragments and hashes are saved separately in `PAPER_THEOREM_SOURCE_EXTRACTS.json`.

## Historical metadata caution

The inherited 17 October `VERIFICATION_SUMMARY.json` says `main_named_results: 8`, while the current paper, current ledger and current Markdown display nine. Preserve the historical receipt unchanged and report the current nine-result count in the new October 20 evidence. This is a metadata-history discrepancy, not a missing theorem endpoint.

No paper, Lean, production simulation, or repository documentation source was edited by this reviewer.
