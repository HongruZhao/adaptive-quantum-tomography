# Supplementary statement correspondence: 20 October 2026

**PASS for the three targeted scope alignments and affected proof applications.** The Lean code and build inputs are unchanged. The main scientific source files, all nine main statement blocks, algorithms and all 149 numbered labels are unchanged. The main PDF has identical page pixels. Supplement revisions are pink on pages 5, 12, 15–16 and 18–19; the supplement remains 26 pages.

| Result | Current printed scope | Existing Lean proof |
|---|---|---|
| Lemma S4.1 | Fixed deterministic nearest-projector selection, including ties; same constant 20 | `PureMatrixController.nearestProjector_expansion` with the unchanged tangent/retraction bounds |
| Lemma S4.2 | Almost-sure consistency and the stated projector Gaussian limit | `amplitude_clt_of_projector_clt`, `smoothChart_clt_of_amplitude_clt`, and the covariance-coordinate identity |
| Lemma S6.2 | Actual adaptive ridge preliminary fit, alignment, floor, batches and tangent solve, for the stipulated identifying, positive-reference and Fisher-symmetric apparatus | `actualCancellationError_secondOrder`, `actual_fittedInformation_tendsto`, and `actualLinearError_rootRate` |

The separate inverse-operator limit is no longer asserted. The proof uses normalized normal-operator convergence and the normal equation directly. The O_p(n^-1) cancellation statement and all equation numbers are retained. Theorem 4.3's supplementary proof and the covariance-example comparison use the direct score expansion. Both the paired reference and Proposition S8.1's Fisher-symmetric reference remain within S6.2. The consistency and root-n preliminary-rate arguments precede the cancellation invocation, so no circular assumption is introduced.

Every use of the three lemma labels was inspected. The projection/retraction uses in the cancellation and moment arguments retain their original geometric clauses. The chart application has already established almost-sure consistency. No unsupported inverse-limit reference remains in the active supplement. Current numbered references resolve without errors; labels and result types were checked against the saved auxiliary files.

Seven existing declaration types and their transitive axioms were checked by Lean for this scope review, using the verified unchanged project objects. See [the targeted receipt](SUPPLEMENT_SCOPE_ENDPOINT_AUDIT.json), [printed types and axiom output](SUPPLEMENT_SCOPE_ENDPOINTS.txt), and [the detailed correspondence receipt](SUPPLEMENT_SCOPE_ALIGNMENT.json). This is an executed targeted audit, not a new 271-module source rebuild. The official fresh source-build evidence elsewhere in this directory remains valid for the identical code.

The correspondence review is performed at source level; Lean does not mechanically read the LaTeX. Several component proofs support some printed lemmas, so this report does not claim a single combined endpoint for every supplementary statement or complete mechanical verification of all prose. Python is separately tested and audited. The corresponding Lean-only source archive is available on [Zenodo](https://doi.org/10.5281/zenodo.23523803).
