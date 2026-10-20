# Reading the Lean sources

Start with [MainPaper.lean](../MainPaper.lean), then use the [current result map](PAPER_TO_LEAN.md). The full folder retains all 633 canonical Lean sources. The selected current-result dependency closure has 508 modules; reading every retained source is unnecessary to locate the principal statements.

| Topic | Entry file | What to look for |
|---|---|---|
| Mixed Algorithms 1-2 and current Theorems 3.1-3.2 | [MainPaperTheorem31.lean](../MainPaperTheorem31.lean) | Exact axis and batch bridges; the combined `theorem_3_1` conclusion |
| Pure Algorithm 3 and current Theorems 4.2-4.3 | [MainPaperTheorem42.lean](../QubitOracle/Paper/MainPaperTheorem42.lean) | `Inputs`, actual process/estimators, `Conclusions`, then the proving theorem |
| Smooth coordinate and ambient limits | [MainPaperPureLimits.lean](../QubitOracle/Paper/MainPaperPureLimits.lean) | Transfer of the actual corrected-estimator limit |
| Expected physical losses | [MainPaperMeanLosses.lean](../QubitOracle/Paper/MainPaperMeanLosses.lean) | `corollary_5_2` and `corollary_5_3` |
| Adaptive lower bound | [AdaptiveSingleCopyOracle.lean](../QubitOracle/AdaptiveDesign/AdaptiveSingleCopyOracle.lean) | Model assumptions, finite histories and weighted bound |
| Geometry definitions | [MainPaperGeometry.lean](../QubitOracle/Paper/MainPaperGeometry.lean) | Fubini-Study pairing, tangent and retraction bridges |
| Audit surface | [MainPaperAudit.lean](../MainPaperAudit.lean) | Exact selected elaborated declarations and transitive-axiom checks |

An `Inputs` structure lists hypotheses. A `Conclusions` structure lists propositions. The theorem constructing `Conclusions` is the proof; the existence of an input or conclusion structure alone is not proof evidence. The preserved identifiers follow the earlier combined theorem numbering, so use the current map rather than inferring paper numbers from filenames.

Definitions of preliminary estimates, reported estimates, conditional information and physical losses are distinct. In particular, the preliminary pure estimator is not assigned the corrected estimator's asymptotic covariance. The exact positive finite batch and coordinate conventions are recorded in the correspondence ledger.

The source distribution contains some historical declarations retained because their modules are imported. The selected endpoint audit, rather than a search for the word `axiom`, determines whether those declarations occur in the audited proof dependencies. See [VERIFICATION.md](VERIFICATION.md).
