# Proof source guide

Start with `MainPaper.lean` and `Supplement.lean`, then read the named result interfaces:

| Interface | Role |
|---|---|
| `MainPaperTheorem31.lean` | Mixed-qubit procedures, consistency, information and Gaussian limits |
| `QubitOracle/Paper/MainPaperTheorem42.lean` | Pure-state preliminary fit, alignment and corrected estimator |
| `QubitOracle/Paper/MainPaperPureCharts.lean` | Smooth coordinates and inverse-information covariance |
| `QubitOracle/Paper/MainPaperMeanLosses.lean` | Expected physical losses |
| `QubitOracle/AdaptiveDesign/AdaptiveSingleCopyOracleCharts.lean` | Finite adaptive lower bound for mixed and pure models |
| `QubitOracle/AdaptiveDesign/PhasePairPOVM.lean` | Phase pairing, identification and Fisher symmetry |
| `QubitOracle/AdaptiveDesign/SupplementProbability.lean` | Bounded martingale tail and real-moment consequences |
| `QubitOracle/AdaptiveDesign/SupplementMoments.lean` | All-real mixed-estimator moment consequences |

`QubitOracle/AdaptiveDesign/` contains probability, regression, geometry and tangent-correction proofs. `QubitOracle/Paper/` connects concrete measurement laws to the result interfaces. Root audit files are metaprograms for reporting and rejecting unsupported axiom dependencies; they are not mathematical assumptions.

The default build includes every distributed module. The [main ledger](MAIN_PAPER_CORRESPONDENCE.json) and [supplementary ledger](SUPPLEMENT_CORRESPONDENCE.json) are the authoritative guides to statement coverage. File names and identifiers do not by themselves establish a match to a numbered result.
