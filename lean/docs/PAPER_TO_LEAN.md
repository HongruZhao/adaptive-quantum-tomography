# Paper-to-Lean correspondence

[MAIN_RESULTS.md](../../MAIN_RESULTS.md) gives every numbered main statement and its Lean endpoint, hypotheses and conclusions. [MAIN_PAPER_CORRESPONDENCE.json](MAIN_PAPER_CORRESPONDENCE.json) maps 43 claim groups and 211 declarations, including auxiliary geometry and estimator definitions. These declarations occur in the 498-entry main audit.

[SUPPLEMENT_RESULTS.md](../../SUPPLEMENT_RESULTS.md) and [SUPPLEMENT_CORRESPONDENCE.json](SUPPLEMENT_CORRESPONDENCE.json) map the supplementary results. The supplementary audit contains 138 entries, some also checked by the main audit. It distinguishes a proved instance used by the main algorithms from a more general printed lemma. A module's presence or successful build is not evidence that all such generalizations have been formalized.

The finite adaptive lower bound uses a fixed policy from past complete labels to a POVM. For finite randomized settings, the setting and outcome are recorded together. Thus the finite history determines the selected conditional experiment. Local unbiasedness is an actual derivative property of that finite experiment.

The pure-state interfaces keep the preliminary projection, adaptive alignment and corrected estimate separate. Gaussian and expected-loss conclusions are proved outputs of the combined endpoints; they are not fields assumed in their input structures. Coordinate changes derive information and covariance transformations from the local inverse maps.

Read [VERIFICATION.md](VERIFICATION.md) for the distinction between statement matching, source compilation, transitive axiom checks and independent kernel replay.
