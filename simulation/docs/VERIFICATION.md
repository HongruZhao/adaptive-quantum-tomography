# Verification and readiness checks

## Checks for the documentation edition

[PACKAGE_REVIEW_20261018.json](../verification/PACKAGE_REVIEW_20261018.json) records the newly performed archive, source/data preservation, syntax/import, test, installation, smoke and saved-figure checks. Run `python -B scripts/check_release.py` to verify the tracked download files without sampling.

The original numerical implementation modules and tests are unchanged. The main numerical settings are unchanged; the default configuration merely disables the removed optional covariance simulations. The original five-study configuration is retained byte for byte under `configs/historical_full_run_20261017.json`.

The package has 37 existing tests covering literal small-record objectives, complete outcome probabilities, phase pairing, reference information, deterministic ties/axes, predetermined schedules, report selection and ensemble diagnostics. A smoke run verifies program execution, not the full paper experiment. Saved-data plotting checks every included mean and Monte Carlo error against its underlying arrays before drawing.

## Saved full-run evidence

The dated files under `verification/` and `results/paper/` describe the earlier full 10,000-replicate studies, diagnostic replay and independent reviews. They are preserved evidence, not a new full Monte Carlo run on 18 October. Historical Markdown reports carry a banner because their old paper page counts, appendix names and removed simulation figure are no longer the current manuscript layout.

The original saved `verification/PAPER_BINDING.json` binds its historical paper snapshot. The current paper and supplement are identified separately by [PAPER_SNAPSHOT.json](PAPER_SNAPSHOT.json). A source- or output-identity check does not imply bitwise reproducibility of adaptive random paths on every platform.

Lean mathematics is distributed separately. This Python package is not mechanically verified by the Lean proof archive. The GitHub URL remains author-supplied; all preparation here is local.


## Repository preparation note: 20 October 2026

The implementation, configurations, tests, saved arrays, and existing MIT license are unchanged from the documentation release. The repository root PDFs are the newer editorial revision; the dated `docs/PAPER_SNAPSHOT.json` intentionally retains the earlier paper hashes. Raw execution logs are omitted, and two inherited JSON metadata exports explicitly remove machine-local paths. The new `MANIFEST.json` and `SHA256SUMS` identify this prepared folder. None of these packaging changes is a new Monte Carlo run or Lean verification.
