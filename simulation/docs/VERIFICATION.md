# Verification and readiness checks

## Fresh verification: 20 October 2026

The unchanged GitHub simulation implementation completed the exact current `configs/paper.json` on **20 October 2026**, in both UTC and America/Chicago. The current [main paper](../../ejs_main.pdf) has **34 pages**. This is fresh execution evidence, separate from the preserved 17-18 October records.

| Check | Result on 20 October 2026 |
|---|---|
| Existing unit tests | **37 passed, 0 failed**; [test output](../verification/20261020/TEST_OUTPUT.txt) |
| Full current paper experiment | **10,000 replicates per study**, all three current studies; **16,384 copies / 202 batches** per record; exact published configuration and seed |
| New observations | 30,000 complete Monte Carlo records, representing 491,520,000 copies, plus three separate diagnostic histories; **757.04 seconds** |
| Raw-output verification | All loss means/Monte Carlo standard errors recomputed from every fresh replicate; finite values, physical ranges and pure design criteria checked |
| Figure generation | Both current paper figures rendered from fresh samples; preserved-data figures redrawn separately |
| Independent algorithm review | Paper-to-function audit and **five new check groups**: dense objective reconstruction, adversarial/metamorphic checks, fixed-record truth-blindness, and different-seed fresh generation with archived-array loading disabled |
| Protected inputs | Execution agent: 18 source/configuration/test/build-input hashes unchanged. Independent reviewer: 689 hashes unchanged, including all 633 Lean sources, numerical sources, paper TeX and the main PDF |

The [fresh execution report](../verification/20261020/FRESH_SIMULATION.md), [full run receipt](../verification/20261020/FULL_RUN_RECEIPT.json), [output checks](../verification/20261020/EXECUTION_CHECKS.json), [source hashes](../verification/20261020/SOURCE_HASHES.json), and [command/timestamp record](../verification/20261020/COMMANDS.json) state exactly what passed. The pinned environment was Python 3.9.6, NumPy 1.26.4 and Matplotlib 3.9.4. Those dependencies were already installed; a new network download is not claimed.

After new generation completed, its arrays were compared with the publication's saved arrays at `rtol=atol=1e-10`. Both mixed loss arrays were bitwise identical. The maximum absolute differences were `6.79e-11` for pure losses, `1.32e-11` for tangent errors and `4.99e-12` for pure design criteria. All passed the stated tolerance; bitwise identity is not claimed for the pure arrays. The preserved saved arrays were not overwritten.

The [separate independent algorithm audit](../verification/20261020/INDEPENDENT_ALGORITHM_AUDIT.md), [machine-readable receipt](../verification/20261020/INDEPENDENT_ALGORITHM_AUDIT.json), and [runnable checker](../verification/20261020/independent_checks.py) assess whether the code implements Algorithms 1-3, rather than merely executing successfully. Its reduced fresh run used a different seed, four replicates and 256 main copies per replicate, and separately exercised historical optional dimensions 2 and 4. This reduced check is not the full paper experiment. The execution agent also recorded [nine instrumented histories with 1,818 new batch-count draws](../verification/20261020/INSTRUMENTED_OBSERVATIONS.json), with old-result reads blocked.

No main-algorithm mismatch, hidden truth-dependent estimator/design, replicate filtering or manufactured simulation curve was found. This is an evidence-bounded code-review conclusion, not a proof that every numerical bug is impossible. Finite simulations do not prove asymptotic theorems. The Python implementation is not mechanically verified by the [Lean proof sources](../../lean/).

## Checks for the documentation edition

[PACKAGE_REVIEW_20261018.json](../verification/PACKAGE_REVIEW_20261018.json) records the newly performed archive, source/data preservation, syntax/import, test, installation, smoke and saved-figure checks. Run `python -B scripts/check_release.py` to verify the tracked download files without sampling.

The original numerical implementation modules and tests are unchanged. The main numerical settings are unchanged; the default configuration merely disables the removed optional covariance simulations. The original five-study configuration is retained byte for byte under `configs/historical_full_run_20261017.json`.

The package has 37 existing tests covering literal small-record objectives, complete outcome probabilities, phase pairing, reference information, deterministic ties/axes, predetermined schedules, report selection and ensemble diagnostics. A smoke run verifies program execution, not the full paper experiment. Saved-data plotting checks every included mean and Monte Carlo error against its underlying arrays before drawing.

## Saved full-run evidence

The dated files under `verification/` and `results/paper/` describe the earlier full 10,000-replicate studies, diagnostic replay and independent reviews. They are preserved evidence, not a new full Monte Carlo run on 18 October. Historical Markdown reports carry a banner because their old paper page counts, appendix names and removed simulation figure are no longer the current manuscript layout.

The original saved `verification/PAPER_BINDING.json` and [PAPER_SNAPSHOT.json](PAPER_SNAPSHOT.json) bind historical manuscript snapshots. In particular, the latter preserves the 18 October **33-page main / 26-page supplement** snapshot; it does not identify the current 34-page main PDF. The new [execution checks](../verification/20261020/EXECUTION_CHECKS.json) bind that current PDF by hash. A source- or output-identity check does not imply bitwise reproducibility of adaptive random paths on every platform.

The [Lean proof sources](../../lean/) are distributed in the same repository. This Python package is not mechanically verified by those proofs. The repository is private and accessible to authorized collaborators.


## Repository preparation note: 20 October 2026

The implementation, configurations, tests, preserved saved arrays and existing MIT license are unchanged from the 18 October documentation release. The repository hosts the current main PDF; the supplement PDF is not hosted here. Historical receipts and snapshot hashes remain unchanged. New `verification/20261020/` records report actual 20 October runs and reviews; the full-size run covers the three current studies, while the removed optional covariance simulations were not rerun at full size. Full fresh output arrays remain in the local audit, with hashes and shapes recorded in the published checks. `MANIFEST.json` and `SHA256SUMS` identify the distributed files.
