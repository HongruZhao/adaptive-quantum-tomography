> Historical report from 17 October 2026. Its paper page counts, appendix labels and optional simulation describe that snapshot. For the current manuscript and package checks, use [VERIFICATION.md](VERIFICATION.md) and [PAPER_SNAPSHOT.json](PAPER_SNAPSHOT.json).

# Independent final review: Figure 2 ensemble design criteria

Date: 2026-10-17. Reviewed staging package: `submission_20261017/python_design_average`, version 1.2.0.

**Status: PASS. No unresolved mathematical, statistical, numerical, receipt, or reviewed prose discrepancy remains.** Figure 2(a) now averages the design criteria across all 10,000 original Algorithm 3 loss streams. The original numerical data, loss panel, measurement/estimation formulas and batch schedule are preserved.

## What was checked independently

I checked every entry of the `(10000,18,2)` design array, recomputed all arithmetic means and Monte Carlo standard errors from independent first/second-moment formulas, replayed eight selected original streams, reconstructed their criteria directly from the returned information matrices, re-rendered the full figures, and checked the actual plotted band vertices. Original core files and the base run receipt are byte-identical to version 1.1.0. The pure estimator, tangent correction and schedule source hashes match that original run. Runtime/data files were kept read-only by this reviewer.

The aggregation inverts each record's current or accumulated information matrix before taking its criterion average. It does not invert information pooled across replicates. The accumulator within each record still uses actual historical batch sizes. Every seed is `[2026101602,3,1,r]`, `r=0,...,9999`, with no selected seed, smoothing or monotone fit. The array itself contains 83,486 positive changes between successive reporting horizons, consistent with retaining individual-record fluctuations.

The sample-standard-deviation normalization is `ddof=1`, divided by `sqrt(10000)`. The `1.96` bands give pointwise Monte Carlo uncertainty in the means. They are not individual-record variability or simultaneous confidence bands, and errors across reporting horizons are correlated. All per-record information criteria satisfy the Gill–Massar constant three numerically; the smallest stored value is approximately `3.00000285`.

## Full replay and its evidence boundary

The completed full replay used every original pure loss stream and compared every saved loss and tangent error at all 18 reporting endpoints. The declared absolute and relative tolerances are `1e-10`. Its maximum absolute loss discrepancy is `8.9724e-11`, and maximum tangent discrepancy is `9.2068e-12`. Eight independent selected-stream checks agree with the saved design criteria within approximately `1.1e-14` and pass the same loss/error tolerances.

This is an output-checked replay of the original random streams. Original individual count records were not persisted, so a bitwise comparison of archived count records cannot be claimed. The README and reproduction notes now make this boundary explicit. The unchanged base data remain the authoritative loss record.

At 16,384 copies, the current and accumulated design means are

| Criterion | Mean | Monte Carlo standard error |
|---|---:|---:|
| Current design | 3.0012496428 | 0.00001415799 |
| Accumulated information | 3.0024237217 | 0.00002686265 |

Independent means agree exactly at the displayed precision; the maximum MCSE discrepancy from the independent raw-moment calculation is below `3.7e-13`.

## Figure and manuscript correspondence

The actual Figure 2(a) lines equal the arithmetic means, and every shaded polygon boundary equals mean plus/minus `1.96` MCSE at the actual completed-batch copy counts. Figure 2(b) retains exactly the original loss data and ordering. All six main axes remain linear over `[256,16384]`; supplementary axes remain logarithmic horizontally. Independently rendered PNGs are byte-identical to all three official PNGs. Figure 1 and supplementary PNGs are unchanged from version 1.1.0. I also inspected the new Figure 2 PNG and verified that the active manuscript Figure 2 PDF matches the package artwork.

The main text defines `C-hat` as the mean of the per-record inverse criteria. Caption, supplement and package documentation distinguish Figure 1's separately seeded single histories from Figure 2(a)'s ensemble means and describe their uncertainty correctly. The added Figure 1 paragraph follows from the almost-sure conditional and accumulated information convergence already stated in `thm:p1`, followed by continuity of inversion at the positive-definite limit. It does not assert monotonicity. No additional theorem assumption or Lean change is introduced.

## Receipt separation and installed-package portability

The base receipt binds only `results.json`, `samples.npz` and `apparatus.npz`. A separate design receipt binds those base hashes and the two design outputs. A fresh small five-study run followed by a diagnostic refresh confirms that the base files and receipt remain byte-identical and all hashes remain valid.

The completed full replay's executed `design.py` and receipt are archived. The subsequent portable version differs only in module-file lookup for hashing; its aggregation functions and numerical replay loop have identical syntax trees. No criterion, summary or base file changed. `PORTABILITY_REBINDING.json` separately binds the final portable modules, preserving every original replay receipt field and its executed-source scope.

Source hashing now uses the actual installed module directory with logical `src/adaptive_tomography/...` keys. Fresh simulations also bind a canonical digest of the effective configuration. Seven focused independent tests pass in an isolated installed-package layout without `src/` or `configs/` siblings, including nonempty source capture, the effective-config digest, and receipt validity after replay. The parent-owned wheel build/install/run/replay/plot check is recorded separately in `INSTALLATION_CHECK.json`.

## Evidence

`INDEPENDENT_FINAL_REVIEW.json` binds this review to the relevant data, executed/current source, final manuscript and artwork hashes. Detailed independent evidence is in `INDEPENDENT_ENSEMBLE_CHECK.json`, `INDEPENDENT_INSTALLED_LAYOUT_TESTS.json`, `INDEPENDENT_PORTABILITY_RESOLUTION.json`, the focused tests and render log. PDF layout and archive/SSD delivery checks remain separate parent-owned evidence. This review does not prove asymptotic results from finite Monte Carlo data or claim formal verification of Python.
