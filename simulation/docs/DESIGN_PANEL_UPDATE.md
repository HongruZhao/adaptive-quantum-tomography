> Historical report from 17 October 2026. Its paper page counts, appendix labels and optional simulation describe that snapshot. For the current manuscript and package checks, use [VERIFICATION.md](VERIFICATION.md) and [PAPER_SNAPSHOT.json](PAPER_SNAPSHOT.json).

# Figure 2 design panel update: version 1.2

The earlier panel showed one separate adaptive record. This release uses
every original Algorithm 3 loss stream, with no change to the root seed,
truth, reference measurement, batch schedule, estimators or copy budget.
The criterion is evaluated after matrix inversion on each record and then
averaged across 10,000 replicates. The shaded bands are pointwise 1.96 Monte
Carlo standard errors of these means. No records are excluded and no
smoothing or monotone fit is applied. Figure 1(a,c) remains single-record.

At n=16,384, the current-design mean is 3.00124964 (MC s.e. 0.00001416); the accumulated-information mean is 3.00242372 (MC s.e. 0.00002686). The bound is 3.

All original loss arrays, apparatus, summary data and the base run receipt
are byte-identical to version 1.1. The new design command replays all
original pure streams and checks every stored loss and tangent error.
The maximum observed deviations and 1e-10 absolute/relative comparison
tolerances are recorded in results/paper/pure_design_receipt.json. Original
individual count records were not retained.

After the completed replay, only module-path lookup for receipt hashes
was made portable to installed wheels. The executed replay source and
receipt are archived in verification; PORTABILITY_REBINDING.json confirms
the diagnostic arrays and summaries are byte-identical. The final wheel
passes all 37 tests and a small run/replay/plot with valid source hashes
and an effective-configuration digest.

All 37 tests pass, including seven independent ensemble tests. A fresh
small end-to-end run checks same-call collection and plotting. The full
array and figure review is in verification/DESIGN_ENSEMBLE_REVIEW.json.
Earlier review receipts retain their version 1.1 scope. No Lean changes,
Lean computation, remote publication or hardware validation is claimed.
