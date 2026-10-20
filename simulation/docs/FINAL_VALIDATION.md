> Historical report from 17 October 2026. Its paper page counts, appendix labels and optional simulation describe that snapshot. For the current manuscript and package checks, use [VERIFICATION.md](VERIFICATION.md) and [PAPER_SNAPSHOT.json](PAPER_SNAPSHOT.json).

The following report describes the preserved version 1.1 base loss run.
The version 1.2 Figure 2(a) diagnostic extension is documented in
[DESIGN_PANEL_UPDATE.md](DESIGN_PANEL_UPDATE.md). Its original evidence is
retained; the current extension has its own receipt and independent review.

# Release validation: 17 October 2026

Version 1.1.0 freshly ran all five studies from the official SSD folder, with
10,000 independent Monte Carlo replicates per study. The main figures use 202
predetermined growing batches through 16,384 copies, 18 actual completed-batch
reports, and linear horizontal axes. The supplementary comparison retains
doubling batches and its original reporting budgets.

The independent implementation review passed 30 tests. The same 30 tests passed
after a local wheel build and isolated installation, using the recorded NumPy
and Matplotlib and no dependency downloads. The final independent review checked
all saved means/Monte Carlo errors, covariance/bias/paired summaries, information
criteria, figure data, printed numbers, source hashes and experimental settings.

Both PDFs rebuilt successfully (44 main / 32 supplement pages). Seven changed
pages were inspected; the other 69 pages are pixel-identical to the previous
checked release. Figures remain beside Sections 6.1 and 6.2. The offline HTML
guide passed desktop/mobile layout and saved-result interaction checks.

The optional D=2 replay changed some sampled records despite identical seeds
and mathematical rules. A traced call had matching PCG64 states and Born
probabilities differing by 5.1e-17, yet returned different counts. Internal
sampler caches and the precise cause were not isolated. The newly saved arrays
and printed results agree.
The D=4 optional replay is bit-identical to the previous release. This is a
numerical replay boundary, not an unreported formula or schedule change.

The prior release is preserved separately. Current source/configuration and
output hashes are in the execution receipt; current paper/figure hashes are in
verification/PAPER_BINDING.json. ZIP and SSD integrity are checked separately.
Theorem/proof sources and all 621 canonical Lean sources are unchanged. No fresh
Lean computation or formal verification of Python is claimed by this update.
