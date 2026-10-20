> Historical report from 17 October 2026. Its paper page counts, appendix labels and optional simulation describe that snapshot. For the current manuscript and package checks, use [VERIFICATION.md](VERIFICATION.md) and [PAPER_SNAPSHOT.json](PAPER_SNAPSHOT.json).

The following report describes the preserved version 1.1 base loss run.
The version 1.2 Figure 2(a) diagnostic extension is documented in
[DESIGN_PANEL_UPDATE.md](DESIGN_PANEL_UPDATE.md). Its original evidence is
retained; the current extension has its own receipt and independent review.

# Independent review: predetermined growing batches and linear main figures

Date: 2026-10-17. Reviewer: independent Python/paper correspondence agent.

**Result: PASS for the reviewed runtime and configuration; no blocking algorithm discrepancy found.** This review permits the full run to begin. It does not certify results that have not yet been generated or the manuscript revisions that will describe them. The earlier 2026-10-16 review and delivery are preserved.

## Reviewed change and mathematical scope

The reviewed package is `submission_20261017/python`, version 1.1.0. The mathematical baseline is the active `source/paper/ejs` manuscript, particularly the predetermined-batch definition in `model.tex`, Algorithms 1–2 in `mixed.tex`, and Algorithm 3 in `persistent.tex`. Those algorithms permit arbitrary predetermined positive finite batches and completed-batch reporting. The new sequence therefore fits the existing assumptions. The final clipped positive batch is a fixed experimental budget choice; it is not a data-dependent stopping time. A finite experiment does not itself demonstrate an asymptotic theorem.

I reviewed the new `schedules.py` and the diffs in `estimators.py`, `mixed.py`, `pure.py`, `simulation.py`, `plotting.py`, and `__main__.py`. The only estimator-loop change is to iterate over the already computed schedule. The mixed ridge objective, safeguards, exact e3-based completion, and allocation probabilities are unchanged. The pure complete POVM, categorical ridge objective, fixed probability floor, preliminary alignment, all-record tangent correction, and normalization retraction are unchanged. The general horizon validator now admits increasing non-power-of-two integers; a separate schedule validator rejects unreachable reports.

## Independently verified acquisition and reporting

The main recurrence is

`m1=16; m_j=max(16,ceil(N_(j-1)/50))`, with only the last batch clipped to the fixed 16,384-copy budget.

An independent literal recurrence matches all 202 runtime batch sizes. Before the final batch, the cumulative count is 16,353; the nominal next size is 328, and the final actual size is 31. Every batch is positive. No reporting target enters the batch generator. The sequence remains constant across different sampled outcomes.

Targets are 256, 512, then 1024, 2048, ..., 16,384. Choosing the nearest completed batch, with earlier endpoints winning ties, gives exactly:

`256, 512, 1020, 2064, 3078, 4070, 5169, 6182, 7105, 8164, 9197, 10157, 11217, 12387, 13409, 14232, 15408, 16384`.

The nominal target 1024 is unreachable under this sequence and is correctly rejected if requested as an actual report. Reports do not split batches or introduce measurement updates. All 202 batches enter independently reconstructed mixed ridge normal equations. For the pure trajectory, all 202 complete count records enter both the independent categorical ridge reconstruction and the literal all-record tangent update; the independently reconstructed projector agrees numerically with the production output.

Sparse versus dense reporting produced the same sampled complete records in the tested trajectories. Pure Born probabilities can differ at machine precision between separately allocated numerical executions (observed maximum discrepancy below `1e-16`); the test accordingly requires numerical agreement, not a cross-execution bitwise guarantee. This is the numerical replay boundary already identified in the previous release, not a change to the mathematical adaptive rule.

The supplementary covariance comparison still uses the original doubling sequence `16,16,32,...,2^23` and reports at `2^12,2^16,2^20,2^24`. Its 21 batches exhaust `2^24` copies. The main schedule is never injected into those optional trajectories.

## Independent tests and actual rendering

The 18 existing paper-algorithm tests and 12 additional schedule/all-record tests pass. Their exact run is recorded in `INDEPENDENT_TESTS.log`. The new tests are in `test_growing_batches.py` in this audit directory for inclusion in the official package. They cover independent recurrence, final clipping, nearest endpoints and tie rules, unreachable reports, optional doubling preservation, complete-record mixed and pure normal equations, tangent correction copy counts, reporting invariance, and outcome-independent batch sizes. The earlier tests continue to cover independent per-observation objectives, complete phase/basis probabilities, fixed floors, reference Fisher information, safeguards, axis edge cases, eigenvalue ties, and loss normalization.

I also ran a genuine four-replicate smoke experiment, using the full 16,384-copy main budget and a reduced optional horizon of `2^12`. This is explicitly not the official 10,000-replicate experiment. All five studies completed and the actual plotter produced PDFs and PNGs. I inspected both main PNGs and captured their Matplotlib axes before closing them:

- Figure 1 has four panels; Figure 2 has two squared-Bures panels.
- All six main horizontal axes are genuinely linear over `[256,16384]`.
- Every primary data series uses the 18 actual completed-batch endpoints.
- Tick labels are 256, 4,096, 8,192, 12,288, 16,384; these are physical copy counts, not categorical positions.
- Both optional axes remain logarithmic, with their own completed doubling horizons.
- Plotting recomputed stored means, Monte Carlo standard errors, covariance, bias, losses, and paired summaries and performed no additional sampling.

The smoke evidence is in `INDEPENDENT_SMOKE_RECEIPT.json`, `independent_smoke.log`, and `independent_smoke/`. It includes exact result/figure hashes. Runtime and configuration hashes at review time are in `INDEPENDENT_CODE_REVIEW_HASHES.json`; the official full run must additionally capture its own immutable start/end hashes and receipts.

## Literature attribution and interpretation

The primary precedent for `ceil(N/50)` is [Struchalin et al., *Experimental adaptive quantum tomography of two-qubit states* (2016), Section II](https://arxiv.org/pdf/1510.05303). The article uses growing measurement blocks of that size. Our initial/minimum size 16, fixed 16,384-copy budget, final clipping, and reporting grid are additional choices. The precedent does not identify their estimator or measurement class with Algorithms 1–3 here. Kravtsov et al. (2013) instead discuss a 1% block rule; the 2% rule should not be attributed to that paper or to Qi et al.

The main diagnostic matrices still evaluate complete conditional Fisher information at the truth and accumulate it with actual batch sizes. Truth enters sampling and diagnostics, not measurement selection or fitting. The fixed seed and experiment/role/replicate separation are unchanged. Primary risks continue to be averages of exact physical losses, and their error bars remain pointwise Monte Carlo errors with divisor `R-1` in the sample variance. The Gill–Massar line bounds the information criterion and is the asymptotic risk benchmark; it is not a universal finite-sample lower bound for biased physical outputs.

## Remaining review boundary

Before final delivery, independently check the full `R=10000` outputs and final `numerics.tex`/supplement descriptions against this configuration, including every reported number and the distinction between the new main schedule and the retained supplementary schedule. Final manuscript/PDF review remains the parent agent's responsibility. No Lean rebuild or new formal-verification claim is made in this Python review. Runtime source and manuscript files were not edited by this reviewer.
