# Reproducibility

## Environments and commands

Use Python 3.9-3.12 with NumPy 1.26.4 and Matplotlib 3.9.4. The archived full run used Python 3.9.6. Follow the [root README](../README.md) for installation, a saved-data plot, an eight-replicate smoke run, or the full current-paper run. Set BLAS thread counts to one for the recorded execution pattern. On headless or read-only-home systems, set `MPLCONFIGDIR` to a writable cache directory.

`configs/paper.json` runs the three studies for the two paper figures. The supplied `results/paper/` bundle also contains optional covariance data. Use a new directory when rerunning.

## Fixed experimental settings

- Mixed truth: `0.9 * (1,2,3) / sqrt(14)`. Bures allocation is uniform; Frobenius allocation is radial/transverse `s(c):1:1`.
- Pure truth: normalized amplitudes `sqrt(j+1) * exp(1j * 0.37 * j)`, for `j=0,...,3`.
- Pure reference: 13 bases, two fair phase branches and four readouts, giving 104 complete labels. Each copy uses one selected four-outcome measurement.
- Ridge coefficients: one. Pure fitted probability floor: `1/6240`. The preliminary unit vector starts at `e0`; eigenvalue tie and phase conventions are fixed in code.
- Main budget: `16384 = 2^14` copies. First batch: 16. Later nominal size: `max(16, ceil(N/50))`, with `N` the count before the batch. The final batch alone is shortened to exhaust the budget. This gives 202 predetermined batches; the final three sizes are 315, 321 and 31.
- Actual reporting counts: 256, 512, 1020, 2064, 3078, 4070, 5169, 6182, 7105, 8164, 9197, 10157, 11217, 12387, 13409, 14232, 15408, 16384. These are nearest completed batches to the targets, with earlier endpoints winning ties. Reporting does not insert acquisition updates.

The proportional batch rule is motivated by Struchalin et al. (2016), https://arxiv.org/pdf/1510.05303. The minimum, budget, reporting grid and estimator are the choices of this paper.

## Random streams and stored quantities

The root seed is `2026101602`. A stream is `SeedSequence([root_seed, experiment_id, role, replication])`. Experiments 1 and 2 are mixed allocations, experiment 3 is Algorithm 3, and 4/5 identify optional covariance runs. Role 0 is a separate diagnostic history; role 1 is a Monte Carlo replicate. The stream rule is unchanged when optional studies are disabled.

Figure 1's information panels use separate single diagnostic histories. Figure 2(a) uses every one of the 10,000 pure loss streams: each information matrix is inverted on its own record before averaging the criteria. Pointwise bands are the arithmetic mean plus or minus 1.96 Monte Carlo standard errors; they are not bands for the spread of individual records or simultaneous confidence bands across horizons. Loss curves reuse each replicate across reporting sizes, so errors across sizes are correlated. No seed selection, smoothing or monotone fitting is applied.

`samples.npz` stores already scaled `n * loss` and `sqrt(n)` tangent errors, not every individual count record. [The data dictionary](DATA_DICTIONARY.md) specifies axes and shapes. The plot command checks saved means, Monte Carlo errors, information summaries and optional covariance diagnostics before drawing.

## What can be replayed

The saved design criteria are computed record by record before averaging. Individual adaptive count histories are not stored; reproducibility is assessed using saved output arrays and controlled fresh runs.

To request the full design replay manually:

```sh
python -B -m adaptive_tomography design --results results/paper
```

This can be long and rewrites the derived design files; use a copy of the saved bundle if preserving the original checksums. Normal full `run` commands collect loss and design diagnostics jointly, without a second replay.

Floating-point or random-sampler implementation differences can change adaptive paths despite identical mathematical rules and seed metadata. The optional D=2 replay illustrates that boundary. The saved arrays are the actual record used to form the paper figures; do not claim that a different environment must reproduce every adaptive count bit for bit.

## Optional covariance comparison

The supplied optional covariance data use doubling batches and reporting counts `2^12, 2^16, 2^20, 2^24` in dimensions 2 and 4. They are additional numerical data, separate from the current paper figures.
