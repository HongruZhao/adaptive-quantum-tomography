# Saved data dictionary

The preserved `results/paper/` arrays are unchanged. Axis names below distinguish current main-figure data from retained optional covariance data. All loss arrays are already scaled by sample size; tangent-error arrays are already scaled by its square root.

## Replicate arrays

| File/key | Shape | Type | Role |
|---|---|---|---|
| `samples.npz / mixed_bures_losses` | `(10000, 18, 2)` | `float64` | Current main figures or apparatus |
| `samples.npz / mixed_frobenius_losses` | `(10000, 18, 2)` | `float64` | Current main figures or apparatus |
| `samples.npz / pure_losses` | `(10000, 18, 2, 2)` | `float64` | Current main figures or apparatus |
| `samples.npz / pure_tangent_errors` | `(10000, 18, 2, 6)` | `float64` | Current main figures or apparatus |
| `samples.npz / optional_D2_losses` | `(10000, 4, 2, 2)` | `float64` | Optional covariance study |
| `samples.npz / optional_D2_tangent_errors` | `(10000, 4, 2, 2)` | `float64` | Optional covariance study |
| `samples.npz / optional_D4_losses` | `(10000, 4, 2, 2)` | `float64` | Optional covariance study |
| `samples.npz / optional_D4_tangent_errors` | `(10000, 4, 2, 6)` | `float64` | Optional covariance study |
| `samples.npz / horizons` | `(18,)` | `int64` | Current main figures or apparatus |
| `samples.npz / optional_horizons` | `(4,)` | `int64` | Optional covariance study |
| `samples.npz / main_batch_sizes` | `(202,)` | `int64` | Current main figures or apparatus |
| `samples.npz / main_batch_endpoints` | `(202,)` | `int64` | Current main figures or apparatus |
| `pure_design_samples.npz / criteria` | `(10000, 18, 2)` | `float64` | Current main figures or apparatus |
| `pure_design_samples.npz / horizons` | `(18,)` | `int64` | Current main figures or apparatus |
| `apparatus.npz / pure_reference` | `(104, 4, 4)` | `complex128` | Current main figures or apparatus |
| `apparatus.npz / pure_reference_bases` | `(13, 4, 4)` | `complex128` | Current main figures or apparatus |
| `apparatus.npz / pure_labels` | `(104, 3)` | `int64` | Current main figures or apparatus |
| `apparatus.npz / pure_truth` | `(4,)` | `complex128` | Current main figures or apparatus |
| `apparatus.npz / mixed_truth` | `(3,)` | `float64` | Current main figures or apparatus |
| `apparatus.npz / optional_D2_reference` | `(40, 2, 2)` | `complex128` | Optional covariance study |
| `apparatus.npz / optional_D2_truth` | `(2,)` | `complex128` | Optional covariance study |
| `apparatus.npz / optional_D4_reference` | `(312, 4, 4)` | `complex128` | Optional covariance study |
| `apparatus.npz / optional_D4_truth` | `(4,)` | `complex128` | Optional covariance study |

## Axes and evidence

- Mixed losses: `(replicate, horizon, loss)`, loss order squared Frobenius then squared Bures.
- Pure losses: `(replicate, horizon, method, loss)`, method order preliminary then corrected.
- Pure tangent errors: `(replicate, horizon, method, real tangent coordinate)` in fixed true Frobenius-orthonormal coordinates.
- Pure design criteria: `(replicate, horizon, criterion)`, current then accumulated Bures information criterion.
- `results.json`: experimental configuration, horizons, summary means/Monte Carlo errors, diagnostic information and optional covariance summaries.
- `run_receipt.json`: original execution environment, source/configuration hashes and base output hashes.
- `pure_design_summary.json` and `pure_design_receipt.json`: mean-design summaries and replay provenance.
- `verification/CURRENT_PAPER_BINDING.json`: current manuscript identity and numerical input hashes.

The files do not contain all individual adaptive batch-count histories. Array integrity, saved-summary agreement, small-record tests and mathematical theorem verification are separate checks.
