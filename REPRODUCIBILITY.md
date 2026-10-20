# Reproducibility

This repository separates mathematical proof checks from simulations and saved-data plotting. Each establishes a different fact. No fresh full Lean build or 10,000-replicate experiment is claimed for the 20 October repository preparation.

On 20 October 2026, the two package integrity checks and all 37 simulation unit tests passed again. The manuscript PDFs were freshly rebuilt and their reference links checked. This is distinct from the dated Lean and full simulation evidence described below.

## Integrity checks

From the repository root:

```sh
python3 -B lean/scripts/check_release.py
python3 -B simulation/scripts/check_release.py
```

These Python-only commands compare the prepared package's files with its manifests. They do not compile Lean, prove mathematical statements, or run numerical experiments. The manifests belong to this GitHub preparation, while the separately dated verification receipts remain historical evidence.

## Lean

See [LEAN_FORMALIZATION.md](LEAN_FORMALIZATION.md) for endpoint correspondence and scope. Requirements are Git, Python 3.9 or newer, [elan](https://github.com/leanprover/elan), and first-run access to the pinned dependencies.

```sh
cd lean
python3 -B scripts/verify.py --cache --replay
```

The command builds the selected 508-module main-result closure and explicit audit roots, checks the 498 selected declarations and their axioms, and replays the 17 designated modules. It does not rebuild upstream Mathlib from source or replay every dependency. Use a clean checkout for fresh project compilation; the runner requires an explicit `--incremental` flag to reuse project proof objects. New logs and receipts are generated locally under `verification/reproduction/` and ignored by Git.

## Python installation and tests

The saved experiment used Python 3.9.6, NumPy 1.26.4, and Matplotlib 3.9.4. The documented supported Python range is 3.9–3.12; use the pinned dependencies.

```sh
cd simulation
python3 -m venv .venv
source .venv/bin/activate
python -m pip install -r requirements.txt
python -m pip install --no-deps -e .
python -B scripts/check_release.py
python -B -m unittest discover -s tests -v
```

On Windows, activate `.venv\Scripts\activate` instead. The retained test suite contains 37 tests covering the actual small-record estimator objectives, complete outcome laws, schedules, fit safeguards, phase pairing, and ensemble diagnostics. Passing those tests is not a formal proof of the numerical implementation.

## Redraw the saved figures

From `simulation/` after installation:

```sh
python -B -m adaptive_tomography plot --results results/paper --output reproduced_figures
```

This uses the supplied arrays and validates their summaries before drawing. The current article's outputs are `figure1_mixed.pdf` and `figure2_pure_bures.pdf`. Historical optional covariance data are also retained, so this command additionally redraws their older figure; that figure is not in the current article or supplement.

Figure 1 uses the two mixed-qubit allocation rules. Figure 2 uses the pure-state procedure at $D=4$, with preliminary and corrected outputs from the same records. The pure reference experiment has 104 complete labels: two phase branches, thirteen bases, and four readouts. Each copy uses only one randomly selected four-outcome projective measurement.

## Smoke run

Use a new output directory:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
  python -B -m adaptive_tomography run --replications 8 --max-power 10 --output results/smoke
python -B -m adaptive_tomography plot --results results/smoke --output results/smoke/figures
```

This runs eight replicates with a 1,024-copy budget. It checks installation and execution; it is not the submitted numerical study.

## Full paper experiment

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
  python -B -m adaptive_tomography run --config configs/paper.json --output results/new_paper
python -B -m adaptive_tomography plot --results results/new_paper --output results/new_paper/figures
```

The supplied principal studies used 10,000 replicates and 16,384 copies per replicate, in 202 predetermined batches. After the first batch of sixteen, the nominal next batch size is `max(16, ceil(N/50))`, with $N$ the number already observed. Only the final batch is shortened to meet the fixed total. Reporting occurs at eighteen selected completed batches. The full experiment takes substantially longer than a smoke run.

Preserve `results/paper/`; use a new output directory. The default configuration runs only the three current main-figure studies. `configs/historical_full_run_20261017.json` retains the older five-study configuration, including optional covariance runs that are not in the current paper.

## Evidence and numerical limits

The [simulation verification guide](simulation/docs/VERIFICATION.md) and [saved package review](simulation/verification/PACKAGE_REVIEW_20261018.json) distinguish the earlier full runs from later installation, 37-test, eight-replicate smoke, and plotting checks. The new repository package preserves the implementation and arrays. Raw execution logs are kept outside this repository; two inherited metadata receipts have their machine-local paths explicitly removed.

The root seed is fixed and all replicates contribute to the summaries. Saved arrays contain scaled losses and tangent errors, not all per-copy count records. A reproducible stream rule is not a guarantee of bitwise-identical adaptive paths across numerical environments. See [the data dictionary](simulation/docs/DATA_DICTIONARY.md) and [detailed reproduction guide](simulation/docs/REPRODUCIBILITY.md) for stream roles, batch counts, reporting endpoints, and Monte Carlo uncertainty.

The dated paper snapshots inside the code folders identify the 18 October documentation edition. The PDFs at the repository root are the newer editorial revision; theorem statements, assumptions, proof arguments, numbering, Lean sources, and numerical implementation are preserved. Those older snapshot hashes are intentionally not relabeled as hashes of the current PDFs.
