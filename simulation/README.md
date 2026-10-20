# Adaptive quantum tomography: simulation code

Companion to **Adaptive quantum tomography by least squares with optimal asymptotic covariance**, by Hongru Zhao and Robert Oliver VandenBerg.

Code version **1.2.0**; documentation prepared **18 October 2026** for the current 33-page main article and 26-page supplement. The implementation and saved numerical arrays are unchanged. The default paper configuration now runs only the three studies needed for the paper's two figures; the original full configuration, including the removed covariance simulation, is retained separately for provenance.

## What this package provides

| Current paper output | Code and saved data |
|---|---|
| Figure 1: mixed-qubit design and loss | Algorithms 1-2, 10,000 replicates per allocation |
| Figure 2: pure-state mean design and loss | Algorithm 3 at dimension 4, 10,000 paired preliminary/corrected replicates |

The paper's two-part supplement describes proofs and supporting results. The old optional covariance **simulation figure is not in the current paper or supplement**. Its implementation, saved arrays and dated reviews remain available as historical material. The finite measurement used by the theoretical covariance example remains relevant to the proof.

## Install

Use Python **3.9-3.12**. The saved experiment used Python 3.9.6, NumPy 1.26.4 and Matplotlib 3.9.4; the two library versions are pinned in `requirements.txt`.

```sh
python3 -m venv .venv
source .venv/bin/activate
python -m pip install -r requirements.txt
python -m pip install --no-deps -e .
python -B scripts/check_release.py
python -B -m unittest discover -s tests -v
```

Windows activation is `.venv\Scripts\activate`. Dependency installation needs network access unless the pinned wheels are already available. See [Reproducibility](docs/REPRODUCIBILITY.md) for environment and batch details.

## Choose a reproduction task

**Redraw the saved figures without sampling:**

```sh
python -B -m adaptive_tomography plot --results results/paper --output reproduced_figures
```

The paper outputs are `figure1_mixed.pdf` and `figure2_pure_bures.pdf`, with PNG copies. Because the preserved saved bundle also contains historical covariance data, this command additionally redraws its historical covariance figure; that extra figure is not part of the current submission.

**Check an installation with eight replicates:**

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
  python -B -m adaptive_tomography run --replications 8 --max-power 10 --output results/smoke
python -B -m adaptive_tomography plot --results results/smoke --output results/smoke/figures
```

The smoke configuration uses the new paper default, with no optional covariance studies. Its small experiment is not the submitted 10,000-replicate result.

**Run the full current paper experiment:**

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
  python -B -m adaptive_tomography run --config configs/paper.json --output results/new_paper
python -B -m adaptive_tomography plot --results results/new_paper --output results/new_paper/figures
```

Use a new output directory to preserve `results/paper/`. The full experiment is substantially longer than the smoke run. To reproduce the original five-study historical configuration, explicitly use `configs/historical_full_run_20261017.json` and a separate output directory.

## Read the implementation

- [Code guide](docs/CODE_GUIDE.md): files, estimator flow and reading order.
- [Algorithm correspondence](docs/ALGORITHM_CORRESPONDENCE.md): paper formulas and functions.
- [Reproducibility](docs/REPRODUCIBILITY.md): exact settings, streams, batching and replay limits.
- [Data dictionary](docs/DATA_DICTIONARY.md): array shapes, axes and saved evidence.
- [Verification guide](docs/VERIFICATION.md): saved full-run evidence versus new package checks.
- [Paper snapshot](docs/PAPER_SNAPSHOT.json): manuscript hashes and current labels.

At dimension 4, 104 complete labels mean **2 phase branches x 13 bases x 4 readouts**. One copy uses one randomly selected four-outcome projective measurement. Grouped multinomial batch counts implement that complete conditional experiment; the code does not measure all 104 labels on one copy.

The main budget is **16,384 = 2^14** copies in 202 predetermined batches. The seed is fixed for reproducibility, and every replicate enters the summaries. The recorded arrays do not retain all individual adaptive count records. Small-sample tests, stream replays and saved-array checks have distinct roles; none is a Lean proof of this Python implementation.

## Evidence, citation and license

The [package review](verification/PACKAGE_REVIEW_20261018.json) states which tests, smoke runs and saved-data plotting checks were newly run. The dated 17 October full-run and diagnostic-replay receipts are preserved. A full 10,000-replicate Monte Carlo rerun is not claimed for this documentation edition.

The software retains its MIT license and original software-author metadata. `CITATION.cff` also identifies the accompanying two-author paper as the preferred citation. The GitHub URL will be added when supplied; no remote publication was performed.


## Repository preparation note: 20 October 2026

The implementation, configurations, tests, saved arrays, and existing MIT license are unchanged from the documentation release. The repository root PDFs are the newer editorial revision; the dated `docs/PAPER_SNAPSHOT.json` intentionally retains the earlier paper hashes. Raw execution logs are omitted, and two inherited JSON metadata exports explicitly remove machine-local paths. The new `MANIFEST.json` and `SHA256SUMS` identify this prepared folder. None of these packaging changes is a new Monte Carlo run or Lean verification.
