# Adaptive quantum tomography: simulation code

Companion to **Adaptive quantum tomography by least squares with optimal asymptotic covariance**, by Hongru Zhao and Robert Oliver VandenBerg.

Code version **1.2.0**; documentation and fresh verification updated **20 October 2026**. The current [main paper](../ejs_main.pdf) has **34 pages**. Numerical sources, configurations, tests and preserved paper-result arrays are unchanged. The default paper configuration runs the three studies needed for its two figures; the original five-study configuration, including the removed covariance simulation, is retained separately for provenance.

## What this package provides

| Current paper output | Code and saved data |
|---|---|
| Figure 1: mixed-qubit design and loss | Algorithms 1-2, 10,000 replicates per allocation |
| Figure 2: pure-state mean design and loss | Algorithm 3 at dimension 4, 10,000 paired preliminary/corrected replicates |

The paper's two-part supplement describes proofs and supporting results. The old optional covariance **simulation figure is not in the current paper or supplement**. Its implementation, saved arrays and dated reviews remain available as historical material. The finite measurement used by the theoretical covariance example remains relevant to the proof.

## Install

Use Python **3.9-3.12**. The saved experiment used Python 3.9.6, NumPy 1.26.4 and Matplotlib 3.9.4; the two library versions are pinned in `requirements.txt`.

Run the following commands from this `simulation/` directory.

```sh
python3 -m venv .venv
source .venv/bin/activate
python -m pip install -r requirements.txt
export PYTHONPATH="$PWD/src"
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
- [Verification guide](docs/VERIFICATION.md): fresh 20 October execution, independent algorithm review, and historical evidence.
- [Historical paper snapshot](docs/PAPER_SNAPSHOT.json): the preserved 18 October manuscript hashes and labels.

At dimension 4, 104 complete labels mean **2 phase branches x 13 bases x 4 readouts**. One copy uses one randomly selected four-outcome projective measurement. Grouped multinomial batch counts implement that complete conditional experiment; the code does not measure all 104 labels on one copy.

The main budget is **16,384 = 2^14** copies in 202 predetermined batches. The seed is fixed for reproducibility, and every replicate enters the summaries. The recorded arrays do not retain all individual adaptive count records. Small-sample tests, stream replays and saved-array checks have distinct roles; none is a Lean proof of this Python implementation.

## Evidence, citation and license

On **20 October 2026**, the unchanged GitHub code passed **37 tests** and a fresh run of the exact `configs/paper.json`: **10,000 replicates for each of the three studies**, each acquiring **16,384 copies in 202 predetermined batches**. The run took **757.04 seconds** in the pinned Python 3.9.6 / NumPy 1.26.4 / Matplotlib 3.9.4 environment. All means and Monte Carlo standard errors were recalculated from the new arrays, and both current paper figures rendered successfully. See the [fresh execution report](verification/20261020/FRESH_SIMULATION.md), [full run receipt](verification/20261020/FULL_RUN_RECEIPT.json), [output checks](verification/20261020/EXECUTION_CHECKS.json), and [test output](verification/20261020/TEST_OUTPUT.txt).

A separately assigned reviewer checked the implementation against the paper's exact Algorithms 1-3 and ran **five new independent check groups**, including a different-seed, four-replicate verification run and independent dense reconstructions of the stated objectives. The [independent algorithm audit](verification/20261020/INDEPENDENT_ALGORITHM_AUDIT.md) found no hidden algorithm substitution, truth-dependent design, discarded replicate or manufactured simulation curve. Its [receipt](verification/20261020/INDEPENDENT_ALGORITHM_AUDIT.json) and [runnable checker](verification/20261020/independent_checks.py) state the exact scope and limitations. This is numerical evidence and code review; Python is not mechanically verified by the Lean proofs.

The [18 October package review](verification/PACKAGE_REVIEW_20261018.json) and dated 17 October full-run and diagnostic-replay receipts remain unchanged. They describe their original executions and are separate from the new 20 October evidence. The removed historical optional covariance studies were not rerun at full size on 20 October.

The software retains its MIT license and original software-author metadata. `CITATION.cff` also identifies the accompanying two-author paper as the preferred citation. The current private repository is [HongruZhao/adaptive-quantum-tomography](https://github.com/HongruZhao/adaptive-quantum-tomography); access is limited to authorized collaborators.


## Repository preparation note: 20 October 2026

The implementation, configurations, tests, preserved saved arrays and existing MIT license are unchanged from the 18 October documentation release. The repository hosts the current **34-page main PDF**; `docs/PAPER_SNAPSHOT.json` intentionally retains the earlier **33-page main / 26-page supplement** snapshot and its hashes. Historical receipts have not been redated. The new execution and independent-review records under `verification/20261020/` describe work actually performed on 20 October. Full fresh output arrays remain in the local audit; their hashes and shapes are published in the execution report rather than committing a second large result bundle. `MANIFEST.json` and `SHA256SUMS` identify the distributed files.
