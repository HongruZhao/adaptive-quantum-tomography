# Reproducibility

The [main paper](ejs_main.pdf), Lean proofs and Python experiments are available to authorized collaborators in this private repository. Proof checking, numerical tests, fresh sampling and saved-data plotting establish different facts.

## Lean

Install Git, Python 3.9 or newer, and [elan](https://github.com/leanprover/elan):

```sh
cd lean
python3 -B scripts/check_release.py
LAKE_ARTIFACT_CACHE=false python3 -B scripts/verify.py --cache --replay
```

The integrity check does not build proofs. The verifier builds all distributed project modules, checks the two declaration inventories and all retained mathematical axiom dependencies, and replays the listed modules. It rejects existing project objects unless `--incremental` is specified. Pinned upstream library caches are separate from project proof objects. First-run dependency acquisition needs network access.

For development, `lake build` and `lake env lean SupplementAudit.lean` run both main and supplementary audits. The exact current proof scope and component correspondence are in [LEAN_FORMALIZATION.md](LEAN_FORMALIZATION.md) and [SUPPLEMENT_RESULTS.md](SUPPLEMENT_RESULTS.md). The [official report](lean/verification/20261020/README.md) records the actual execution, rather than treating archive integrity as proof verification.

## Python

Use Python **3.9–3.12**; the tested environment is **Python 3.9.6 / NumPy 1.26.4 / Matplotlib 3.9.4**.

```sh
cd simulation
python3 -m venv .venv
source .venv/bin/activate
python -m pip install -r requirements.txt
export PYTHONPATH="$PWD/src"
python -B scripts/check_release.py
python -B -m unittest discover -s tests -v
```

On Windows activate `.venv\Scripts\activate`; in PowerShell use `$env:PYTHONPATH="$PWD/src"`. A headless system can set `MPLBACKEND=Agg` and `MPLCONFIGDIR` to a writable cache directory.

For a small fresh run:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
  python -B -m adaptive_tomography run --replications 8 --max-power 10 --output results/smoke
python -B -m adaptive_tomography plot --results results/smoke --output results/smoke/figures
```

For all current paper experiments:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
  python -B -m adaptive_tomography run --config configs/paper.json --output results/new_paper
python -B -m adaptive_tomography plot --results results/new_paper --output results/new_paper/figures
```

Use a new output directory. The full configuration runs **10,000 replicates for each of three studies**, with **16,384 copies in 202 batches** per replicate. To redraw supplied data without sampling:

```sh
python -B -m adaptive_tomography plot --results results/paper --output reproduced_figures
```

The paper outputs are `figure1_mixed.pdf` and `figure2_pure_bures.pdf`. The supplied bundle also includes optional covariance data, which the plot command draws as an additional comparison. The [algorithm correspondence](simulation/docs/ALGORITHM_CORRESPONDENCE.md), [settings](simulation/docs/REPRODUCIBILITY.md) and [data dictionary](simulation/docs/DATA_DICTIONARY.md) explain the arrays and batch experiment.

## Official numerical evidence: 20 October 2026

The [execution report](simulation/verification/20261020/FRESH_SIMULATION.md) records 37 passing tests and the full three-study run. Means and Monte Carlo errors were recalculated from every fresh replicate; physical ranges and both figures were checked. Mixed arrays reproduce bitwise and pure arrays agree within the recorded floating-point tolerance. A [separate audit](simulation/verification/20261020/INDEPENDENT_ALGORITHM_AUDIT.md) reconstructs the objectives, tests truth-blind fitting and generates altered-seed outputs with saved-array loading disabled.

The numerical source, configuration, tests and saved arrays are unchanged. These checks are numerical evidence and source review; the Python program is not mechanically verified by Lean. Finite simulations do not prove the asymptotic theorems.
