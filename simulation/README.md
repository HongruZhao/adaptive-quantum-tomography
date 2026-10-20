# Adaptive quantum tomography: simulations

Python implementation of Algorithms 1–3 for **Adaptive quantum tomography by least squares with optimal asymptotic covariance**, by Hongru Zhao and Robert Oliver VandenBerg. The [main paper](../ejs_main.pdf) has 34 pages. This repository is private.

## Install and test

Use Python **3.9–3.12**; the tested numerical libraries are pinned in `requirements.txt`:

```sh
python3 -m venv .venv
source .venv/bin/activate
python -m pip install -r requirements.txt
export PYTHONPATH="$PWD/src"
python -B scripts/check_release.py
python -B -m unittest discover -s tests -v
```

On Windows use `.venv\Scripts\activate`. These commands run directly from `src/`; an editable package installation is unnecessary.

## Run

Small fresh experiment:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
  python -B -m adaptive_tomography run --replications 8 --max-power 10 --output results/smoke
python -B -m adaptive_tomography plot --results results/smoke --output results/smoke/figures
```

Full paper experiment:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
  python -B -m adaptive_tomography run --config configs/paper.json --output results/new_paper
python -B -m adaptive_tomography plot --results results/new_paper --output results/new_paper/figures
```

Use a new output directory. To redraw supplied data, use `python -B -m adaptive_tomography plot --results results/paper --output reproduced_figures`. The paper outputs are `figure1_mixed.pdf` and `figure2_pure_bures.pdf`. The supplied arrays also contain an optional covariance comparison, so saved-data plotting draws one additional figure.

## Experiment and evidence

Figure 1 uses Algorithms 1–2; Figure 2 uses Algorithm 3 in dimension 4. The configuration specifies 10,000 replicates per study, 16,384 copies and 202 predetermined batches per replicate. At dimension 4, the 104 complete labels represent two phase branches, 13 bases and four outcomes. Each copy uses one selected four-outcome projective measurement. Grouped multinomial counts give the same objectives as the corresponding individual complete records.

The official **20 October 2026** [execution report](verification/20261020/FRESH_SIMULATION.md) records **37 passing tests** and a fresh full three-study run in **757.04 seconds**, using Python 3.9.6 / NumPy 1.26.4 / Matplotlib 3.9.4. Means, Monte Carlo errors, physical ranges and both paper figures were checked. A [separate algorithm audit](verification/20261020/INDEPENDENT_ALGORITHM_AUDIT.md) ran five independent check groups, including dense objective reconstruction, truth-blind fitting and fresh altered-seed generation with saved-array loading disabled.

No numerical source, test, configuration or supplied array was changed during this release preparation. The [code guide](docs/CODE_GUIDE.md), [algorithm correspondence](docs/ALGORITHM_CORRESPONDENCE.md), [settings](docs/REPRODUCIBILITY.md) and [data dictionary](docs/DATA_DICTIONARY.md) explain the implementation. Numerical checks and source review are distinct from Lean verification; Lean does not mechanically verify this Python program. The software retains its MIT license.
