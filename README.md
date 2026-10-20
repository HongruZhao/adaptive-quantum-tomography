# Adaptive quantum tomography by least squares

Lean proof sources and Python simulations accompanying **Adaptive quantum tomography by least squares with optimal asymptotic covariance**, by **Hongru Zhao** and **Robert Oliver VandenBerg**.

**[Read the main paper](https://github.com/HongruZhao/adaptive-quantum-tomography/blob/main/ejs_main.pdf).** This repository is currently private; the paper link and source files are accessible to authorized collaborators. The supplement PDF is not hosted in this repository.

The development treats interior mixed qubits and pure states in each fixed finite dimension. It distinguishes learning a loss-optimal measurement design from constructing an estimator that uses its information efficiently. [MAIN_RESULTS.md](MAIN_RESULTS.md) states the formal results and their Lean entry points. [LEAN_FORMALIZATION.md](LEAN_FORMALIZATION.md) explains assumptions, correspondence, and verification scope.

## Files

| Item | Purpose |
|---|---|
| [ejs_main.pdf](https://github.com/HongruZhao/adaptive-quantum-tomography/blob/main/ejs_main.pdf) | Main article |
| [MAIN_RESULTS.md](MAIN_RESULTS.md) | Mathematical statements and corresponding Lean declarations |
| [lean/](lean/) | All 633 canonical Lean source files and original dependency pins |
| [simulation/](simulation/) | Python implementation, configurations, tests, and saved numerical data |
| [LEAN_FORMALIZATION.md](LEAN_FORMALIZATION.md) | Proof assumptions and dated verification evidence |
| [REPRODUCIBILITY.md](REPRODUCIBILITY.md) | Detailed proof and numerical reproduction instructions |

## Run and verify Lean

Install [elan](https://github.com/leanprover/elan), Git, and Python 3.9 or newer. From the repository root:

```sh
cd lean
python3 -B scripts/check_release.py
python3 -B scripts/verify.py --cache --replay
```

The first command verifies package hashes only. The second obtains the pinned upstream cache, builds the 508-module current-result closure and the explicit `MainPaper` and `MainPaperAudit` roots, checks 498 selected declarations and their transitive axioms, and requests kernel replay of 17 selected modules. First-run dependency acquisition needs network access. Use a clean checkout for fresh project compilation; add `--incremental` only when intentionally reusing project proof objects. New receipts are written to `lean/verification/reproduction/`.

For normal development after dependencies are available:

```sh
lake build MainPaper MainPaperAudit
lake env lean MainPaperAudit.lean
```

The toolchain is Lean **v4.33.0-rc2**, with Mathlib commit **641fbd329d4ffb62bef83c51f54088469056bd36**. The original broader Lake defaults are preserved; the commands above select the main-paper roots explicitly.

## Run the Python simulations

Use Python **3.9–3.12**. From the repository root, enter `simulation/`, install the pinned numerical dependencies, and make its source package importable:

```sh
cd simulation
python3 -m pip install -r requirements.txt
export PYTHONPATH="$PWD/src"
python3 -B scripts/check_release.py
python3 -B -m unittest discover -s tests -v
```

Run these commands in a virtual environment if you do not want to use your existing Python environment. The commands execute the package directly from `src/`; an editable package installation is not required. The test suite has 37 tests.

Run an eight-replicate, 1,024-copy smoke experiment and plot its results:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
  python3 -B -m adaptive_tomography run --replications 8 --max-power 10 --output results/smoke_20261020
python3 -B -m adaptive_tomography plot --results results/smoke_20261020 --output results/smoke_20261020/figures
```

Use a new output directory if that name already exists. To redraw the supplied paper data without sampling:

```sh
python3 -B -m adaptive_tomography plot --results results/paper --output reproduced_figures
```

The current paper figures are `figure1_mixed.pdf` and `figure2_pure_bures.pdf`. The saved bundle also retains historical optional covariance data, so the plot command additionally draws its older figure. A smoke run is separate from the principal 10,000-replicate studies. See [REPRODUCIBILITY.md](REPRODUCIBILITY.md) for the full run, settings, data dictionary, and tested environment.

## Verification evidence and limits

The 17 October 2026 saved evidence records a fresh source build of 567 project modules in the larger native workspace, audits of 498 selected declarations, and kernel replay of 17 selected modules. The 19 October focused review replayed seven existing source-identical proof modules and inspected sixteen declarations. For audited selected endpoints, only `propext`, `Classical.choice`, and `Quot.sound` occur. Twelve scientific axiom leaves in retained imported historical material are inventoried separately and do not enter those selected endpoint dependencies.

**The entire 633-source tree is not asserted to be axiom free or freshly rebuilt by this repository preparation.** The dated receipts do not establish a new build when the repository is downloaded. The Lean mathematics does not mechanically verify the Python implementation or Monte Carlo values. The 20 October Python checks include 37 fresh tests and a fresh eight-replicate smoke experiment with plotting; they are not a new full 10,000-replicate run.

## Citation and licenses

Citation metadata are in [CITATION.cff](CITATION.cff). The proof and simulation software retain their existing MIT notices in [lean/LICENSE](lean/LICENSE) and [simulation/LICENSE](simulation/LICENSE). The manuscript PDF has not been assigned a software license by this preparation; manuscript rights remain with its authors. Pinned dependencies retain their own licenses.
