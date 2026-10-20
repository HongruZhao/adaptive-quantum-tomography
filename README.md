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
LAKE_ARTIFACT_CACHE=false python3 -B scripts/verify.py --cache --replay
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

**Fresh checks passed on 20 October 2026.** The [Lean report](lean/verification/20261020/README.md) records 508 project modules compiled from source, 498 declaration types and transitive axiom sets checked, all nine main results covered by 17 mapped declarations, and 17 selected modules kernel replayed. All selected axiom sets contain only `propext`, `Classical.choice` and `Quot.sound`. Pinned upstream library objects were reused; all 633 retained sources and the paper stayed unchanged.

The [Python report](simulation/verification/20261020/FRESH_SIMULATION.md) records 37 passing tests and a fresh full paper run: 10,000 replicates for each of three studies, with 16,384 copies and 202 batches per replicate. Every loss mean and Monte Carlo error was checked and both figures rendered. Mixed arrays reproduce bitwise; pure arrays agree within the recorded floating-point tolerance. A [separate independent audit](simulation/verification/20261020/INDEPENDENT_ALGORITHM_AUDIT.md) found no main-algorithm mismatch or manufactured-result path and supplies additional runnable checks.

The [final verification table](MAIN_RESULTS.md#what-was-actually-verified) distinguishes these new executions from older evidence. The selected Lean checks do not establish an axiom-free build of every historical declaration or replay of every dependency. Twelve documented legacy scientific axiom leaves remain outside the selected endpoint dependencies. Lean does not mechanically verify the Python implementation or Monte Carlo values.

## Citation and licenses

Citation metadata are in [CITATION.cff](CITATION.cff). The proof and simulation software retain their existing MIT notices in [lean/LICENSE](lean/LICENSE) and [simulation/LICENSE](simulation/LICENSE). The manuscript PDF has not been assigned a software license by this preparation; manuscript rights remain with its authors. Pinned dependencies retain their own licenses.
