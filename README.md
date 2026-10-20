# Adaptive quantum tomography by least squares

Lean proofs and Python simulations accompanying **Adaptive quantum tomography by least squares with optimal asymptotic covariance**, by **Hongru Zhao** and **Robert Oliver VandenBerg**.

**[Read the main paper](https://github.com/HongruZhao/adaptive-quantum-tomography/blob/main/ejs_main.pdf).** This repository is private. Public release of this repository or a Zenodo record requires the authors' explicit approval. The supplement PDF is not hosted here.

The paper studies interior mixed qubits and pure states in fixed finite dimension. Learning a loss-optimal measurement design and estimating the state efficiently are separate tasks. The pure-state procedure uses a tangent-space correction to achieve inverse-information covariance.

| File | Contents |
|---|---|
| [MAIN_RESULTS.md](MAIN_RESULTS.md) | All nine numbered main results, with their printed statements and Lean correspondence |
| [SUPPLEMENT_RESULTS.md](SUPPLEMENT_RESULTS.md) | Supplementary statement scope and component proof correspondence |
| [lean/](lean/) | Reduced proof source tree, dependency pins, verification scripts and current evidence |
| [simulation/](simulation/) | Numerical implementation, tests, configuration and saved data |
| [LEAN_FORMALIZATION.md](LEAN_FORMALIZATION.md) | Formal assumptions and verification scope |
| [REPRODUCIBILITY.md](REPRODUCIBILITY.md) | Instructions for reproducing proof and simulation checks |

## Verify Lean

Install [elan](https://github.com/leanprover/elan), Git and Python 3.9 or newer, then run:

```sh
cd lean
python3 -B scripts/check_release.py
LAKE_ARTIFACT_CACHE=false python3 -B scripts/verify.py --cache --replay
```

The first command checks file integrity. The second builds every distributed project module, checks 498 main-paper and 138 supplementary declaration entries (with overlap), checks all retained mathematical declarations for unsupported axioms, and replays the designated modules. Dependency acquisition needs network access. Use a clean checkout for fresh project compilation; `--incremental` explicitly permits reuse. New receipts go to `lean/verification/reproduction/`.

For normal development after dependencies are available:

```sh
lake build
lake env lean SupplementAudit.lean
```

The toolchain is **Lean v4.33.0-rc2**, with Mathlib pinned to **641fbd329d4ffb62bef83c51f54088469056bd36**. Only pinned upstream dependencies are cached; project objects are not distributed.

## Run the simulations

Use Python **3.9–3.12**. From the repository root:

```sh
cd simulation
python3 -m venv .venv
source .venv/bin/activate
python -m pip install -r requirements.txt
export PYTHONPATH="$PWD/src"
python -B scripts/check_release.py
python -B -m unittest discover -s tests -v
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
  python -B -m adaptive_tomography run --replications 8 --max-power 10 --output results/smoke
python -B -m adaptive_tomography plot --results results/smoke --output results/smoke/figures
```

Use a new output directory for each run. To run the paper's full experiment, replace the run command's overrides with `--config configs/paper.json --output results/new_paper`. To redraw supplied data, use `python -B -m adaptive_tomography plot --results results/paper --output reproduced_figures`.

The paper figures are `figure1_mixed.pdf` and `figure2_pure_bures.pdf`. The supplied data also contain an optional covariance comparison, so saved-data plotting additionally draws that comparison. [REPRODUCIBILITY.md](REPRODUCIBILITY.md) explains the settings and data.

## Verification

The official evidence is dated **20 October 2026**. The [Lean report](lean/verification/20261020/README.md) separates source compilation, statement checks, axiom dependencies and kernel replay. The [Python report](simulation/verification/20261020/FRESH_SIMULATION.md) records **37 passing tests** and **10,000 replicates for each of three studies**, with **16,384 copies in 202 batches** per replicate. A [separate algorithm audit](simulation/verification/20261020/INDEPENDENT_ALGORITHM_AUDIT.md) checks the numerical procedures against Algorithms 1–3 and tests fresh generation.

All retained mathematical Lean declarations depend only on the standard logical axioms `propext`, `Classical.choice` and `Quot.sound`. The supplementary coverage table records the current restricted statements and their component proofs; the three identified scope differences are resolved without changing Lean. A successful build is not a claim of complete mechanical formalization of every sentence in the supplement. Lean does not mechanically verify the Python program or its numerical output.

## Citation and licenses

See [CITATION.cff](CITATION.cff). The software retains the MIT notices in [lean/LICENSE](lean/LICENSE) and [simulation/LICENSE](simulation/LICENSE). The manuscript PDF remains subject to its authors' rights; it is not assigned the software license. Dependencies retain their own licenses.
