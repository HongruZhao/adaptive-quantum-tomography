# Adaptive quantum tomography by least squares

Research companion to **Adaptive quantum tomography by least squares with optimal asymptotic covariance**, by **Hongru Zhao** and **Robert Oliver VandenBerg**.

The paper analyzes explicit least-squares estimators under repeated adaptive measurement selection. It treats interior mixed qubits and pure states in every fixed finite dimension. The repository contains the paper, its supplement, all 633 canonical Lean source files, and the simulation implementation and saved data used for the main figures.

## The result

A good measurement design and an efficient estimator are different requirements. The reported estimators in this paper achieve both: the conditional classical Fisher information converges to the specified loss-optimal target, and the limiting estimation covariance is its inverse. For pure states, a preliminary ridge estimate chooses the next measurement alignment; a weighted correction on its fitted tangent space produces the efficient reported estimate.

Writing $\mathcal I^\star$ for the limiting single-copy information in the same local coordinates as the parameter $\theta$, the reported estimator satisfies

```math
\sqrt n(\widehat\theta_n-\theta_0)
\;\Longrightarrow\;
\mathcal N\!\left(0,(\mathcal I^\star)^{-1}\right).
```

The conclusions are pointwise at each fixed truth and dimension. Measurements may be updated after any predetermined positive finite batch sizes; reporting limits are taken at completed batches. Proved moment bounds also give the corresponding expected squared Bures and Frobenius loss limits. These are not uniform minimax or finite-sample optimality claims.

Read [the main results](MAIN_RESULTS.md) for precise models, information targets, loss constants, and scope. The finite-sample adaptive lower bound compares locally unbiased coordinate estimators; the reported physical estimators may be biased and attain the benchmark asymptotically.

## Read the paper and code

| Item | Start here |
|---|---|
| Main article | [ejs_main.pdf](ejs_main.pdf) |
| Supplement | [ejs_supplement.pdf](ejs_supplement.pdf) |
| Mathematical claims and their limits | [MAIN_RESULTS.md](MAIN_RESULTS.md) |
| Lean results, assumptions, and dated verification evidence | [LEAN_FORMALIZATION.md](LEAN_FORMALIZATION.md) |
| Rebuild or reproduce a figure | [REPRODUCIBILITY.md](REPRODUCIBILITY.md) |
| Proof-source project | [lean/README.md](lean/README.md) |
| Simulation implementation and saved arrays | [simulation/README.md](simulation/README.md) |

```text
.
├── ejs_main.pdf
├── ejs_supplement.pdf
├── README.md
├── MAIN_RESULTS.md
├── LEAN_FORMALIZATION.md
├── REPRODUCIBILITY.md
├── CITATION.cff
├── lean/              # all 633 canonical Lean sources and pinned dependencies
└── simulation/        # Python implementation, configurations, tests, saved data
```

## Lean evidence and its boundary

The source tree retains both the current result development and historical material. **The entire 633-file tree is not asserted to be axiom free or freshly rebuilt by this repository preparation.** The current main-result dependency closure has 508 modules. The saved 17 October 2026 verification records a fresh source build of 567 project modules in the larger native workspace, audits of 498 selected declarations, and kernel replay of 17 selected modules. For those selected declarations, only the standard logical axioms `propext`, `Classical.choice`, and `Quot.sound` occur. Twelve legacy scientific axiom leaves in the retained imported environment are documented separately and excluded from the selected endpoint dependencies.

A focused 19 October check replayed seven existing source-identical proof modules and inspected 16 relevant declarations for the adaptive lower bound. It was not a fresh full source build. The saved receipts are dated evidence, not new execution on downloading this repository. See [LEAN_FORMALIZATION.md](LEAN_FORMALIZATION.md) for entry points and reproduction instructions.

## Quick checks

With Python installed, check the packaged source and data hashes without running Lean or simulations:

```sh
python3 -B lean/scripts/check_release.py
python3 -B simulation/scripts/check_release.py
```

For Lean reproduction, install [elan](https://github.com/leanprover/elan), then run from `lean/`:

```sh
python3 -B scripts/verify.py --cache --replay
```

For Python installation, tests, and saved-data plotting, use the commands in [REPRODUCIBILITY.md](REPRODUCIBILITY.md). The saved principal studies used 10,000 replicates; a smoke run is a separate execution check. The Lean development does not mechanically verify the Python implementation or numerical Monte Carlo values.

## Citation and licenses

Citation metadata are in [CITATION.cff](CITATION.cff). The Lean and Python software retain their existing MIT notices in [lean/LICENSE](lean/LICENSE) and [simulation/LICENSE](simulation/LICENSE). No software license is assigned here to the manuscript PDFs; manuscript rights remain with their authors. Pinned third-party dependencies retain their own licenses.
