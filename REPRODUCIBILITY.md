# Reproducibility

This repository separates mathematical proof checks, Python tests, small simulation runs, and saved-data plotting. Each establishes a different fact. **[The main article](https://github.com/HongruZhao/adaptive-quantum-tomography/blob/main/ejs_main.pdf)** is available to authorized collaborators while this repository is private. The supplement PDF is not included.

## Integrity checks

From the repository root:

```sh
python3 -B lean/scripts/check_release.py
python3 -B simulation/scripts/check_release.py
```

These Python-only commands compare packaged files with their manifests. They do not compile Lean or run simulations. The manifests identify the prepared code folders; separate dated receipts document earlier executions.

## Lean proof reproduction

Install Git, Python 3.9 or newer, and [elan](https://github.com/leanprover/elan). From the repository root:

```sh
cd lean
python3 -B scripts/verify.py --cache --replay
```

The command obtains pinned dependencies and their upstream cache, builds the selected 508-module current-result closure plus the explicit `MainPaper` and `MainPaperAudit` roots, checks 498 selected elaborated declaration types and their axiom sets, verifies dependency revisions, and replays 17 designated modules. First-run dependency/cache acquisition requires network access. The original toolchain is Lean v4.33.0-rc2; Mathlib is pinned to commit `641fbd329d4ffb62bef83c51f54088469056bd36`.

For a smaller ordinary development check after dependencies are available:

```sh
lake build MainPaper MainPaperAudit
lake env lean MainPaperAudit.lean
```

A clean verification run rejects existing project proof objects. The explicit `--incremental` flag permits their reuse. Upstream caches are distinct from project objects. New logs and receipts go to `lean/verification/reproduction/`, which is ignored by Git. The runner does not build every retained historical source, rebuild upstream Mathlib from source, or replay every dependency.

Read [LEAN_FORMALIZATION.md](LEAN_FORMALIZATION.md) for proof assumptions, result correspondence, and dated evidence. All 633 canonical sources are retained unchanged; the repository preparation is not a new full Lean build.

## Python environment and tests

Use Python 3.9–3.12. The saved experiments and the fresh 20 October smoke check used **Python 3.9.6, NumPy 1.26.4, and Matplotlib 3.9.4**. The two numerical libraries are pinned in `simulation/requirements.txt`.

From the repository root:

```sh
cd simulation
python3 -m pip install -r requirements.txt
export PYTHONPATH="$PWD/src"
python3 -B scripts/check_release.py
python3 -B -m unittest discover -s tests -v
```

These commands run the package directly from `src/`, so no editable installation is needed. To use an isolated environment, first create and activate one with `python3 -m venv .venv` and `source .venv/bin/activate`, then run the same installation and test commands. On Windows use `.venv\Scripts\activate`; in PowerShell set `$env:PYTHONPATH="$PWD/src"` instead of `export`.

The 37 tests cover literal small-record estimator objectives, complete outcome laws, predetermined schedules, safeguards, phase pairing, and diagnostics. Their fresh 20 October pass is a software check, not a formal proof of the Python implementation.

On a headless machine or when the default home cache is unwritable, set `MPLCONFIGDIR` to a writable directory and `MPLBACKEND=Agg`. The numerical algorithms do not depend on the display backend.

## Fresh smoke experiment

From `simulation/`, with `PYTHONPATH` set as above:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
  python3 -B -m adaptive_tomography run --replications 8 --max-power 10 --output results/smoke_20261020
python3 -B -m adaptive_tomography plot --results results/smoke_20261020 --output results/smoke_20261020/figures
```

This runs eight replicates for the mixed Bures, mixed Frobenius, and pure-state procedures, each with a maximum of 1,024 copies, and draws the two smoke figures. It uses the default current-paper configuration with the requested replicate/count overrides; no numerical source or configuration file is edited. Generated dated smoke outputs are ignored by Git. Use a new output directory when rerunning to preserve earlier records.

The 20 October smoke run completed successfully in the pinned environment, with finite valid loss arrays and successful figure generation. It is an execution/reproduction check, not a fresh run of the submitted 10,000-replicate studies.

## Redraw the supplied paper figures

```sh
python3 -B -m adaptive_tomography plot --results results/paper --output reproduced_figures
```

The command uses the supplied arrays and validates their summaries before plotting. The current article's figures are `figure1_mixed.pdf` and `figure2_pure_bures.pdf`, with PNG copies. Historical optional covariance data are also retained, so the command additionally redraws their older figure; it is not a current article figure.

Figure 1 uses the two mixed-qubit allocation rules. Figure 2 uses the pure-state procedure at dimension four, with preliminary and corrected estimates from the same records. Its reference experiment has 104 complete labels: two phase branches, thirteen bases, and four readouts. Each copy uses one selected four-outcome projective measurement.

## Full paper experiment

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
  python3 -B -m adaptive_tomography run --config configs/paper.json --output results/new_paper
python3 -B -m adaptive_tomography plot --results results/new_paper --output results/new_paper/figures
```

The principal supplied studies used 10,000 replicates and 16,384 copies per replicate, in 202 predetermined batches. After the first batch of sixteen, the nominal next batch size is `max(16, ceil(N/50))`, with $N$ the number already observed. Only the final batch is shortened to meet the fixed total. Reporting occurs at eighteen selected completed batches. The full experiment takes substantially longer than a smoke run.

Preserve `results/paper/`; use a new output directory. The default configuration runs the three current main-figure studies. `configs/historical_full_run_20261017.json` retains the older five-study configuration, including optional covariance studies that are not current article simulations.

## Evidence and limits

The [simulation verification guide](simulation/docs/VERIFICATION.md) and [saved package review](simulation/verification/PACKAGE_REVIEW_20261018.json) distinguish earlier full runs from later installation, test, smoke, and plotting checks. The repository preserves the numerical implementation and arrays. Raw historical execution logs stay outside the repository; two metadata exports explicitly omit machine-local paths.

All replicates contribute to the summaries. Saved arrays contain scaled losses and tangent errors, not every per-copy count record. A fixed seed and stream rule do not guarantee bitwise-identical adaptive paths across numerical environments. See [the data dictionary](simulation/docs/DATA_DICTIONARY.md) and [detailed numerical guide](simulation/docs/REPRODUCIBILITY.md) for stream roles, reporting endpoints, Monte Carlo uncertainty, and replay limits.

The dated snapshots inside the code folders identify the 18 October documentation edition. The root main PDF is a newer editorial revision with the same mathematical statements, assumptions, proof arguments, numbering, Lean sources, and numerical implementation. Earlier snapshot hashes intentionally retain their actual dates rather than being relabeled as the current PDF's hashes. No fresh full Lean build or full 10,000-replicate Monte Carlo rerun is claimed for the 20 October repository preparation.
