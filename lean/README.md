# Adaptive quantum tomography: Lean sources

This folder contains all **633 canonical Lean source files**, together with the original toolchain, Lake configuration, and dependency pins. It includes the current result development and retained historical material. The [root formalization guide](../LEAN_FORMALIZATION.md) explains verification scope, hypotheses, and endpoint correspondence.

## Start here

| Task | File or command |
|---|---|
| Match current paper results to Lean | [docs/PAPER_TO_LEAN.md](docs/PAPER_TO_LEAN.md) |
| Read principal source entry points | [docs/CODE_GUIDE.md](docs/CODE_GUIDE.md) |
| Check prepared-package hashes only | `python3 -B scripts/check_release.py` |
| Reproduce selected proof and axiom checks | `python3 -B scripts/verify.py --cache --replay` |
| Inspect dated verification evidence | [verification/README.md](verification/README.md) |

The paper has nine named theorems, propositions, and corollaries. Existing Lean identifiers bundle some split paper statements: `theorem_3_1` contains current Theorems 3.1 and 3.2, and `theorem_4_2` contains current Theorems 4.2 and 4.3. `Inputs` lists hypotheses; the proving theorem supplies its `Conclusions`.

## Build selected current results

Install Git, Python 3.9 or newer, and [elan](https://github.com/leanprover/elan). The pins specify Lean **v4.33.0-rc2** and Mathlib **641fbd329d4ffb62bef83c51f54088469056bd36**.

```sh
python3 -B scripts/check_release.py
python3 -B scripts/verify.py --cache --replay
```

The first command checks file integrity only. The second builds the 508-module current-result closure, builds the explicit `MainPaper` and `MainPaperAudit` roots, inspects 498 selected declaration types and axiom sets, checks dependency revisions, and replays 17 selected modules. It writes new timestamped receipts under `verification/reproduction/`. A fresh run rejects existing project proof objects; use `--incremental` only to expressly reuse them. Upstream caches are separate from project proof objects.

For ordinary development after dependencies are installed:

```sh
lake build MainPaper MainPaperAudit
lake env lean MainPaperAudit.lean
```

The original `lakefile.toml` remains unchanged. Its plain `lake build` defaults are broader: `AdaptiveTomography` and `MainPaperAudit`. Neither command claims to compile every retained historical source.

## Evidence boundary

The saved 17 October 2026 evidence records a fresh build of 567 project modules in the larger native workspace, audits of 498 selected declarations, and replay of 17 selected modules. The 19 October focused adaptive-bound review replays seven existing source-identical proof modules and inspects sixteen declarations. Neither is a fresh full build performed during this repository preparation.

The audited selected declarations use only standard logical axioms. Twelve legacy scientific axiom leaves in retained imported historical material are inventoried separately and do not enter those selected endpoint dependencies. **No axiom-free claim is made for every declaration in the full 633-source tree.** This development does not mechanically verify Python code, Monte Carlo values, hardware, runtime, or literature attribution.

## Files and license

- [MainPaper.lean](MainPaper.lean): public imports for current main results.
- [MainPaperAudit.lean](MainPaperAudit.lean): selected statement and axiom audit.
- [AdaptiveTomography.lean](AdaptiveTomography.lean): original broader project entry.
- `QubitOracle/Paper/`: current-result interfaces and supporting bridges.
- `QubitOracle/AdaptiveDesign/`: estimator, adaptive policy, information, and probability arguments.
- `docs/`: correspondence guides and current label maps.
- `verification/`: curated dated evidence and source hashes; raw logs are omitted.

The existing MIT license and original software-author metadata are preserved. The paper PDFs have not been assigned a software license by this preparation. No new build or publication follows merely from reading these saved receipts.
