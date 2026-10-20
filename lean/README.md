# Adaptive quantum tomography: Lean proofs

This directory contains the reduced proof source tree for the accompanying main results and the supplementary statements documented in [SUPPLEMENT_RESULTS.md](../SUPPLEMENT_RESULTS.md). It contains no scientific input axioms or unfinished proof placeholders. The explicit hypotheses of the retained theorems are unchanged.

## Run

Install [elan](https://github.com/leanprover/elan), Git and Python 3.9 or newer:

```sh
python3 -B scripts/check_release.py
LAKE_ARTIFACT_CACHE=false python3 -B scripts/verify.py --cache --replay
```

The verifier builds all project modules, compares elaborated statement types, audits transitive axioms, checks dependency pins and replays the designated modules. It rejects existing project objects unless `--incremental` is requested. Receipt files are written to `verification/reproduction/`. The integrity command alone is not proof verification.

After dependencies are available, ordinary development uses:

```sh
lake build
lake env lean SupplementAudit.lean
```

The defaults are `MainPaperAudit` and `SupplementAudit`; all distributed modules are in their import closure. `MainPaper.lean` selects main results. `Supplement.lean` adds supporting results. `MainPaperTheorem31.lean` supplies the combined mixed-qubit endpoint.

## Read

- [Main results](../MAIN_RESULTS.md): printed statements, assumptions and entry points.
- [Supplementary coverage](../SUPPLEMENT_RESULTS.md): current checked cases and component correspondence.
- [Formalization scope](../LEAN_FORMALIZATION.md): interfaces and evidence boundaries.
- [Code guide](docs/CODE_GUIDE.md): proof structure and reading order.
- [Official verification](verification/20261020/README.md): current source, type, axiom and replay evidence.

Lean **v4.33.0-rc2** and Mathlib **641fbd329d4ffb62bef83c51f54088469056bd36** are pinned. Project proof objects and upstream caches are not distributed. The only transitive axioms of retained mathematical declarations are `propext`, `Classical.choice` and `Quot.sound`.

The current supplement uses the fixed selection, almost-sure consistency and actual-procedure cases represented by the unchanged Lean code; the scope audit distinguishes component proofs from combined endpoints. Lean does not verify the companion Python program. The repository and prepared Zenodo archive require explicit author approval before public release. The code retains its MIT license.
