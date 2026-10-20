# Verification

The official evidence is in [verification/20261020](../verification/20261020/README.md). It records the source inventory, dependency pins, exact declaration types, transitive axioms and actual replay list for the distributed source tree.

```sh
python3 -B scripts/check_release.py
LAKE_ARTIFACT_CACHE=false python3 -B scripts/verify.py --cache --replay
```

The first command verifies packaged hashes only. The second builds all project modules, runs the main and supplementary audits, verifies exact saved types and standard-only axioms, checks pins, and replays the designated modules. Fresh project compilation uses an empty project build directory; upstream pinned dependencies may use caches. `--incremental` records intentional object reuse.

The main audit checks 498 declaration entries. The supplementary audit checks 138 entries and traverses the type/value dependencies of every retained mathematical declaration. Overlap between these inventories is reported, not counted twice as distinct results. The audit rejects any axiom other than `propext`, `Classical.choice` and `Quot.sound`, including `sorryAx`.

The source build checks proof terms, while separate `leanchecker` replay provides the additional evidence described by its module list. Neither step mechanically establishes LaTeX-to-Lean semantic correspondence or verifies the Python implementation. The correspondence ledgers and the current supplementary scope audit state the precise coverage and component correspondence.
