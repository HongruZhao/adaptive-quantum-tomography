# Saved formal verification evidence

The [20261020/ report](20261020/README.md) records the newly executed 20 October source build, statement/axiom checks, nine-result endpoint review and selected kernel replay. The other dated files below preserve earlier verification evidence; they have not been relabelled as new runs. Raw execution logs, caches, compiled objects, machine-local locators, and the complete initial preflight log are retained in the authors' working archive and are not bundled here.

- `20261020/`: fresh 508-module source compilation, 498 types/axioms, nine main results / 17 mapped declarations, 17 selected-module replays, compiler/import freshness receipts and metadata-only preflight repair.
- `VERIFICATION_SUMMARY.json`: 17 October fresh 567-module source build, selected declaration audit, and 17-module replay summary.
- `BUILD_INPUTS.json`: source hashes, topological build order, and replay list for the 508-module current-result closure used by `scripts/verify.py`.
- `CANONICAL_SOURCE_SHA256.json`: all 633 canonical source hashes, newly copied and compared for package integrity only.
- `EXPECTED_DECLARATIONS.json`, `ELABORATED_STATEMENTS.json`, `TRANSITIVE_AXIOMS.json`: 498 selected declaration names, elaborated types, and transitive axiom sets.
- `LEGACY_AXIOM_INVENTORY.json`: twelve retained scientific axiom leaves in the audited imported environment; selected endpoint intersection is empty.
- `DEPENDENCY_PINS.json`: saved dependency revision evidence, with original pins also in `lean-toolchain` and `lake-manifest.json`.
- `KERNEL_REPLAY.json`: saved seventeen-module replay result.
- `theorem51_review_20261019/`: saved focused seven-module replay and sixteen-declaration audit for the adaptive lower bound.

The historical summary uses older paper-result grouping in some fields. Current numbering is in [the paper-to-Lean guide](../docs/PAPER_TO_LEAN.md). No source-integrity check proves theorem correspondence or a new build. See [the root guide](../../LEAN_FORMALIZATION.md).
