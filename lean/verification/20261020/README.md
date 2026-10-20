# Fresh Lean verification — 20 October 2026

**PASS.** The published GitHub Lean project was freshly compiled on 20 October 2026 (America/Chicago) from an empty project build directory. The unchanged project roots are `MainPaper` and `MainPaperAudit`.

## Exactly what ran

```sh
cd lean
python3 -B scripts/verify.py --replay
```

The nine dependency repositories were already available at their exact pinned revisions, so this execution reused their cached upstream objects and did not need `--cache`. A new checkout may use `--cache --replay`. No old project proof objects were reused. Lake permits local artifact-cache reads by default, so freshness was also checked directly: all 508 modules logged a `Built` action and have a non-synthetic trace recording the pinned compiler on the current checkout source path; no project cache fetch/unpack/restore was found. Every compiler setup also resolves all project imports to the fresh checkout build tree. [Freshness audit](FRESHNESS_CHECKS.json).

- 508 project modules freshly source-compiled: independently confirmed to be exactly the `MainPaper`/`MainPaperAudit` project import closure. Both root targets passed.
- 498 selected elaborated declaration types exactly matched the saved reference inventory. All 498 transitive axiom sets contained only `propext`, `Classical.choice`, and/or `Quot.sound`; no selected declaration depends on `sorryAx` or a nonstandard scientific axiom.
- All 211 endpoints in the 43-group paper correspondence ledger occurred in that freshly checked inventory.
- All nine printed principal results passed through their exact mapped endpoints, including 17 group endpoints/bridges. See [per-result checks](MAIN_ENDPOINT_CHECKS.json). Theorems 3.1/3.2 share one combined endpoint; Theorems 4.2/4.3 share another.
- 17 selected modules were freshly kernel replayed, including every principal result's defining module. The supplementary covariance-identity bridge was freshly source-compiled and type/axiom audited; its module was not one of the 17 explicitly replayed modules.
- All 633 retained `.lean` source files, `lakefile.toml`, toolchain, dependency manifest, and verification script remained byte-identical. All 508 new project `.olean` timestamps fall on 20 October 2026 in America/Chicago and postdate the run start.

The separate [independent statement-to-endpoint review](ENDPOINT_INDEPENDENT_REVIEW.md) checks the nine paper statements against their formal hypotheses and conclusions; it is distinct from the execution receipts above.

## Reproducibility correction

A local preflight found that `BUILD_INPUTS.json` retained an old expected hash for `lakefile.toml`. The existing GitHub lakefile matched the 17 October native full-project file exactly. Only the verification metadata hash was repaired; the lakefile and Lean sources were unchanged. The initial assertion occurred before Lean execution and is not a failed compilation. [Exact repair evidence](VERIFICATION_METADATA_REPAIR.json).

## Scope boundary

This is a fresh build of the 508-module current-paper project closure, not of all 633 retained source files. Pinned upstream dependency libraries were reused, not rebuilt. Kernel replay covered 17 selected modules, not every project module or every upstream dependency. Type/axiom checks establish the selected formal statements; their relationship to the paper remains the explicit semantic correspondence documented in `MAIN_RESULTS.md` and the ledger.

## Receipts

[Summary and dates](SUMMARY.json), [commands](COMMANDS.json), [source hashes](SOURCE_SHA256.json), [new object hashes and timestamps](OBJECT_SHA256_AND_TIMESTAMPS.json), [elaborated types](ELABORATED_STATEMENTS.json), [transitive axioms](TRANSITIVE_AXIOMS.json), [import closure](IMPORT_CLOSURE.json), [search-root boundary](SEARCH_ROOTS.json). Raw build/audit/replay output is retained in the local dated audit, and a repeat invocation produces a new `verification/reproduction/` directory.
