# Verification instructions

Use the [root formalization guide](../../LEAN_FORMALIZATION.md) for exact dated evidence, scope, and assumptions.

```sh
python3 -B scripts/check_release.py
python3 -B scripts/verify.py --cache --replay
```

Run these from `lean/`. The first command is an integrity check. The second builds the 508-module current-result closure and explicit `MainPaper` and `MainPaperAudit` roots, checks the 498 selected declaration types and transitive axiom sets, verifies pinned dependency revisions, and requests replay of 17 selected modules. It does not claim a build of all 633 retained sources or replay of every dependency.

A clean run rejects existing project proof objects; `--incremental` permits their reuse. New logs and receipts go to `verification/reproduction/`. Network access is needed for initial pinned dependencies and cache acquisition.

The 17 October summary records the larger workspace's 567-module source build. The 19 October receipt records a seven-module focused replay of existing source-identical objects. These are saved, dated evidence, not new execution performed by the 20 October GitHub preparation. The selected endpoints use only standard logical axioms; the documented retained legacy axioms are not silently promoted to verified hypotheses.
