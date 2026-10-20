# Official Lean verification: 20 October 2026

**PASS for the distributed source tree and the documented statement scope.**

| Check | Passed |
|---|---|
| Fresh project build | All **271 distributed source modules** compiled, beginning with zero project proof objects |
| Current-source binding | All 271 compiler-trace source hashes match current files using Lake's own text hashing; **10,369 project import bindings** resolve inside the clean build |
| Main declaration audit | **498** elaborated types match exactly; all **nine main results**, seven principal groups and **17 mapped declarations** included; all 211 correspondence-ledger declarations present |
| Supplementary audit | **138** entries checked; **131** preserved types match exactly and seven further moment/tail consequences are proved |
| Distinct selected declarations | **621**; the two inventories overlap |
| Whole retained mathematical axiom audit | **5,565 declarations** and all their transitive dependencies checked; only `propext`, `Classical.choice`, `Quot.sound` |
| Independent kernel replay | **30 modules** passed with `leanchecker`; the exact list is in [SUMMARY.json](SUMMARY.json) |
| Proof preservation | **2,268 retained original declaration blocks** unchanged; main statement types and hypotheses preserved |
| Dependency pins | All nine upstream package revisions match the pinned manifest |

The fresh build and the portable-verifier test are distinct checks. The build started with an empty project object directory; [FRESHNESS_CHECKS.json](FRESHNESS_CHECKS.json) checks actual compiler actions and current source hashes. The portable command was then tested on that completed build with the explicit `--incremental --replay` flags; [PORTABLE_RUN.json](PORTABLE_RUN.json) accurately records object reuse for that test. Its 30-module replay is new execution. Upstream pinned library objects were cached; upstream Mathlib was not rebuilt or completely replayed.

The [main endpoint receipt](MAIN_ENDPOINT_CHECKS.json), [elaborated main types](ELABORATED_STATEMENTS.json), [supplementary types](SUPPLEMENT_ELABORATED_STATEMENTS.json), [source inventory](SOURCE_SHA256.json) and [preservation receipt](SOURCE_AND_STATEMENT_PRESERVATION.json) identify the checked payload. [PORTABLE_COMMANDS.json](PORTABLE_COMMANDS.json) and [AUDIT_LOG_SHA256.json](AUDIT_LOG_SHA256.json) identify actual commands and local raw logs. The raw machine logs, compiled objects and caches are not distributed.

**Coverage limit:** this is not a complete formalization of every printed supplementary formulation. Lemmas S4.1, S4.2 and S6.2 have the precise generality differences recorded in [SUPPLEMENT_RESULTS.md](../../../SUPPLEMENT_RESULTS.md). The proved instances used by the main algorithms are retained. No conclusion is supplied as an assumption to disguise these differences. Source compilation and axiom checking do not mechanically establish LaTeX-to-Lean semantic correspondence or verify Python.

## Reproduce

From `lean/`, after installing Git, Python and elan:

```sh
python3 -B scripts/check_release.py
LAKE_ARTIFACT_CACHE=false python3 -B scripts/verify.py --cache --replay
```

The second command requires an empty project build directory; `--incremental` permits and records reuse. It writes new timestamped reports to `verification/reproduction/`. The toolchain is Lean v4.33.0-rc2 with Mathlib commit `641fbd329d4ffb62bef83c51f54088469056bd36`.

This repository is private. Public GitHub or Zenodo release requires explicit author approval.
