# Official numerical verification: 20 October 2026

| Check | Passed scope |
|---|---|
| Tests | 37 tests, zero failures |
| Full paper run | Three studies, 10,000 replicates each; 16,384 copies in 202 batches per replicate |
| Fresh outputs | Every loss mean and Monte Carlo error recomputed; finite values, physical ranges and design criteria checked |
| Figures | Both paper figures rendered from fresh samples |
| Independent review | Five check groups comparing Algorithms 1–3 with source code, dense objectives, physical probabilities, truth-blind fits, edge cases and fresh altered-seed sampling |

The [execution report](../verification/20261020/FRESH_SIMULATION.md), [run receipt](../verification/20261020/FULL_RUN_RECEIPT.json), [output checks](../verification/20261020/EXECUTION_CHECKS.json) and [test output](../verification/20261020/TEST_OUTPUT.txt) record the actual commands and timestamps. The environment was Python 3.9.6 / NumPy 1.26.4 / Matplotlib 3.9.4.

After fresh generation, principal arrays were compared with supplied data at `rtol=atol=1e-10`. Mixed loss arrays were bitwise identical. Maximum absolute differences were `6.79e-11` for pure losses, `1.32e-11` for tangent errors and `4.99e-12` for pure design criteria, all within tolerance. The supplied arrays were not overwritten. Optional covariance experiments were not rerun at full size.

The [independent audit](../verification/20261020/INDEPENDENT_ALGORITHM_AUDIT.md) and [runnable checker](../verification/20261020/independent_checks.py) found no main-algorithm mismatch, hidden truth-dependent fitting, replicate filtering or manufactured-result path within their checked scope. The execution checks also instrumented nine histories with 1,818 newly sampled batch-count draws while blocking saved-result reads.

The execution receipts preserve the exact inputs tested at execution time. [CURRENT_PAPER_BINDING.json](../verification/CURRENT_PAPER_BINDING.json) identifies the current main PDF separately; documentation or typesetting updates do not rerun a simulation. The numerical implementation and experiment configuration are unchanged. These are finite checks and source review, not a proof that every possible numerical bug is absent or a mechanical verification of Python by Lean.
