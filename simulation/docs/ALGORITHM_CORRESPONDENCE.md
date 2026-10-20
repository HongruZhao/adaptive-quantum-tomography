# Paper-to-code correspondence

The code uses the procedures printed in the current main paper. Array indices
start at zero; the paper's mixed-axis labels start at one. This changes labels,
not the selected effects or probabilities.

| Paper object | Implementation | Correspondence |
|---|---|---|
| Algorithms 1–2, mixed ridge objective | `mixed.trajectory` | Each sampled axis contributes its realized count to the Gram matrix; signed outcome counts form the right-hand side; every previous batch is retained. |
| Bures safeguard | `mixed.design_estimate` | Keep the raw estimate only inside the open Bloch ball, otherwise reset to zero. |
| Frobenius safeguard | `mixed.design_estimate` | Euclidean projection onto radius `sqrt(1-(n+1)^(-1/2))`. |
| Radial-first measurement axes | `mixed.measurement_design` | Exact `e3`-based Householder formula; `(e3,e1,e2)` at zero and the identity branch at radial direction `e3`. |
| Allocations | `mixed.measurement_design` | Bures `1/3,1/3,1/3`; Frobenius `(s(c),1,1)/(2+s(c))`. |
| Complete binary record | `mixed.trajectory` | Six setting-outcome masses `pi[k]*(1+y*v[k]^T*truth)/2`; batch multinomial sampling retains both labels. |
| Algorithm 3 reference seed | `pure.reference_measurement` | Coordinate and every real/imaginary two-level basis, followed by the prescribed fixed reflection; `B=D^2-D+1`. |
| Phase pairing | `pure.reference_measurement`, `estimators.phase_pair` | `V=diag(i,1,...,1)`; effects `F/2` and `V* F V/2`. The complete label is `(branch,basis,readout)`. |
| Alignment | `estimators.householder_frame` | Exact phase-adjusted formula sending `e0` to the preliminary unit vector. Only the preliminary fit selects subsequent alignments. |
| Categorical ridge objective | `pure.preliminary`, `pure.trajectory` | All labelled residual coordinates are included: a batch contributes `m F^T F`, not a Gram matrix weighted by observed setting frequencies. Complete POVM effects include the phase/basis selection factors. |
| Pure projection | `estimators.top_vector` | Largest algebraic eigenvalue, fixed computed-eigenvalue tie and phase rules; initial vector `e0`. |
| Fitted tangent correction | `pure.correction`, `estimators.weighted_tangent_update` | All past effects and residuals evaluated at the same final preliminary state; fixed floor `min reference mass/4`; Frobenius tangent ridge `eta I`. |
| Physical reported output | `pure.correction` | Normalize `h+Delta h`; no iterative likelihood maximization. |
| Batch schedule | `schedules.batch_sizes` | Initial 16 copies; nominal main size `max(16,ceil(N/50))`; final budget clipping only. The whole sequence is computed before sampling. |
| Reporting | `schedules.nearest_reporting_horizons` | Nearest actual completed-batch endpoints; ties choose the earlier endpoint; no inserted acquisition updates. |
| Information diagnostics | `mixed.information`, `pure.information` | Complete conditional information calculated at the truth; average matrices use actual preceding batch alignments and batch sizes. |
| Actual losses | `mixed.physical_losses`, `pure.physical_losses` | Paper's squared Bures/fidelity convention and squared Frobenius norm. Pure Bures evaluation uses stable phase-aligned vector distance. |
| Optional covariance comparison (not a current-paper figure) | `optional`, `simulation._covariance_summary` | Preserve repeated effect labels and compare the preliminary/corrected estimates on the same adaptive records; use unbiased sample covariance with divisor `R-1`. |

For a batch with a fixed measurement, complete multinomial outcome counts are
sufficient for every displayed objective and update. Grouping repeated shots
therefore changes storage and computation, not the conditional experiment or
the estimator. The paper permits predetermined finite batches; this release
uses predetermined growing batches for the main figures; the optional covariance comparison uses doubling batches, with no data-dependent stopping rule. The main
reports occur at actual completed batches; selecting reporting targets does
not change acquisition or design updates.

The tests independently expand small grouped records into the literal
per-copy objectives and compare the resulting fits. They also check branch
probabilities, reference information, the floor, alignment, axis edge cases,
tie rules and unreachable reporting sizes. The independent audit is in
`../verification/20261020/INDEPENDENT_ALGORITHM_AUDIT.md`; the full fresh run receipt is
`../verification/20261020/FULL_RUN_RECEIPT.json`.

These checks concern the numerical implementation. Lean source checking of
the main-paper mathematical results is provided in the repository's `lean/` directory; it is not a formal verification of this Python program.

## Current manuscript locations

The main algorithms are in Sections 3 and 4. The reference construction is Supplement S5, the tangent-solve implementation is Algorithm S1 in Supplement S2.7, and the written limit proofs are in Supplement S1.2-S1.3. Theoretical covariance-example calculations remain in S8; the optional numerical comparison is separate from the main figures. Parts I and II of the supplement separate main-result proofs from supporting technical results.
