# Independent simulation–paper algorithm audit

**Review date: 20 October 2026 (America/Chicago). Verdict: PASS for the reviewed main-paper implementation and the fresh finite checks below. No algorithm substitution, truth-dependent design, discarded replicate, or manufactured simulation curve was found.**

This review was assigned separately from the execution agent. It inspected the GitHub simulation sources against the unchanged current paper and wrote additional numerical checks independently of the package's existing 37 unit tests. The paper, numerical implementation, configurations, archived numerical results, and all 633 Lean source files were kept unchanged. This report does not claim that Python has been formally verified in Lean, or that finite numerical checks prove the paper's asymptotic theorems.

The current paper is [ejs_main.pdf](../../../ejs_main.pdf). The three main simulation procedures implement Algorithms 1–3 in its Sections 3–4; experiment settings are in Section 6. The supporting reference-measurement construction is Proposition S5.1. The separately retained two-latitude covariance experiment belongs to Section S8 and is not the POVM used for the paper's Figure 2.

## Exact correspondence checked

| Paper definition or algorithm step | GitHub implementation | What was checked |
|---|---|---|
| Mixed all-observation ridge objective, Section 3.1; Algorithms 1–2 | `mixed.py:62–86` | The ridge Gram matrix starts at `lambda I`; each realized setting contributes its count, and signed outcomes contribute to the right-hand side. Every previous batch enters the fit. A separate expanded individual-copy least-squares solve gives the same raw estimates. |
| Bures safeguard, equation (3.1) | `mixed.py:7–11` | The raw vector is retained only in the open Bloch ball. At or beyond radius one it is reset to zero. |
| Frobenius safeguard, equation (3.2) | `mixed.py:12–15` | Euclidean projection onto radius `sqrt(1-(n+1)^(-1/2))`, with the actual accumulated copy count. |
| Mixed Householder completion, equation (3.4) | `mixed.py:18–32` | The exact `e3`-based formula, the `u=e3` branch, and the zero-estimate reference triple `(e3,e1,e2)`. This is a real Bloch-axis construction, not a claimed 2-by-2 qubit gate. |
| Bures/Frobenius allocations and the complete joint observation law | `mixed.py:33–40,74–83` | Bures probabilities are `(1,1,1)/3`; Frobenius probabilities are `(s,1,1)/(2+s)`. Six complete setting/sign masses are `pi[k]*(1+y*v[k]^T*theta0)/2`. The axes and probabilities remain fixed throughout each predetermined batch. |
| Pure reference bases, Example 4.1 and Proposition S5.1 | `pure.py:9–33` | Coordinate bases and every real/imaginary two-level basis; `B=D^2-D+1`; the prescribed fixed reflection using coordinates `1,...,D`; complete branch/basis/readout labels. At `D=4` there are 104 labelled effects and the denominator floor is exactly `1/6240`. |
| Phase pairing, equation (4.3) | `pure.py:27–33`; `estimators.py:39–44` | `V=diag(i,1,...,1)`, effects `F/2` and `V*FV/2`, including both branch and basis probabilities. A separate physical branch → selected PVM → readout calculation agrees for all 104 labels. |
| Phase-adjusted Householder alignment, equation (4.6) | `estimators.py:28–36`; `pure.py:145–147` | The displayed complex formula, including the zero-first-coordinate phase branch; `U*U=I` and `Ue0=h`. Effective measured effects are `UE_zU*`, corresponding to applying `U*` before the fixed reference measurement. |
| Complete pure Born sampling | `pure.py:148–152` | Counts are newly drawn from the complete aligned POVM's Born probabilities. Tiny negative floating-point residues are clipped and masses normalized only to stabilize floating-point sampling; no fitted denominator floor replaces this observation law. |
| Pure preliminary ridge objective, equation (4.5) | `pure.py:130–158`; `estimators.py:130–156` | The complete categorical objective includes every possible label on every observed copy. A batch adds `m F^T F`; its Gram matrix is not incorrectly weighted by counts of the realized label. The right-hand side uses observed counts. No positivity, trace, or rank constraint is secretly imposed before the rank-one projection. |
| Pure projection, initialization, tie and phase conventions | `estimators.py:171–188`; `pure.py:136,158` | Initial `h=e0`; largest **algebraic** eigenvalue; fixed exact-computed-eigenvalue tie rule and phase rule. A negative eigenvalue with larger absolute magnitude is not selected. |
| All-record fitted tangent objective, equation (4.8) | `pure.py:55–74`; `estimators.py:72–116` | Fitted probabilities and the tangent space are evaluated at the same final all-record preliminary estimate. Every acquired batch enters the residual and curvature. The floor is one quarter of the minimum fixed-reference probability. Clipped denominators are not renormalized. The Frobenius penalty is `eta I` in a Frobenius-orthonormal real tangent basis. |
| Normalization retraction, equation (4.9) | `pure.py:71–74`; `estimators.py:107–112` | Exactly normalize `h+Delta h`; no hidden iterative likelihood optimizer, oracle correction, or true-state tangent space is used for estimation. |
| Algorithm 3 design versus reported estimate | `pure.py:145–176` | Only the preliminary estimate selects the next alignment. The correction is computed at reporting endpoints and is not substituted for the next batch's design estimate. Preliminary and corrected losses use identical acquired records. |
| Predetermined main batches and completed-batch reporting, Section 6 | `schedules.py:5–54`; `simulation.py:77–84` | The full schedule is constructed before observations: initial/minimum 16, growth `ceil(N/50)`, final clipping only. Nearest completed endpoints are selected, with earlier-endpoint ties. Reports do not introduce extra measurement updates. The full paper setting has 202 batches and 16,384 acquired copies. |
| Actual physical losses, equation (2.7) and Section 6 | `mixed.py:53–59`; `pure.py:77–86` | Squared Frobenius loss and squared Bures distance, rather than local quadratic approximations. Mixed losses were separately checked through 2-by-2 density matrices and matrix-square-root Bures evaluation. Pure losses were checked from fidelity. |
| Conditional information diagnostics, equation (6.1) | `mixed.py:43–45,80–98`; `pure.py:43–47,156–187` | Truth is used to evaluate information diagnostics, not to select or fit measurements. Accumulated information uses the actual batch alignments and their copy counts. The current criterion uses the next batch's alignment. |
| Monte Carlo RNG allocation and aggregation | `simulation.py:54–61,85–96,101–164`; `design.py:24–78` | Every role-1 replicate is used; seeds separate experiment/role/replicate. Role 0 is explicitly a different diagnostic history. Pure information criteria are inverted per record before averaging, as specified in Figure 2; all main means and unbiased Monte Carlo standard errors were recomputed from fresh raw arrays. |
| Plotting and benchmark lines | `plotting.py:11–56,64–179` | Main data curves are raw saved means and their Monte Carlo errors. The dotted Gill–Massar curves are separately labelled analytic benchmarks. No smoothing, sorting by outcome, monotonicity forcing, benchmark substitution for the estimates, or selection of favorable replicate streams was found. |

### Why batch multinomials implement the stated experiment

Within a batch the design is fixed. Each fresh copy has the same complete setting–outcome probabilities conditional on the preceding batches. The multinomial call therefore samples the exact joint count distribution of those copies. Counts preserve every sufficient sum used by the displayed ridge and tangent objectives. Compression discards within-batch order, which these updates do not use; it does not insert extra independent observations for repeated labels or omit the initial copies.

### Truth-access check

The simulation naturally supplies the true state to the observation generator and to loss/information evaluation. That does not make the estimator an oracle. Source-level dataflow inspection found no path from truth into the fitted design except through simulated observations. An additional fixed-record test replaced the random sampler by the same predetermined count tape under two different truths. Both mixed rules returned identical design estimates, axes and probabilities; the pure procedure returned identical preliminary and corrected projectors. The resulting probabilities and evaluated losses can differ, as they should.

## New independent execution on 20 October

Evidence: `INDEPENDENT_ALGORITHM_AUDIT.json`, `INDEPENDENT_SOURCE_BASELINE.json` and `independent_checks.py` in this directory. The JSON receipt records the final published checking script's exact hash and the checks that actually ran. Fresh raw arrays and figures are retained in `independent_small_run/` and `independent_small_run_figures/`.

- **Dense mixed replay:** both rules, four batches and 128 copies per rule. The exact probabilities supplied to the RNG were checked against a separate forward reconstruction of the paper's rule. All-copy augmented least squares recovered every raw/safeguarded estimate. Physical losses were independently reconstructed with density matrices.
- **Dense pure replay:** `D=4`, four batches and 128 copies. A separate full categorical, individual-copy design matrix and augmented least-squares solver recovered the preliminary estimate. A separate Gram–Schmidt tangent frame and dense weighted least-squares objective recovered the corrected projector and losses. This checks the optimized count implementation against a different numerical formulation.
- **Adversarial and metamorphic checks:** dimensions `2,3,4,7`; 16 Householder vectors including poles and zero first coordinate; full reference rank/normalization and exact floors; active fitted-probability clipping; largest-algebraic-eigenvalue and exact-tie branches; equality after tripling both record counts and ridge coefficients; equivariance of the preliminary estimate under a random ambient unitary coordinate change.
- **Fresh generation and aggregation:** four independent replicates per study, 256 main copies per replicate, for both mixed rules, the `D=4` pure algorithm, and historical optional covariance settings `D=2,4`. The fresh seed is `202610200713`. This is explicitly a reduced verification configuration, not a replacement for the 10,000-replicate paper experiment.
- **No saved-array shortcut:** `numpy.load` was disabled during the fresh generator call. Generation still completed. Every main replicate was then regenerated from its documented RNG key and matched the saved fresh loss/tangent arrays. All main means/Monte Carlo standard errors and pure design means/errors were recomputed from those arrays. All three figure sets rendered successfully from the fresh output.
- **Preservation:** hashes were checked before and after against 689 protected files: all 633 Lean sources, 10 simulation modules, two configurations, three test modules, 40 paper TeX files and the current main PDF. No protected file changed during this independent audit.

The separate full-size execution report records the execution agent's Oct 20 run and should be cited separately. The small independent run above is evidence of a different seed and checking implementation; it is not silently relabelled as the full paper run.

## Historical evidence and limits

The stored `results/paper/run_receipt.json` retains its **17 October** timestamps. It must not be redated to imply a new run. Its three original result hashes still match `results.json`, `samples.npz` and `apparatus.npz`. Its exact `mixed.py`, `pure.py`, `estimators.py`, `schedules.py` and `optional.py` digests match the current numerical kernels. Some orchestration/version/plotting/configuration files have changed since that receipt: the present default excludes the historical optional comparison and generates the averaged pure design panel jointly with the main run. Thus a claim that every current file equals every historical run hash would be false. The separately preserved update and portability receipts describe those changes; new Oct 20 runs bind their own current source hashes.

The historical optional module uses the direct two-latitude Fisher-symmetric POVM from equation (S8.2), including repeated labels. It is deliberately different from the phase-paired projective construction used by the main Figure 2. The current default `configs/paper.json` does not request that optional experiment. The independent small run exercised it separately and did not relabel it as the main reference apparatus.

This review found no evidence of fabrication or a hidden change to the main algorithms. That is an evidence-bounded conclusion, not a proof of the absence of every possible numerical bug. Finite checks do not establish asymptotic convergence, uniform risk performance, or physical hardware behavior. Archived arrays alone cannot authenticate an earlier execution date, and exact bitwise RNG paths can depend on floating-point/library details. These qualifications are part of the verification scope.

## Re-running the independent checks

With the simulation package's pinned dependencies installed, use a new output directory:

```sh
python -B independent_checks.py \
  --repo /path/to/adaptive-quantum-tomography \
  --output /path/to/new-independent-evidence
```

The script reads the checkout, writes only its caller-selected evidence directory, refuses to reuse an existing fresh-sample directory, and checks that protected numerical/Lean/paper inputs remain unchanged. On a standalone checkout, it binds the available root main PDF; the additional canonical TeX source checks are present only when that local paper source tree is available.
