# Main results and their Lean statements

This page reproduces **all five main-paper theorem statements**, together with the two main propositions and two corollaries, from the [current main article](https://github.com/HongruZhao/adaptive-quantum-tomography/blob/main/ejs_main.pdf). Statement wording and every mathematical clause are retained; project-specific TeX macros are expanded and cross-references use the article's printed numbers. Each statement is followed by its actual Lean assumptions, proved conclusions, and dated verification evidence. A fresh source build, declaration audit and selected kernel replay passed on **20 October 2026**; dated simulation execution and an independent algorithm audit are recorded in the final table.

The full statement and type inventories are the [43-group, 211-endpoint correspondence ledger](lean/docs/MAIN_PAPER_CORRESPONDENCE.json), [freshly elaborated Lean types](lean/verification/20261020/ELABORATED_STATEMENTS.json), and [LEAN_FORMALIZATION.md](LEAN_FORMALIZATION.md). Some current paper theorems are clauses of one older combined Lean declaration; the correspondence below identifies that explicitly.

## Notation and algorithm prerequisites

The definitions and algorithms referenced by the statements are in the [main article](https://github.com/HongruZhao/adaptive-quantum-tomography/blob/main/ejs_main.pdf), Sections 2–5 and Appendices A–B.

- States are $`D\times D`$ density matrices. Pure states are rank-one projectors $`P=hh^*`$ with $`\lVert h\rVert=1`$; $`d=D-1`$ and their real dimension is $`2d`$. Their tangent space is $`T_P=\lbrace A=A^*:PA+AP=A\rbrace `$. The coordinate-free SLD quantum Fisher information is $`\mathcal H_P`$; $`H(\theta)`$ is its coordinate matrix. Classical information is $`\mathcal J_{a,P}`$ as a tangent-space form and $`\mathcal I_a(\theta)`$ as a coordinate matrix. A randomized design has information $`\mathcal I_{\xi_t}`$.
- Equation (2.1) fixes **predetermined positive finite integers** $m_j$ and defines $N_0=0$, $N_j=\sum_{k=1}^j m_k$, and $n_-(t)=N_{j-1}$ for $N_{j-1}<t\le N_j$. These are the completed-batch sample sizes and the last update before copy $t$.
- **Algorithms 1–2, mixed qubits:** $\theta_0\in\mathbb R^3$, $\lVert\theta_0\rVert<1$, $s_0=\sqrt{1-\lVert\theta_0\rVert^2}$, and $H_0=H(\theta_0)$. With $G_n=\sum_{t\le n}a_ta_t^{\mathsf T}$ and $B_n=\sum_{t\le n}a_tY_t$, the ridge fit is $\widehat\theta_n=(\lambda I_3+G_n)^{-1}B_n$. Algorithm 1 uses the safeguard $c_n=\widehat\theta_n\mathbf1_{\lbrace \lVert\widehat\theta_n\rVert<1\rbrace }$ in (3.1); Algorithm 2 projects onto the ball of radius $\sqrt{1-(n+1)^{-1/2}}$ in (3.2). Equation (3.4) specifies their common radial/transverse axis construction. Their allocations are $\pi_B=(1/3,1/3,1/3)$ and $\pi_F(c)=(\sqrt{1-\lVert c\rVert^2},1,1)/(2+\sqrt{1-\lVert c\rVert^2})$, and their information targets in (3.5) are $\mathcal I_B^\star=H_0/3$ and $\mathcal I_F^\star=H_0^{1/2}/(2+s_0)$.
- **Proposition 4.1 and Algorithm 3, pure states:** a finite reference POVM $`\mathsf F=\lbrace F_r\rbrace `$ has nonzero rank-one effects, (C1) $`\mathrm{span}_{\mathbb R}\lbrace F_r\rbrace =\mathrm{Herm}(\mathbb C^D)`$, and (C2) $`\mathrm{tr}(P_{\mathrm{ref}}F_r)>0`$ for all $`r`$. Here $`P_{\mathrm{ref}}=e_0e_0^*`$. The paired effects in (4.3) are $`E_{0,r}=F_r/2`$ and $`E_{1,r}=V^*F_rV/2`$, where $`V=I_D+(i-1)P_{\mathrm{ref}}`$. Equation (4.1) is the reference amplitude chart with $`H(0)=I_{2d}`$. Algorithm 3 uses the matrix ridge fit $`\widehat A_n`$ in (4.5), its largest-algebraic-eigenvalue rank-one projection $`\widehat P_n`$, and the fitted-tangent weighted ridge correction (4.8), followed by the normalization (4.9) giving $`\widehat P_n^{\mathrm{eff}}`$. The denominator floor is $`\tau=\frac14\min_z\mathrm{tr}(P_{\mathrm{ref}}E_z)>0`$; $`\lambda,\eta>0`$. The measurement-alignment unitary is fixed by (4.6). All these estimators use the actual recorded adaptive setting–outcome data. The corresponding exact Lean definitions are [Inputs and its estimators](lean/QubitOracle/Paper/MainPaperTheorem42.lean#L23).
- **Theorem 5.1, policies and likelihood:** either the interior Bloch model ($D=2$) or a smooth local pure-state parametrization $\rho(\theta)=\Gamma(\theta)$ is used. A prescribed parameter-independent policy $\zeta_t$ maps the complete outcome history to a finite single-copy POVM. Finite setting randomization is represented by weighting effects and recording both setting and readout. Appendix B assumes finite record-label sets independent of $\theta$ at each fixed horizon and existence at $\theta_0$ of all first partial derivatives of every conditional outcome probability, with effects fixed when the history is fixed; zero probabilities are allowed and their scores are zero. A finite-valued estimator is locally unbiased when $m_n(\theta_0)=\theta_0$ and the Jacobian of $m_n(\theta)=\mathbb E_\theta T_n$ at $\theta_0$ is the identity. Equation (2.9) defines

```math
C_{\mathrm{GM}}(W,H)
=\frac{\left[\mathrm{tr}\left\{(H^{-1/2}WH^{-1/2})^{1/2}\right\}\right]^2}{D-1}.
```

## Proposition 2.1 — Pure-state quantum Fisher information

### Paper statement

Let $P=hh^*$ with $\lVert h\rVert=1$. The pairing $\mathcal{H}_P$ is independent of the chosen directional SLDs. For $A,B\in T_P$ and $v\in\mathbb{C}^D$ with $h^*v=0$, it satisfies **(2.5)**

```math
\mathcal{H}_P[A,B]=2\mathrm{tr}(AB),\qquad \mathcal{H}_P[hv^*+vh^*,hv^*+vh^*]=4\lVert v\rVert^2.
```

In a chart (Definition A.2) with tangent basis $`A_j=\partial_j\Gamma(\theta)`$, $`[H(\theta)]_{jk}=\mathcal{H}_P[A_j,A_k]`$ and $`\mathcal{H}_P[A,B]=u^{\mathsf{T}}H(\theta)w`$ whenever $`A=\sum_{j=1}^p u_jA_j`$ and $`B=\sum_{k=1}^p w_kA_k`$, with $`u,w\in\mathbb{R}^p`$.

### Lean correspondence and verification

**Declaration:** [`QubitOracle.Paper.PureQuantumInformation.proposition_2_1`](lean/QubitOracle/Paper/PureQuantumInformationProposition.lean#L230) is one combined theorem covering all clauses above.

**Assumptions:** `h : PureVector d` supplies a unit vector in dimension `d+1`; tangent arguments are elements of `tangentSpace h`. Directional SLDs are arbitrary Hermitian matrices satisfying `IsDirectionalSLD`. The coordinate clause accepts any finite tangent family and corresponding directional SLDs, so it applies to the basis from a chart. The horizontal-vector clause assumes its complex inner product with `h` is zero.

**Proved conclusions:** equality of every admissible SLD pairing with `quantumInformation`, the intrinsic trace formula, the horizontal-vector squared-norm formula, all coordinate entries and the coordinate contraction. SLD independence follows from equality to the same intrinsic pairing; it is not an assumed information identity.

**Verification:** group **T01**. On **20 October 2026**, the defining module was freshly source-compiled and kernel replayed; the declaration type and transitive axioms were freshly checked. See the [nine-result endpoint receipt](lean/verification/20261020/MAIN_ENDPOINT_CHECKS.json).

## Theorem 3.1 — Strong consistency and Fisher information convergence

### Paper statement

Let $L=B$ denote Algorithm 1 with allocation $\pi_B$, and $L=F$ denote Algorithm 2 with allocation $\pi_F(c_{n_-(t)})$ on copy $t$. Both rules use the adaptive measurement axes $v_{n_-(t),k}$ defined in (3.4), with the design estimate $c_{n_-(t)}$ from the corresponding algorithm. Here $n_-(t)=N_{j-1}$ for $N_{j-1}<t\le N_j$, as defined in (2.1). For either rule $L\in\lbrace B,F\rbrace $, every fixed interior truth, every $\lambda>0$, and every batch sequence (2.1), the implemented estimator satisfies almost surely **(3.6)**

```math
\begin{gathered}
 \widehat\theta_n\to\theta_0,\qquad c_n\to\theta_0,\qquad
 \mathcal{I}_{\xi_t}(\theta_0)\to\mathcal{I}_L^\star,\\
 \frac1n\sum_{t\le n}\mathcal{I}_{\xi_t}(\theta_0)\to\mathcal{I}_L^\star,
 \qquad \frac1n\sum_{t\le n}\mathcal{I}_{a_t}(\theta_0)\to\mathcal{I}_L^\star.
 \end{gathered}
```

Both safeguards, (3.1) and (3.2), are eventually inactive almost surely.

### Lean correspondence and verification

**Declaration:** [`QubitOracle.Paper.MainPaperTheorem31.theorem_3_1`](lean/MainPaperTheorem31.lean#L112). This is a **combined endpoint for current Theorems 3.1 and 3.2**, not merely the current Theorem 3.1.

**Assumptions:** explicit arguments `loss : Loss`, `ridge : ℝ` with `0 < ridge`, `m : ℕ → ℕ` with `∀ j, 0 < m j`, and `θ : OneQubitPhysicalParameter` with `blochNormSq θ.1 < 1`. The concrete policy, estimator, safeguard and refresh schedule are definitions, not extra convergence hypotheses.

**Proved conclusions used here:** the endpoint's first almost-sure conjunction gives raw and physical-output consistency, current conditional information convergence, average conditional information convergence, and average realized-axis information convergence. Its final almost-sure clause proves eventual equality of the safeguard and raw estimator. [`action_in_batch`](lean/MainPaperTheorem31.lean#L72) and [`label_order`](lean/MainPaperTheorem31.lean#L102) identify the actual batch-held action and Lean's transverse/transverse/radial label order with the paper's radial-first order. Lean copy indices start at zero.

**Verification:** group **T02**. On **20 October 2026**, the combined theorem, covariance identity and batch/label bridges were freshly compiled and their types and axioms checked; `MainPaperTheorem31` was kernel replayed. The two current paper theorems remain clauses of that one checked conjunction. See the [endpoint receipt](lean/verification/20261020/MAIN_ENDPOINT_CHECKS.json).

## Theorem 3.2 — Asymptotic normality with inverse-information covariance

### Paper statement

Under the hypotheses of Theorem 3.1, the ridge estimator and the physical output are asymptotically normal: **(3.7)**

```math
n^{1/2}(\widehat\theta_n-\theta_0)\Longrightarrow
 \mathcal{N}_3(0,\Sigma_L),\qquad \Sigma_L=(\mathcal{I}_L^\star)^{-1},
```

and the asymptotic normality in (3.7) also holds with $c_n$ in place of $\widehat\theta_n$. Explicitly, **(3.8)**

```math
\begin{aligned}
 \Sigma_B&=3(I_3-\theta_0\theta_0^{\mathsf{T}}),\\
 \Sigma_F&=(2+s_0)\left(I_3-
              \frac{\theta_0\theta_0^{\mathsf{T}}}{1+s_0}\right).
 \end{aligned}
```

The assertions cover the maximally mixed state, single-shot updates, and all completed-batch subsequences.

### Lean correspondence and verification

**Declaration:** the **same** [`QubitOracle.Paper.MainPaperTheorem31.theorem_3_1`](lean/MainPaperTheorem31.lean#L112), using its two `TendstoInDistribution` clauses. There is no separately claimed `theorem_3_2` endpoint.

**Assumptions:** exactly the mixed-model arguments listed under Theorem 3.1; the Gaussian limits are conclusions, not inputs. The covariance identity is [`QubitOracle.AdaptiveDesign.P1Weighted.covariance_eq_information_inv`](lean/QubitOracle/AdaptiveDesign/P1WeightedCovariance.lean#L119), also mapped in group T02. The endpoint uses the concrete normalized raw error and controller/physical-output error. The permitted interior truth includes zero, and the positive-batch schedule includes single-copy batches.

**Proved conclusions used here:** inverse-information Gaussian limits for both errors and the loss-specific covariance identity. The full-sample limits imply the stated completed-batch subsequences.

**Verification:** group **T02**, using the same **20 October 2026** combined declaration and selected-module replay as Theorem 3.1. This is a clause-level split of one freshly checked statement, not a separately named `theorem_3_2`. See the [endpoint receipt](lean/verification/20261020/MAIN_ENDPOINT_CHECKS.json).

## Proposition 4.1 — Phase pairing

### Paper statement

The effects (4.3) form an informationally complete measurement on the full state space and have positive reference probabilities. In the reference coordinates (4.1), centered at $P_{\mathrm{ref}}$, **(4.4)**

```math
\mathcal{I}_{\mathsf{E}}(0)=H(0)/2=I_{2d}/2
```

Equivalently, $`\mathcal{J}_{\mathsf{E},P_{\mathrm{ref}}}=\tfrac12\mathcal{H}_{P_{\mathrm{ref}}}`$ as bilinear forms on $`T_{P_{\mathrm{ref}}}`$; this is Fisher symmetry at $`P_{\mathrm{ref}}`$.

### Lean correspondence and verification

**Declarations:** [`QubitOracle.AdaptiveDesign.PhasePair.paired_conditions`](lean/QubitOracle/AdaptiveDesign/PhasePairPOVM.lean#L211) and [`QubitOracle.AdaptiveDesign.PhasePair.paired_fisher_of_rankOne`](lean/QubitOracle/AdaptiveDesign/PhasePairPOVM.lean#L205).

**Assumptions:** a finite POVM `P`, `Identifying P` for (C1), `Regular P` for (C2), and `RankOne P`. Positive reference probabilities exclude zero effects. The `paired` definition records the fair branch and reference outcome, with weights included in the effects.

**Proved conclusions:** `paired_conditions` gives `Identifying (paired P) ∧ Regular (paired P) ∧ FisherSymmetric (paired P)`; the Fisher assertion is proved by `paired_fisher_of_rankOne`, rather than being an assumption. The coordinate-free reading uses Proposition 2.1's metric normalization and the information-coordinate bridges in the ledger. This is one conjunction plus its Fisher component, not a claim of two distinct versions of Proposition 4.1.

**Verification:** group **T03**. On **20 October 2026**, both declarations were freshly compiled and their elaborated types and standard-only transitive axiom sets checked; `PhasePairPOVM` was kernel replayed. See the [endpoint receipt](lean/verification/20261020/MAIN_ENDPOINT_CHECKS.json).

## Theorem 4.2 — Strong consistency and Fisher information convergence

### Paper statement

Fix $D\ge2$, a reference POVM satisfying (C1)–(C2) with rank-one effects, $\lambda,\eta>0$, a pure truth $P_0$, and batches (2.1). The paired adaptive experiment and estimators in Algorithm 3, defined by (4.5) and (4.8), satisfy, almost surely, **(4.10)**

```math
\begin{aligned}
 \widehat A_n&\to P_0,\quad\widehat P_n\to P_0,
       \quad\widehat P_n^{\mathrm{eff}}\to P_0,
       &&(n=N_j,\ j\to\infty),\\
 U_tP_{\mathrm{ref}}U_t^*&\to P_0,\qquad \mathcal{J}_{a_t,P_0}\to \mathcal{H}_{P_0}/2,
       &&(t\to\infty),\\
 \frac1n\sum_{t\le n}\mathcal{J}_{a_t,P_0}&\to \mathcal{H}_{P_0}/2,
       &&(n=N_j,\ j\to\infty).
 \end{aligned}
```

Here $t\to\infty$ runs through all measured copies. The limits indexed by $n$ hold along the completed-batch sample sizes $n=N_j$, $j\to\infty$, where $N_j$ is the cumulative number of copies after batch $j$ defined in (2.1).

### Lean correspondence and verification

**Declaration:** [`QubitOracle.Paper.MainPaperTheorem42.theorem_4_2`](lean/QubitOracle/Paper/MainPaperTheorem42.lean#L127), with type `theorem_4_2 (A : Inputs d O) (truth : PureVector d) : Conclusions A truth`. This is a **combined endpoint for current Theorems 4.2 and 4.3**.

**Assumptions:** [`Inputs`](lean/QubitOracle/Paper/MainPaperTheorem42.lean#L23) has `dimension_positive : 0 < d`, a finite reference POVM, `identifying`, `regular`, `rankOne`, positive `lambda` and `eta`, and positive predetermined integer `batches`; the truth is a unit `PureVector d`. The finite outcome type carries the measurable instances needed for the path law. The paired apparatus, raw fit, preliminary projection, corrected estimate, alignment and reporting horizon are constructed definitions in `Inputs`.

**Proved conclusions used here:** [`Conclusions`](lean/QubitOracle/Paper/MainPaperTheorem42.lean#L79) fields `raw_consistent`, `preliminary_consistent`, `corrected_consistent`, `alignment_consistent`, `conditional_information`, and `average_information`. These fields are outputs of the theorem, not assumptions in `Inputs`. Normalized amplitude coordinates have SLD matrix `I`; the information limit is `I/2`, representing the displayed intrinsic form.

**Verification:** group **T04**. On **20 October 2026**, `Inputs`, `Conclusions` and the combined theorem were freshly compiled and their types and axioms checked. `MainPaperTheorem42` and its selected chart/limit modules were kernel replayed. See the [endpoint receipt](lean/verification/20261020/MAIN_ENDPOINT_CHECKS.json).

## Theorem 4.3 — Estimation rates and asymptotic normality

### Paper statement

Under the hypotheses of Theorem 4.2, the estimators in Algorithm 3 satisfy the following conclusions along $n=N_j$, $j\to\infty$. **(i) Estimation rates.** The matrix least-squares estimator and its rank-one projection satisfy $\lVert \widehat A_n-P_0\rVert_F=O_p(n^{-1/2})$ and $\lVert \widehat P_n-P_0\rVert_F=O_p(n^{-1/2})$. **(ii) Asymptotic normality.** In any fixed smooth pure-state chart $(\mathcal{U},\varphi)$ as in Definition A.2, with $P_0\in\mathcal{U}$, let $\theta_0=\varphi(P_0)$ and let $H(\theta_0)$ be the matrix in the parametrization $\Gamma(\theta)=\varphi^{-1}(\theta)$. Then **(4.11)**

```math
n^{1/2}\{\varphi(\widehat P_n^{\mathrm{eff}})-\varphi(P_0)\}
 \Longrightarrow\mathcal{N}_{2d}(0,2H(\theta_0)^{-1}).
```

Equivalently, $n^{1/2}(\widehat P_n^{\mathrm{eff}}-P_0)$ converges in distribution to a centered Gaussian supported on the true tangent space, with identity covariance in Frobenius-orthonormal tangent coordinates.

### Lean correspondence and verification

**Declaration:** the **same** [`QubitOracle.Paper.MainPaperTheorem42.theorem_4_2`](lean/QubitOracle/Paper/MainPaperTheorem42.lean#L127), through its [`Conclusions`](lean/QubitOracle/Paper/MainPaperTheorem42.lean#L79) fields. There is no separately claimed `theorem_4_3` endpoint.

**Assumptions:** the same `Inputs` and pure truth as Theorem 4.2. The arbitrary-chart clause quantifies over [`MainPaperPureCharts.SmoothCoordinates`](lean/QubitOracle/Paper/MainPaperPureCharts.lean#L20): a local homeomorphism containing zero with smooth map and inverse. Its invertible derivative is derived from those inverse maps; covariance and statistical limits are not chart assumptions.

**Proved conclusions used here:** `raw_root_rate`, `preliminary_root_rate`, `chart_normality`, `chart_covariance`, and `chart_sld_information`; and `ambient_normality`, `ambient_gaussian`, `ambient_centered`, `ambient_tangent_support`, and `ambient_covariance`. The chart covariance is twice inverse SLD information. The ambient covariance is the Frobenius inner product on tangent vectors, giving identity in an orthonormal tangent basis. The raw-rate fields use `TightNorm` for the root-sample-size scaled errors; the Gaussian limits explicitly use completed-batch horizons.

**Verification:** group **T04**, using the same **20 October 2026** combined declaration and selected-module replay as Theorem 4.2. The complete checked `Conclusions` structure supplies both current printed theorem statements. See the [endpoint receipt](lean/verification/20261020/MAIN_ENDPOINT_CHECKS.json).

## Theorem 5.1 — Adaptive Gill–Massar bound

### Paper statement

For either model above, let $H=H(\theta_0)\succ0$ be the SLD quantum Fisher information matrix and $W\succeq0$ a weight in the same coordinates. For any sequence of policies $(\zeta_t)_{t\ge1}$ as above, under the conditional-likelihood assumptions in Appendix B, every finite-valued coordinate estimator $T_n$ locally unbiased at $\theta_0$ and every $n\ge1$ satisfy **(5.1)**

```math
n\,\mathbb{E}_{\theta_0}\!\left[
 (T_n-\theta_0)^{\mathsf{T}}W(T_n-\theta_0)\right]
 \ge C_{\mathrm{GM}}(W,H),
```

where $C_{\mathrm{GM}}$ is defined in (2.9).

### Lean correspondence and verification

**Declaration:** [`QubitOracle.AdaptiveDesign.AdaptiveSingleCopyOracle.theorem_5_1`](lean/QubitOracle/AdaptiveDesign/AdaptiveSingleCopyOracleCharts.lean#L251) is one combined theorem with mixed and pure alternatives. Its model-specific endpoints are [`theorem_5_1_mixed`](lean/QubitOracle/AdaptiveDesign/AdaptiveSingleCopyOracle.lean#L84) and [`theorem_5_1_pure`](lean/QubitOracle/AdaptiveDesign/AdaptiveSingleCopyOracleCharts.lean#L198).

**Assumptions:** `M : QuantumModel` is an interior mixed qubit or `d > 0` with [`PureChartData`](lean/QubitOracle/AdaptiveDesign/AdaptiveSingleCopyOracleCharts.lean#L30). Pure chart data give a locally physical state map at the truth and its invertible tangent derivative; they do not supply an information bound. The other arguments are a policy `List Y → FinitePOVM (Fin M.systemDimension) Y` with finite `Y`, a real symmetric positive-semidefinite weight (`W.PosSemidef`), `n ≥ 1`, an estimator on `Record Y n`, and its actual finite-model `LocallyUnbiased` property. The policy is fixed as the parameter varies. Its history-list length represents time; finite setting randomness is incorporated in the complete outcome labels. No rank-one measurement or positive-outcome-probability assumption is imposed.

**Proved conclusion:** `oracleConstant W M.quantumInformation (M.systemDimension-1) ≤ n * quadraticRisk W T`, with quantum information derived from the actual model. The Born regularity, score identities and Gill–Massar information inequality are proved internally. The finite decision-tree/finite-sum proof establishes the scalar whitened-information consequence needed for the risk bound; the paper's sigma-field notation is not a separate Lean object. The theorem permits singular positive-semidefinite weights and does not invert classical record information.

**Verification:** group **T05**. On **20 October 2026**, the combined theorem and both model-specific alternatives were freshly source-compiled, their exact types and transitive axioms checked, and both defining endpoint modules kernel replayed. See the [endpoint receipt](lean/verification/20261020/MAIN_ENDPOINT_CHECKS.json).

## Corollary 5.2 — Mixed-qubit expected-loss attainment

### Paper statement

Under the hypotheses of Theorem 3.2, let $c_n$ be the safeguarded output (3.1) for Algorithm 1 or the projected output (3.2) for Algorithm 2. Along $n=N_j$, $j\to\infty$, **(5.2)**

```math
\begin{aligned}
 n\,\mathbb{E}_{\theta_0}D_B^2\{\rho(c_n),\rho(\theta_0)\}
   &\longrightarrow 9/4 &&\text{(Algorithm 1)},\\
 n\,\mathbb{E}_{\theta_0}\lVert \rho(c_n)-\rho(\theta_0)\rVert_F^2
   &\longrightarrow (2+s_0)^2/2 &&\text{(Algorithm 2)}.
 \end{aligned}
```

### Lean correspondence and verification

**Declaration:** [`QubitOracle.Paper.MainPaperMeanLosses.corollary_5_2`](lean/QubitOracle/Paper/MainPaperMeanLosses.lean#L51) combines the two expected-loss limits.

**Assumptions:** positive ridge, predetermined positive integer batches, and an interior mixed truth. `mixedOutput` constructs the physical state from the actual safeguard/projection. The first conjunction uses the Bures policy and the second the Frobenius policy. There is no additional local-unbiasedness, moment-bound or assumed expected-loss-limit hypothesis.

**Proved conclusions:** the scaled integrals of actual physical squared Bures and Frobenius losses tend to `9/4` and `(2+mixedRadialGap truth.val)^2/2` along `batchEndpoint m j`. The companion [`qubit_bures_comm`](lean/QubitOracle/Paper/MainPaperMeanLosses.lean#L24) justifies the paper's estimate-first Bures argument order. The matrix-square-root Bures loss and physical outputs are used, rather than only the quadratic Taylor approximation.

**Verification:** group **T06**. On **20 October 2026**, the combined expected-loss endpoint and Bures-order bridge were freshly compiled, their types and standard-only axiom sets checked, and `MainPaperMeanLosses` kernel replayed. The expectation limits use proved moment estimates, not the simulation. See the [endpoint receipt](lean/verification/20261020/MAIN_ENDPOINT_CHECKS.json).

## Corollary 5.3 — Pure-state expected-loss attainment

### Paper statement

Under the hypotheses of Theorem 4.3, the reported tangent-corrected projector of Algorithm 3 satisfies, along $n=N_j$, $j\to\infty$, **(5.3)**

```math
\begin{aligned}
 n\,\mathbb{E}_{P_0}D_B(\widehat P_n^{\mathrm{eff}},P_0)^2&\longrightarrow d,\\
 n\,\mathbb{E}_{P_0}\lVert \widehat P_n^{\mathrm{eff}}-P_0\rVert_F^2&\longrightarrow2d.
 \end{aligned}
```

### Lean correspondence and verification

**Declaration:** [`QubitOracle.Paper.MainPaperMeanLosses.corollary_5_3`](lean/QubitOracle/Paper/MainPaperMeanLosses.lean#L92) combines the two pure-state expected-loss limits.

**Assumptions:** exactly `A : MainPaperTheorem42.Inputs d O` and `truth : PureVector d`, as under Theorems 4.2–4.3. `pureOutput` is the actual reported phase-paired corrected projector. No local-unbiasedness or extra moment hypothesis is added.

**Proved conclusions:** scaled actual physical Bures and squared Frobenius loss integrals tend to `d` and `2*d` along `A.horizon j`. [`pure_bures_comm`](lean/QubitOracle/Paper/MainPaperMeanLosses.lean#L31) supplies the estimate-first Bures argument order. Both limits are proved for the same corrected procedure.

**Verification:** group **T07**. On **20 October 2026**, the combined declaration and Bures bridge were freshly compiled, their types and standard-only axiom sets checked, and their defining module kernel replayed. This verifies the formal expected-loss conclusion, rather than inferring it from a central limit theorem. See the [endpoint receipt](lean/verification/20261020/MAIN_ENDPOINT_CHECKS.json).

## What was actually verified

**Official verification record: 20 October 2026.**

The statements above are tied to the documented source-level semantic correspondence, not just similarly named identifiers. The [ledger](lean/docs/MAIN_PAPER_CORRESPONDENCE.json) has **43 claim groups and 211 selected endpoints**; all 211 occur in the freshly checked 498-declaration inventory. The current nine displayed main results use groups T01–T07: two groups each bundle a pair of current theorem numbers.

| Dated evidence | Established scope | Boundary |
|---|---|---|
| [20 October 2026: fresh Lean build](lean/verification/20261020/README.md) | **508 project modules** compiled from source; explicit `MainPaper` and `MainPaperAudit` roots passed; **498 declaration types and transitive axiom sets** checked; all **nine main results**, seven principal groups and **17 mapped declarations** covered | Pinned upstream libraries were reused; no claim to rebuild all 633 historical sources or upstream Mathlib |
| [20 October 2026: kernel replay](lean/verification/20261020/SUMMARY.json) | **17 selected modules** freshly replayed with `leanchecker`, including the main combined endpoint modules | Selected-module replay, not replay of the whole dependency closure |
| [20 October 2026: Python tests and full simulation](simulation/verification/20261020/FRESH_SIMULATION.md) | **37 tests passed**; exact paper configuration freshly ran **10,000 replicates for each of three studies**, **16,384 copies and 202 batches** per replicate; all means, Monte Carlo errors, physical ranges and both fresh figures checked | Python 3.9.6 / NumPy 1.26.4 / Matplotlib 3.9.4; historical optional covariance studies were not fully rerun |
| [20 October 2026: numerical reproduction](simulation/verification/20261020/EXECUTION_CHECKS.json) | All saved principal arrays compared only after fresh generation: mixed arrays bitwise identical; maximum pure scaled-loss difference **6.79 × 10⁻¹¹**, within recorded tolerance; separate observation instrumentation checked **1,818 new multinomial draws** | Pure arrays are not claimed bitwise identical; a simulation is not a proof of the asymptotic theorems |
| [20 October 2026: independent simulation audit](simulation/verification/20261020/INDEPENDENT_ALGORITHM_AUDIT.md) | Separate source-to-paper review and **five independent check groups** passed: dense objective reconstruction, physical Born probabilities, truth-blind estimation, edge cases, and fresh altered-seed generation with saved-array loading disabled; no main-algorithm mismatch or manufactured-result path found | Independent finite checks and code review, not mechanical verification of Python or proof that every possible bug is absent |
| [20 October 2026: statement and source preservation](lean/verification/20261020/ENDPOINT_INDEPENDENT_REVIEW.md) and [final hash guard](lean/verification/20261020/FINAL_PRESERVATION.json) | All nine printed statements and explicit Lean hypotheses independently reviewed; paper, all 633 Lean sources and numerical implementation preserved | Semantic correspondence is independently reviewed; it is not a mechanized LaTeX-to-Lean translation |

For the selected audited endpoint dependencies, the only axioms are `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or scientific input axiom occurs in those selected sets. The [full retained tree](lean/) has 633 canonical source files and also contains historical material: [twelve legacy scientific axiom leaves](lean/verification/LEGACY_AXIOM_INVENTORY.json) are documented outside the selected endpoint dependencies. Source presence does not establish a statement match or a fresh verification of every declaration.

[LEAN_FORMALIZATION.md](LEAN_FORMALIZATION.md) gives the toolchain pins, full evidence boundaries, and commands for producing a new selected source build and replay. The Lean proofs do not mechanically verify the Python code, Monte Carlo values, physical measurement hardware, bibliography or novelty claims.
