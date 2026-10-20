# Main results

This guide states the paper's scope and principal conclusions. The [main article](ejs_main.pdf) contains the full assumptions, definitions, and numbering; the [supplement](ejs_supplement.pdf) contains the detailed proofs. [LEAN_FORMALIZATION.md](LEAN_FORMALIZATION.md) identifies formal endpoints and verification limits.

## Experiment and reporting schedule

An unknown density matrix is estimated from independently prepared copies. The measurement on a new copy can depend on previous complete setting–outcome records. The design is therefore predictable from the past, while the next observation remains random. “Conditional Fisher information” means the information of that next single-copy experiment conditional on the observed past; it is not the observed likelihood Hessian.

Two models are studied:

- Interior mixed qubits, with Bloch parameter $\theta_0\in\mathbb R^3$ and $\lVert\theta_0\rVert<1$.
- Pure states in dimension $D\ge2$, represented by rank-one projectors, with real parameter dimension $2d$ and $d=D-1$.

Fix positive finite batch sizes $m_1,m_2,\ldots$ in advance and write $N_j=\sum_{k=1}^j m_k$. All data collected before a batch select its measurement design. Estimation limits are taken along completed batches $n=N_j$. Single-copy updates are included. Data-dependent stopping or batching is not included by this schedule assumption.

## Interior mixed qubits: Theorems 3.1 and 3.2

A safeguarded ridge least-squares estimate fitted to all accumulated observations selects the measurement axes and supplies the reported estimate. The Bures rule uses equal allocation over three orthogonal axes. The Frobenius rule also adapts the radial-versus-transverse allocation. A real Householder construction specifies the Bloch axes; it is not itself a physical two-dimensional qubit gate.

Let $H=H(\theta_0)$ be the symmetric logarithmic derivative quantum Fisher information and let $s_0=\sqrt{1-\lVert\theta_0\rVert^2}$. The limiting classical information targets are

```math
\mathcal I_B^\star=H/3,
\qquad
\mathcal I_F^\star=H^{1/2}/(2+s_0).
```

The procedures are strongly consistent, their conditional information converges to the corresponding target, and their reported estimates are asymptotically normal with covariance $(\mathcal I_L^\star)^{-1}$. The conclusions include the maximally mixed state. These allocations have established precedents; the paper analyzes the specified repeatedly updated ridge procedures rather than claiming invention of their information targets.

## Pure states: Proposition 4.1 and Theorems 4.2 and 4.3

The preliminary matrix ridge fit is projected onto rank-one projectors and chooses the next measurement alignment. A phase-paired reference measurement is Fisher symmetric at its reference state: its classical information there is one half of the quantum Fisher information. The aligned reference family remains informationally complete. The concrete example can be implemented by randomization over fixed projective bases after a data-dependent premeasurement unitary; the theorem permits the broader rank-one reference-POVM class satisfying its conditions.

At a reporting horizon, inverse-probability weighted least squares on the fitted pure-state tangent space gives a correction. A normalization retraction returns the corrected estimate to the pure-state model. The preliminary estimate selects the design; the corrected estimate is the reported estimator.

The preliminary and corrected projectors are strongly consistent, and conditional information converges to $H/2$ in any fixed local coordinates. The corrected estimator has limiting covariance

```math
\Sigma=2H^{-1}=(H/2)^{-1}.
```

In Frobenius-orthonormal tangent coordinates, this covariance is the identity; in the normalized amplitude coordinates used in the paper, it is twice the identity. These statements use different coordinate normalizations of the same limit.

Optimal measurement information alone does not make the unweighted preliminary fit efficient. The paper gives an explicit measurement example with asymptotic variance $4/3$ in each Frobenius-orthonormal tangent direction for a pure qubit, compared with the available inverse-information variance of one. This is an example of inefficiency, not a claim that every unweighted fit is inefficient.

## Adaptive lower bound: Theorem 5.1

For either model, let $W\succeq0$ be the coordinate loss weight and $H\succ0$ the quantum information at the truth. Under the conditional-likelihood assumptions in main Appendix B, any finite-valued coordinate estimator $T_n$ locally unbiased at $\theta_0$ satisfies, for every $n\ge1$,

```math
n\,\mathbb E_{\theta_0}
\left[(T_n-\theta_0)^{\mathsf T}W(T_n-\theta_0)\right]
\ge C_{\mathrm{GM}}(W,H),
```

where

```math
C_{\mathrm{GM}}(W,H)
=\frac{\left[\mathrm{tr}\!\left\{
(H^{-1/2}WH^{-1/2})^{1/2}\right\}\right]^2}{D-1}.
```

The policy may select any finite single-copy POVM as a parameter-independent function of the complete past records. Random setting choice is included by recording the setting and readout together. The bound also permits singular $W$ and does not require inversion of the classical record information.

## Pointwise expected-loss attainment: Corollaries 5.2 and 5.3

For the design matched to each loss, the reported estimators satisfy the following limits along completed batches:

| Model | Expected squared Bures loss, multiplied by $n$ | Expected squared Frobenius loss, multiplied by $n$ |
|---|---|---|
| Interior mixed qubits | $9/4$ | $(2+s_0)^2/2$ |
| Pure states | $d$ | $2d$ |

The mixed-qubit entries use the Bures and Frobenius allocation rules respectively. For pure states the same corrected estimator gives both limits. The paper uses squared fidelity $F$ and squared Bures distance $D_B^2=2(1-\sqrt F)$. Proved fourth-moment bounds justify uniform integrability and convergence of expected losses; asymptotic normality alone would not justify this step.

The physical outputs may be biased. Local unbiasedness defines the finite-sample lower-bound comparison class, not an additional assumption on these physical outputs. Attainment is pointwise at each fixed truth and dimension. The paper makes no uniform local minimax assertion, finite-sample superiority claim, or claim covering all dimensions simultaneously.
