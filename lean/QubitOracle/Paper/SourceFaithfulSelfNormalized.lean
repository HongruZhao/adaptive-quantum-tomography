import Mathlib

/-!
# Self-normalized vector martingale inequality

This file records a source-faithful interface to Theorem 16 of

Y. Abbasi-Yadkori, D. Pal, and C. Szepesvari, *Regret Bounds for the Adaptive
Control of Linear Quadratic Systems*, COLT/PMLR 19 (2011).

Source: https://proceedings.mlr.press/v19/abbasi-yadkori11a/abbasi-yadkori11a.pdf

The interface exposes the adapted regressors, conditionally sub-Gaussian
martingale differences, self-normalized sum, regularized Gram matrix, and the
single event on which the inequality holds simultaneously for all times.
-/

namespace QubitOracle.Paper.SourceFaithfulSelfNormalized

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

/-- Outer product `x xᵀ`. -/
def vectorOuterProduct {d : ℕ} (x : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => x i * x j

/-- Concrete filtration, adapted vector process, and conditionally
`R`-sub-Gaussian martingale-difference noise from Theorem 16.  Lean index `k`
represents the source's regressor `m_{k}` and noise `eta_{k+1}`. -/
structure SelfNormalizedMartingaleData
    (Ω : Type*) [MeasurableSpace Ω] (d : ℕ) (μ : Measure Ω) (R : ℝ) where
  filtration : Filtration ℕ (inferInstance : MeasurableSpace Ω)
  regressor : ℕ → Ω → (Fin d → ℝ)
  noise : ℕ → Ω → ℝ
  regressorAdapted : Adapted filtration regressor
  noiseAdapted : Adapted filtration noise
  noiseIntegrable : ∀ k, Integrable (noise k) μ
  exponentialIntegrable : ∀ (k : ℕ) (gamma : ℝ),
    Integrable (fun ω => Real.exp (gamma * noise (k + 1) ω)) μ
  martingaleDifference : ∀ k,
    MeasureTheory.condExp (filtration k) μ (noise (k + 1)) =ᵐ[μ] 0
  conditionallySubGaussian : ∀ (k : ℕ) (gamma : ℝ),
    MeasureTheory.condExp (filtration k) μ
      (fun ω => Real.exp (gamma * noise (k + 1) ω)) ≤ᵐ[μ]
        fun _ => Real.exp (gamma ^ 2 * R ^ 2 / 2)

/-- `S_t = sum_{k=1}^t eta_k m_{k-1}`. -/
def selfNormalizedSum
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω} {R : ℝ}
    (data : SelfNormalizedMartingaleData Ω d μ R)
    (t : ℕ) (ω : Ω) : Fin d → ℝ :=
  ∑ k ∈ Finset.range t, data.noise (k + 1) ω • data.regressor k ω

/-- `V_t = sum_{k=1}^t m_{k-1} m_{k-1}ᵀ`. -/
def gramProcess
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω} {R : ℝ}
    (data : SelfNormalizedMartingaleData Ω d μ R)
    (t : ℕ) (ω : Ω) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ k ∈ Finset.range t, vectorOuterProduct (data.regressor k ω)

/-- The regularized Gram matrix `Vbar_t = V + V_t`. -/
def regularizedGram
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω} {R : ℝ}
    (data : SelfNormalizedMartingaleData Ω d μ R)
    (V : Matrix (Fin d) (Fin d) ℝ)
    (t : ℕ) (ω : Ω) : Matrix (Fin d) (Fin d) ℝ :=
  V + gramProcess data t ω

/-- Squared matrix-weighted Euclidean norm `xᵀ A x`. -/
def weightedNormSq {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ i, x i * (Matrix.mulVec A x) i

/-- The determinant confidence radius in Theorem 16. -/
def selfNormalizedRadius
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω} {R : ℝ}
    (data : SelfNormalizedMartingaleData Ω d μ R)
    (V : Matrix (Fin d) (Fin d) ℝ) (delta : ℝ)
    (t : ℕ) (ω : Ω) : ℝ :=
  2 * R ^ 2 * Real.log
    ((Real.sqrt (Matrix.det (regularizedGram data V t ω)) *
        (Real.sqrt (Matrix.det V))⁻¹) / delta)

/-- The event on which the self-normalized inequality holds uniformly for
every `t >= 0`. -/
def selfNormalizedGoodEvent
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω} {R : ℝ}
    (data : SelfNormalizedMartingaleData Ω d μ R)
    (V : Matrix (Fin d) (Fin d) ℝ) (delta : ℝ) : Set Ω :=
  {ω | ∀ t : ℕ,
    weightedNormSq (regularizedGram data V t ω)⁻¹
        (selfNormalizedSum data t ω) ≤
      selfNormalizedRadius data V delta t ω}

/-- **Scientific axiom: Abbasi-Yadkori--Pal--Szepesvari (2011), Theorem 16.**

For a positive-definite deterministic regularizer `V` and `0 < delta < 1`,
the displayed self-normalized inequality holds simultaneously for every time
with probability at least `1 - delta`.
-/
axiom abbasiYadkoriPalSzepesvari2011_theorem16
    {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ] {R : ℝ}
    (data : SelfNormalizedMartingaleData Ω d μ R)
    (V : Matrix (Fin d) (Fin d) ℝ)
    (hV : V.PosDef) (hR : 0 ≤ R)
    (delta : ℝ) (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    ENNReal.ofReal (1 - delta) ≤ μ (selfNormalizedGoodEvent data V delta)

end

end QubitOracle.Paper.SourceFaithfulSelfNormalized
