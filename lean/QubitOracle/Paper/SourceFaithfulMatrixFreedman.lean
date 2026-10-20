import Mathlib

/-!
# Tropp's matrix Freedman inequality

This file records a source-faithful interface to Theorem 1.2 of

J. A. Tropp, *Freedman's Inequality for Matrix Martingales*, Electronic
Communications in Probability 16 (2011), 262--270.

Source: https://tropp.caltech.edu/papers/Tro11-Freedmans-Inequality.pdf

The sole scientific axiom below is not an arbitrary proposition oracle.  Its
arguments expose the filtered probability space, the self-adjoint matrix
martingale, its increments, the conditional second moments, the predictable
quadratic variation, and the uniform crossing event appearing in the source.
-/

namespace QubitOracle.Paper.SourceFaithfulMatrixFreedman

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

/-- Algebraically largest eigenvalue of a real self-adjoint `d` by `d`
matrix.  The value outside the nonempty self-adjoint domain is set to zero;
all uses in Tropp's theorem carry the corresponding source hypotheses. -/
def largestEigenvalue {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  if hA : A.IsHermitian then
    if hd : 0 < d then hA.eigenvalues ⟨0, hd⟩ else 0
  else 0

/-- Spectral/operator norm, represented by the largest eigenvalue of
`Aᵀ A`. -/
def matrixOperatorNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  Real.sqrt (largestEigenvalue (A.transpose * A))

/-- The zero-based difference `X_{k+1} = Y_{k+1} - Y_k`. -/
def matrixIncrement {Ω : Type*} {d : ℕ}
    (Y : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ)
    (k : ℕ) (ω : Ω) : Matrix (Fin d) (Fin d) ℝ :=
  Y (k + 1) ω - Y k ω

/-- Concrete filtered self-adjoint matrix martingale data used in Tropp's
Theorem 1.2. -/
structure MatrixMartingaleData
    (Ω : Type*) [MeasurableSpace Ω] (d : ℕ) (μ : Measure Ω) where
  filtration : Filtration ℕ (inferInstance : MeasurableSpace Ω)
  process : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ
  adaptedEntry : ∀ k i j,
    StronglyMeasurable[filtration k] (fun ω => process k ω i j)
  integrableEntry : ∀ k i j, Integrable (fun ω => process k ω i j) μ
  incrementSquareIntegrableEntry : ∀ k i j,
    Integrable (fun ω => ((matrixIncrement process k ω) ^ 2) i j) μ
  initialZero : process 0 =ᵐ[μ] 0
  selfAdjoint : ∀ k, ∀ᵐ ω ∂μ, (process k ω).IsHermitian
  martingaleStepEntry : ∀ k i j,
    MeasureTheory.condExp (filtration k) μ
      (fun ω => process (k + 1) ω i j) =ᵐ[μ]
        fun ω => process k ω i j

/-- Entrywise conditional second-moment matrix
`E_k(X_{k+1}^2)`.  This representation avoids imposing an artificial norm on
the raw matrix type; finite-dimensional matrix conditional expectation is
entrywise in the source as well. -/
def conditionalIncrementSquare
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
    (data : MatrixMartingaleData Ω d μ)
    (k : ℕ) (ω : Ω) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j =>
    MeasureTheory.condExp (data.filtration k) μ
      (fun ω' => ((matrixIncrement data.process k ω') ^ 2) i j) ω

/-- Tropp's predictable quadratic variation
`W_k = sum_{j=1}^k E_{j-1}(X_j^2)`, with zero-based Lean indexing. -/
def predictableQuadraticVariation
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
    (data : MatrixMartingaleData Ω d μ)
    (k : ℕ) (ω : Ω) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ j ∈ Finset.range k, conditionalIncrementSquare data j ω

/-- The uniform-in-time event in Tropp's Theorem 1.2.  The source writes the
variance threshold as `sigma^2`; here `varianceThreshold` denotes that whole
nonnegative real number. -/
def matrixFreedmanCrossingEvent
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
    (data : MatrixMartingaleData Ω d μ)
    (t varianceThreshold : ℝ) : Set Ω :=
  {ω | ∃ k : ℕ,
    t ≤ largestEigenvalue (data.process k ω) ∧
      matrixOperatorNorm (predictableQuadraticVariation data k ω) ≤
        varianceThreshold}

/-- The exact real-valued upper bound in Tropp's Theorem 1.2. -/
def matrixFreedmanBound (d : ℕ) (R t varianceThreshold : ℝ) : ℝ :=
  (d : ℝ) * Real.exp
    (-((t ^ 2 / 2) / (varianceThreshold + R * t / 3)))

/-- **Scientific axiom: Tropp (2011), Theorem 1.2.**

For a `d`-dimensional self-adjoint matrix martingale whose increments obey
`lambda_max(X_k) <= R` almost surely, the probability that some `Y_k` crosses
`t` while the spectral norm of its predictable quadratic variation remains
at most `varianceThreshold` is bounded by

`d * exp (-(t^2/2)/(varianceThreshold + R*t/3))`.
-/
axiom tropp2011_matrixFreedman_theorem1_2
    {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (data : MatrixMartingaleData Ω d μ)
    (R t varianceThreshold : ℝ)
    (hd : 0 < d) (hR : 0 < R) (ht : 0 ≤ t)
    (hvariance : 0 < varianceThreshold)
    (hincrement : ∀ k,
      ∀ᵐ ω ∂μ, largestEigenvalue (matrixIncrement data.process k ω) ≤ R) :
    μ (matrixFreedmanCrossingEvent data t varianceThreshold) ≤
      ENNReal.ofReal (matrixFreedmanBound d R t varianceThreshold)

end

end QubitOracle.Paper.SourceFaithfulMatrixFreedman
