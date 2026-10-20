import QubitOracle.Paper.CramerWold
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
namespace QubitOracle.Paper

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

noncomputable section

abbrev MartingaleScoreSpace (D : Type*) [Fintype D] := EuclideanSpace ℝ D

def martingaleArrayPartialSum
    {Omega : Type*} (increment : ℕ → ℕ → Omega → ℝ) (row : ℕ) : ℕ → Omega → ℝ :=
  fun k omega => ∑ j ∈ Finset.range k, increment row j omega

def martingaleArrayTerminalSum
    {Omega : Type*} (increment : ℕ → ℕ → Omega → ℝ) : ℕ → Omega → ℝ :=
  fun n omega => martingaleArrayPartialSum increment n n omega

def hallHeydeArrayConditionalVariance
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (filtration : ℕ → Filtration ℕ (inferInstance : MeasurableSpace Omega))
    (increment : ℕ → ℕ → Omega → ℝ) (n : ℕ) : Omega → ℝ :=
  fun omega => ∑ k ∈ Finset.range n,
    mu[(fun omega => increment n k omega ^ 2) | filtration n k] omega

def hallHeydeArrayConditionalLindeberg
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (filtration : ℕ → Filtration ℕ (inferInstance : MeasurableSpace Omega))
    (increment : ℕ → ℕ → Omega → ℝ) (epsilon : ℝ) (n : ℕ) : Omega → ℝ :=
  fun omega => ∑ k ∈ Finset.range n,
    mu[(fun omega => if epsilon < |increment n k omega| then increment n k omega ^ 2 else 0) |
      filtration n k] omega


structure MartingaleCLTProblem (D : Type*) [Fintype D] where
  Omega : Type
  measurableSpace : MeasurableSpace Omega
  mu : @Measure Omega measurableSpace
  probabilityMeasure : @IsProbabilityMeasure Omega measurableSpace mu
  filtration : ℕ → Filtration ℕ measurableSpace
  increment : ℕ → ℕ → Omega → MartingaleScoreSpace D

def MartingaleCLTProblem.projectedIncrement
    {D : Type*} [Fintype D] (problem : MartingaleCLTProblem D)
    (u : MartingaleScoreSpace D) : ℕ → ℕ → problem.Omega → ℝ :=
  fun n k omega => ⟪u, problem.increment n k omega⟫

/-- Vector-valued terminal score in row `n`. -/
def MartingaleCLTProblem.terminalSum
    {D : Type*} [Fintype D] (problem : MartingaleCLTProblem D) :
    ℕ → problem.Omega → MartingaleScoreSpace D :=
  fun n omega => ∑ k ∈ Finset.range n, problem.increment n k omega

def MartingaleCLTProblem.IsSquareIntegrableMartingaleDifferenceArray
    {D : Type*} [Fintype D] (problem : MartingaleCLTProblem D) : Prop :=
  letI : MeasurableSpace problem.Omega := problem.measurableSpace
  letI : IsProbabilityMeasure problem.mu := problem.probabilityMeasure
  (∀ u n, Martingale
      (martingaleArrayPartialSum (problem.projectedIncrement u) n)
      (problem.filtration n) problem.mu) ∧
    (∀ u n k, MemLp (problem.projectedIncrement u n k) 2 problem.mu) ∧
    (∀ n k, problem.filtration n k ≤ problem.filtration (n + 1) k)

def MartingaleCLTProblem.HasConditionalLindeberg
    {D : Type*} [Fintype D] (problem : MartingaleCLTProblem D) : Prop :=
  letI : MeasurableSpace problem.Omega := problem.measurableSpace
  letI : IsProbabilityMeasure problem.mu := problem.probabilityMeasure
  ∀ u epsilon, 0 < epsilon →
    TendstoInMeasure problem.mu
      (hallHeydeArrayConditionalLindeberg problem.mu problem.filtration
        (problem.projectedIncrement u) epsilon)
      atTop (fun _ => 0)

def martingaleScoreQuadraticForm
    {D : Type*} [Fintype D] (M : Matrix D D ℝ)
    (u : MartingaleScoreSpace D) : ℝ :=
  dotProduct (fun i => u i) (M.mulVec (fun i => u i))

def MartingaleCLTProblem.ConditionalCovarianceConverges
    {D : Type*} [Fintype D] (problem : MartingaleCLTProblem D)
    (M : Matrix D D ℝ) : Prop :=
  letI : MeasurableSpace problem.Omega := problem.measurableSpace
  letI : IsProbabilityMeasure problem.mu := problem.probabilityMeasure
  ∀ u, TendstoInMeasure problem.mu
    (hallHeydeArrayConditionalVariance problem.mu problem.filtration
      (problem.projectedIncrement u))
    atTop (fun _ => martingaleScoreQuadraticForm M u)

def MartingaleCLTProblem.SumConvergesToGaussian
    {D : Type*} [Fintype D] (problem : MartingaleCLTProblem D)
    (M : Matrix D D ℝ) : Prop :=
  letI : MeasurableSpace problem.Omega := problem.measurableSpace
  letI : IsProbabilityMeasure problem.mu := problem.probabilityMeasure
  ∀ u, TendstoInDistribution
    (martingaleArrayTerminalSum (problem.projectedIncrement u)) atTop id
    (fun _ => problem.mu) (gaussianReal 0 (martingaleScoreQuadraticForm M u).toNNReal)

/-- Actual multivariate convergence of the vector terminal score. -/
def MartingaleCLTProblem.VectorSumConvergesToGaussian
    {D : Type*} [Fintype D] [DecidableEq D]
    (problem : MartingaleCLTProblem D) (M : Matrix D D ℝ) : Prop :=
  letI : MeasurableSpace problem.Omega := problem.measurableSpace
  letI : IsProbabilityMeasure problem.mu := problem.probabilityMeasure
  TendstoInDistribution problem.terminalSum atTop id
    (fun _ => problem.mu) (multivariateGaussian 0 M)

/-- A linear projection of `N(0,M)` is the scalar Gaussian with variance
`u^T M u`. -/
theorem multivariateGaussian_map_inner
    {D : Type*} [Fintype D] [DecidableEq D]
    (M : Matrix D D ℝ) (hM : M.PosSemidef)
    (u : MartingaleScoreSpace D) :
    (multivariateGaussian 0 M).map (innerSL ℝ u) =
      gaussianReal 0 (martingaleScoreQuadraticForm M u).toNNReal := by
  rw [IsGaussian.map_eq_gaussianReal]
  congr 2
  · rw [ContinuousLinearMap.integral_comp_id_comm]
    · simp
    · exact IsGaussian.integrable_id
  · change Var[(fun x => ⟪u, x⟫); multivariateGaussian 0 M] =
      martingaleScoreQuadraticForm M u
    rw [← covarianceBilin_self IsGaussian.memLp_two_id,
      covarianceBilin_multivariateGaussian hM]
    rfl




end

end QubitOracle.Paper
