import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import QubitOracle.Paper.CramerWold

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

axiom hallHeyde1980_corollary3_1
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (filtration : ℕ → Filtration ℕ (inferInstance : MeasurableSpace Omega))
    (increment : ℕ → ℕ → Omega → ℝ)
    (variance : ℝ) (hvarianceNonnegative : 0 ≤ variance)
    (hmartingale : ∀ n, Martingale (martingaleArrayPartialSum increment n) (filtration n) mu)
    (hsquareIntegrable : ∀ n k, MemLp (increment n k) 2 mu)
    (hnested : ∀ n k, filtration n k ≤ filtration (n + 1) k)
    (hLindeberg : ∀ epsilon : ℝ, 0 < epsilon →
      TendstoInMeasure mu
        (hallHeydeArrayConditionalLindeberg mu filtration increment epsilon)
        atTop (fun _ => 0))
    (hConditionalVariance :
      TendstoInMeasure mu
        (hallHeydeArrayConditionalVariance mu filtration increment)
        atTop (fun _ => variance)) :
    TendstoInDistribution (martingaleArrayTerminalSum increment) atTop id
      (fun _ => mu) (gaussianReal 0 variance.toNNReal)

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

theorem martingale_score_clt
    {D : Type*} [Fintype D]
    (problem : MartingaleCLTProblem D) (M : Matrix D D ℝ)
    (hM : M.PosDef)
    (hMDS : problem.IsSquareIntegrableMartingaleDifferenceArray)
    (hLindeberg : problem.HasConditionalLindeberg)
    (hCovariance : problem.ConditionalCovarianceConverges M) :
    problem.SumConvergesToGaussian M := by
  letI : MeasurableSpace problem.Omega := problem.measurableSpace
  letI : IsProbabilityMeasure problem.mu := problem.probabilityMeasure
  intro u
  apply hallHeyde1980_corollary3_1 problem.mu problem.filtration
    (problem.projectedIncrement u) (martingaleScoreQuadraticForm M u)
  · exact hM.posSemidef.dotProduct_mulVec_nonneg (fun i => u i)
  · exact hMDS.1 u
  · exact hMDS.2.1 u
  · exact hMDS.2.2
  · exact hLindeberg u
  · exact hCovariance u

/-- Backward-compatible paper-facing name for the source-shaped score CLT. -/
theorem adaptiveScoreCLT_of_martingale_conditions
    {D : Type*} [Fintype D]
    (problem : MartingaleCLTProblem D) (M : Matrix D D ℝ)
    (hM : M.PosDef)
    (hMDS : problem.IsSquareIntegrableMartingaleDifferenceArray)
    (hLindeberg : problem.HasConditionalLindeberg)
    (hCovariance : problem.ConditionalCovarianceConverges M) :
    problem.SumConvergesToGaussian M :=
  martingale_score_clt problem M hM hMDS hLindeberg hCovariance

/-- Hall--Heyde in every direction, followed by the proved Cramer--Wold
device, gives the genuine multivariate score limit. -/
theorem martingale_score_clt_multivariate
    {D : Type*} [Fintype D] [DecidableEq D]
    (problem : MartingaleCLTProblem D) (M : Matrix D D ℝ)
    (hM : M.PosDef)
    (hMDS : problem.IsSquareIntegrableMartingaleDifferenceArray)
    (hLindeberg : problem.HasConditionalLindeberg)
    (hCovariance : problem.ConditionalCovarianceConverges M)
    (hTerminalMeasurable :
      letI : MeasurableSpace problem.Omega := problem.measurableSpace
      ∀ n, AEMeasurable (problem.terminalSum n) problem.mu) :
    problem.VectorSumConvergesToGaussian M := by
  letI : MeasurableSpace problem.Omega := problem.measurableSpace
  letI : IsProbabilityMeasure problem.mu := problem.probabilityMeasure
  apply cramerWold_tendstoInDistribution problem.terminalSum hTerminalMeasurable
  intro u
  have hscalar := martingale_score_clt problem M hM hMDS hLindeberg hCovariance u
  refine
    { forall_aemeasurable := fun n => by
        apply (hscalar.forall_aemeasurable n).congr
        filter_upwards [] with omega
        simp [MartingaleCLTProblem.terminalSum, martingaleArrayTerminalSum,
          martingaleArrayPartialSum, MartingaleCLTProblem.projectedIncrement,
          inner_sum]
      aemeasurable_limit := by fun_prop
      tendsto := ?_ }
  have hprojection (n : ℕ) :
      (fun omega => ⟪u, problem.terminalSum n omega⟫) =
        martingaleArrayTerminalSum (problem.projectedIncrement u) n := by
    funext omega
    simp [MartingaleCLTProblem.terminalSum, martingaleArrayTerminalSum,
      martingaleArrayPartialSum, MartingaleCLTProblem.projectedIncrement,
      inner_sum]
  simp_rw [hprojection]
  let pvec : ProbabilityMeasure ℝ :=
    ⟨(multivariateGaussian 0 M).map (innerSL ℝ u),
      Measure.isProbabilityMeasure_map (by fun_prop)⟩
  let pscalar : ProbabilityMeasure ℝ :=
    ⟨gaussianReal 0 (martingaleScoreQuadraticForm M u).toNNReal, inferInstance⟩
  have hlimit : pvec = pscalar := by
    apply Subtype.ext
    exact multivariateGaussian_map_inner M hM.posSemidef u
  have htarget :
      (⟨(multivariateGaussian 0 M).map (fun x => ⟪u, x⟫),
        Measure.isProbabilityMeasure_map (by fun_prop)⟩ : ProbabilityMeasure ℝ) = pvec := by
    apply Subtype.ext
    rfl
  rw [htarget, hlimit]
  simpa [pscalar] using hscalar.tendsto

end

end QubitOracle.Paper
