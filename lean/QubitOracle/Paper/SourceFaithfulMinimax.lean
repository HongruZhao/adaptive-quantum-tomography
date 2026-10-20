import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

namespace QubitOracle.Paper

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace Topology

noncomputable section

universe u v w

abbrev LANParameter (D : Type*) [Fintype D] := EuclideanSpace ℝ D

structure StatisticalExperiment (H : Type u) where
  Sample : Type v
  measurableSpace : MeasurableSpace Sample
  measure : H → @Measure Sample measurableSpace
  probabilityMeasure : ∀ h, @IsProbabilityMeasure Sample measurableSpace (measure h)

def experimentLikelihoodRatio
    {H : Type*} (E : StatisticalExperiment H) (h h0 : H) : E.Sample → ℝ :=
  letI : MeasurableSpace E.Sample := E.measurableSpace
  fun omega => ((E.measure h).rnDeriv (E.measure h0) omega).toReal

def experimentLogLikelihoodRatio
    {H : Type*} (E : StatisticalExperiment H) (h h0 : H) : E.Sample → ℝ :=
  fun omega => Real.log (experimentLikelihoodRatio E h h0 omega)

def likelihoodRatioVector
    {H : Type*} (E : StatisticalExperiment H) (I : Finset H) (h0 : H) :
    E.Sample → EuclideanSpace ℝ I :=
  fun omega => WithLp.toLp 2 (fun h : I =>
    experimentLikelihoodRatio E h.1 h0 omega)

def LikelihoodRatioVectorsConverge
    {H : Type*} (E : ℕ → StatisticalExperiment H)
    (E_limit : StatisticalExperiment H) (I : Finset H) (h0 : H) : Prop :=
  letI (n : ℕ) : MeasurableSpace (E n).Sample := (E n).measurableSpace
  letI (n : ℕ) : IsProbabilityMeasure ((E n).measure h0) :=
    (E n).probabilityMeasure h0
  letI : MeasurableSpace E_limit.Sample := E_limit.measurableSpace
  letI : IsProbabilityMeasure (E_limit.measure h0) := E_limit.probabilityMeasure h0
  TendstoInDistribution
    (fun n => likelihoodRatioVector (E n) I h0) atTop
    (likelihoodRatioVector E_limit I h0)
    (fun n => (E n).measure h0) (E_limit.measure h0)

/-- van der Vaart Definition 9.1, stated through every finite vector of
likelihood ratios and every base point. -/
def ExperimentsConverge
    {H : Type*} (E : ℕ → StatisticalExperiment H)
    (E_limit : StatisticalExperiment H) : Prop :=
  ∀ (I : Finset H) (h0 : H), LikelihoodRatioVectorsConverge E E_limit I h0

def lanMatrixAction
    {D : Type*} [Fintype D] (J : Matrix D D ℝ) (h : LANParameter D) :
    LANParameter D :=
  WithLp.toLp 2 (J.mulVec (fun i => h i))

def lanQuadraticForm
    {D : Type*} [Fintype D] (J : Matrix D D ℝ) (h : LANParameter D) : ℝ :=
  dotProduct (fun i => h i) (J.mulVec (fun i => h i))

def gaussianScoreExperiment
    {D : Type*} [Fintype D] [DecidableEq D] (J : Matrix D D ℝ) :
    StatisticalExperiment (LANParameter D) where
  Sample := LANParameter D
  measurableSpace := inferInstance
  measure h := multivariateGaussian (lanMatrixAction J h) J
  probabilityMeasure _ := inferInstance

def gaussianLocationExperiment
    {D : Type*} [Fintype D] [DecidableEq D] (Sigma : Matrix D D ℝ) :
    StatisticalExperiment (LANParameter D) where
  Sample := LANParameter D
  measurableSpace := inferInstance
  measure h := multivariateGaussian h Sigma
  probabilityMeasure _ := inferInstance

def LANRemainderConvergesInProbability
    {D : Type*} [Fintype D]
    (E : ℕ → StatisticalExperiment (LANParameter D))
    (J : Matrix D D ℝ)
    (score : ∀ n, (E n).Sample → LANParameter D) : Prop :=
  ∀ (h : LANParameter D) (epsilon : ℝ), 0 < epsilon →
    Tendsto
      (fun n => (E n).measure 0
        {omega | epsilon ≤
          |experimentLogLikelihoodRatio (E n) h 0 omega -
            (⟪h, score n omega⟫ - (1 / 2 : ℝ) * lanQuadraticForm J h)|})
      atTop (nhds 0)

def LANScoreConverges
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : ℕ → StatisticalExperiment (LANParameter D))
    (J : Matrix D D ℝ)
    (score : ∀ n, (E n).Sample → LANParameter D) : Prop :=
  letI (n : ℕ) : MeasurableSpace (E n).Sample := (E n).measurableSpace
  letI (n : ℕ) : IsProbabilityMeasure ((E n).measure 0) :=
    (E n).probabilityMeasure 0
  TendstoInDistribution score atTop id
    (fun n => (E n).measure 0) (multivariateGaussian 0 J)

/-- Concrete LAN definition: local domination, the likelihood-ratio expansion,
and Gaussian score convergence under the base experiment. -/
def IsLANSequence
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : ℕ → StatisticalExperiment (LANParameter D))
    (J : Matrix D D ℝ)
    (score : ∀ n, (E n).Sample → LANParameter D) : Prop :=
  (∀ n h, (E n).measure h ≪ (E n).measure 0) ∧
  LANRemainderConvergesInProbability E J score ∧
  LANScoreConverges E J score

/-- Exact source interface for van der Vaart (1998), Theorem 9.4. -/
axiom vanDerVaart1998_theorem9_4
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : ℕ → StatisticalExperiment (LANParameter D))
    (J : Matrix D D ℝ) (hJ : J.PosSemidef)
    (score : ∀ n, (E n).Sample → LANParameter D)
    (hLAN : IsLANSequence E J score) :
    ExperimentsConverge E (gaussianScoreExperiment J)

structure Statistic {H : Type*} (E : StatisticalExperiment H)
    (A : Type*) [MeasurableSpace A] where
  toFun : E.Sample → A
  measurable : @Measurable E.Sample A E.measurableSpace inferInstance toFun

instance {H : Type*} {E : StatisticalExperiment H} {A : Type*}
    [MeasurableSpace A] : CoeFun (Statistic E A) (fun _ => E.Sample → A) :=
  ⟨Statistic.toFun⟩

def statisticLaw
    {H A : Type*} [MeasurableSpace A]
    (E : StatisticalExperiment H) (T : Statistic E A) (h : H) : Measure A :=
  letI : MeasurableSpace E.Sample := E.measurableSpace
  (E.measure h).map T

structure RandomizedStatistic {H : Type*} (E : StatisticalExperiment H)
    (A : Type*) [MeasurableSpace A] where
  kernel : @Kernel E.Sample A E.measurableSpace inferInstance
  isMarkovKernel : @IsMarkovKernel E.Sample A E.measurableSpace inferInstance kernel

def randomizedStatisticLaw
    {H A : Type*} [MeasurableSpace A]
    (E : StatisticalExperiment H) (T : RandomizedStatistic E A) (h : H) : Measure A :=
  letI : MeasurableSpace E.Sample := E.measurableSpace
  letI : IsMarkovKernel T.kernel := T.isMarkovKernel
  T.kernel ∘ₘ E.measure h

def IsDominatedExperiment {H : Type*} (E : StatisticalExperiment H) : Prop :=
  letI : MeasurableSpace E.Sample := E.measurableSpace
  ∃ dominating : Measure E.Sample,
    SigmaFinite dominating ∧ ∀ h, E.measure h ≪ dominating

def IsBowlShapedLoss
    {A : Type*} [AddCommGroup A] [Module ℝ A]
    (ell : A → ℝ≥0∞) : Prop :=
  (∀ c : ℝ≥0∞, Convex ℝ {x | ell x ≤ c}) ∧
  ∀ x, ell (-x) = ell x

def gaussianDecisionRisk
    {D A : Type*} [Fintype D] [DecidableEq D]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [MeasurableSpace A]
    (Sigma : Matrix D D ℝ) (target : LANParameter D →ₗ[ℝ] A)
    (ell : A → ℝ≥0∞)
    (T : RandomizedStatistic (gaussianLocationExperiment Sigma) A)
    (h : LANParameter D) : ℝ≥0∞ :=
  ∫⁻ z, ell (z - target h) ∂
    randomizedStatisticLaw (gaussianLocationExperiment Sigma) T h

end

end QubitOracle.Paper
