import QubitOracle.Paper.MartingaleCLT
import QubitOracle.Paper.MartingaleCLTConsolidated
import QubitOracle.Paper.SourceFaithfulMinimax

/-!
# Adaptive martingale LAN as convergence of statistical experiments

This module joins the concrete martingale score theorem to the actual
Radon--Nikodym likelihood-ratio definition in `SourceFaithfulMinimax`.
There are no proposition-valued placeholders: the remaining premises are
the Hall--Heyde hypotheses, local absolute continuity, and convergence in
probability of the displayed likelihood remainder.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory ProbabilityTheory

noncomputable section

/-- A sequence of local experiments on one common trajectory space. -/
def fixedSampleExperiment
    {D : Type*} [Fintype D] {Omega : Type} [MeasurableSpace Omega]
    (P : ℕ → LANParameter D → Measure Omega)
    (hP : ∀ n h, IsProbabilityMeasure (P n h)) :
    ℕ → StatisticalExperiment (LANParameter D) :=
  fun n =>
    { Sample := Omega
      measurableSpace := inferInstance
      measure := P n
      probabilityMeasure := hP n }

/-- A vector martingale triangular array on the same trajectory space as the
adaptive local experiments. -/
def fixedSampleMartingaleProblem
    {D : Type*} [Fintype D] {Omega : Type} [MeasurableSpace Omega]
    (mu : Measure Omega) (hmu : IsProbabilityMeasure mu)
    (filtration : ℕ → Filtration ℕ (inferInstance : MeasurableSpace Omega))
    (increment : ℕ → ℕ → Omega → MartingaleScoreSpace D) :
    MartingaleCLTProblem D where
  Omega := Omega
  measurableSpace := inferInstance
  mu := mu
  probabilityMeasure := hmu
  filtration := filtration
  increment := increment

/-- Concrete sufficient conditions for adaptive LAN.

The score CLT is proved from Hall--Heyde and Cramer--Wold.  The likelihood
premise is the actual Radon--Nikodym logarithmic expansion appearing in
`LANRemainderConvergesInProbability`, and `hDomination` is local absolute
continuity. -/
theorem adaptiveLANSequence_of_martingale_conditions
    {D : Type*} [Fintype D] [DecidableEq D]
    {Omega : Type} [MeasurableSpace Omega]
    (P : ℕ → LANParameter D → Measure Omega)
    (hP : ∀ n h, IsProbabilityMeasure (P n h))
    (mu : Measure Omega) (hmu : IsProbabilityMeasure mu)
    (hbase : ∀ n, P n 0 = mu)
    (filtration : ℕ → Filtration ℕ (inferInstance : MeasurableSpace Omega))
    (increment : ℕ → ℕ → Omega → MartingaleScoreSpace D)
    (M : Matrix D D ℝ) (hM : M.PosDef)
    (hMDS : MartingaleCLTProblem.IsSquareIntegrableMartingaleDifferenceArray
      (fixedSampleMartingaleProblem mu hmu filtration increment))
    (hLindeberg : MartingaleCLTProblem.HasConditionalLindeberg
      (fixedSampleMartingaleProblem mu hmu filtration increment))
    (hCovariance : MartingaleCLTProblem.ConditionalCovarianceConverges
      (fixedSampleMartingaleProblem mu hmu filtration increment) M)
    (hTerminalMeasurable : ∀ n,
      AEMeasurable
        ((fixedSampleMartingaleProblem mu hmu filtration increment).terminalSum n) mu)
    (hDomination : ∀ n h, P n h ≪ P n 0)
    (hRemainder : LANRemainderConvergesInProbability
      (fixedSampleExperiment P hP) M
      (fixedSampleMartingaleProblem mu hmu filtration increment).terminalSum) :
    IsLANSequence (fixedSampleExperiment P hP) M
      (fixedSampleMartingaleProblem mu hmu filtration increment).terminalSum := by
  refine ⟨hDomination, hRemainder, ?_⟩
  have hscore := martingale_score_clt_multivariate_consolidated
    (fixedSampleMartingaleProblem mu hmu filtration increment) M hM
    hMDS hLindeberg hCovariance hTerminalMeasurable
  simpa [LANScoreConverges, MartingaleCLTProblem.VectorSumConvergesToGaussian,
    fixedSampleExperiment, fixedSampleMartingaleProblem, hbase] using hscore

/-- The same concrete assumptions imply convergence of the adaptive local
experiments to the Gaussian score experiment.  This is the rigorous point at
which van der Vaart Theorem 9.4 enters the minimax route. -/
theorem adaptiveExperimentsConverge_gaussianScore_of_martingale_conditions
    {D : Type*} [Fintype D] [DecidableEq D]
    {Omega : Type} [MeasurableSpace Omega]
    (P : ℕ → LANParameter D → Measure Omega)
    (hP : ∀ n h, IsProbabilityMeasure (P n h))
    (mu : Measure Omega) (hmu : IsProbabilityMeasure mu)
    (hbase : ∀ n, P n 0 = mu)
    (filtration : ℕ → Filtration ℕ (inferInstance : MeasurableSpace Omega))
    (increment : ℕ → ℕ → Omega → MartingaleScoreSpace D)
    (M : Matrix D D ℝ) (hM : M.PosDef)
    (hMDS : MartingaleCLTProblem.IsSquareIntegrableMartingaleDifferenceArray
      (fixedSampleMartingaleProblem mu hmu filtration increment))
    (hLindeberg : MartingaleCLTProblem.HasConditionalLindeberg
      (fixedSampleMartingaleProblem mu hmu filtration increment))
    (hCovariance : MartingaleCLTProblem.ConditionalCovarianceConverges
      (fixedSampleMartingaleProblem mu hmu filtration increment) M)
    (hTerminalMeasurable : ∀ n,
      AEMeasurable
        ((fixedSampleMartingaleProblem mu hmu filtration increment).terminalSum n) mu)
    (hDomination : ∀ n h, P n h ≪ P n 0)
    (hRemainder : LANRemainderConvergesInProbability
      (fixedSampleExperiment P hP) M
      (fixedSampleMartingaleProblem mu hmu filtration increment).terminalSum) :
    ExperimentsConverge (fixedSampleExperiment P hP)
      (gaussianScoreExperiment M) :=
  vanDerVaart1998_theorem9_4 (fixedSampleExperiment P hP) M hM.posSemidef
    (fixedSampleMartingaleProblem mu hmu filtration increment).terminalSum
    (adaptiveLANSequence_of_martingale_conditions P hP mu hmu hbase filtration
      increment M hM hMDS hLindeberg hCovariance hTerminalMeasurable
      hDomination hRemainder)

end

end QubitOracle.Paper
