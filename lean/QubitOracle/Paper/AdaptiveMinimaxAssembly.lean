import QubitOracle.Paper.AdaptiveLANExperimentBridge
import QubitOracle.Paper.SourceFaithfulAsymptoticMinimax

/-!
# Adaptive LAN-to-minimax assembly

This module composes the martingale sufficient conditions for adaptive LAN,
the LAN-to-Gaussian-experiment theorem, and Le Cam's asymptotic minimax
theorem.  The resulting statement applies to every estimator sequence and does
not assume LAN as an input.
-/

namespace QubitOracle.Paper

open MeasureTheory ProbabilityTheory

noncomputable section

/-- General adaptive local asymptotic minimax theorem obtained from explicit
martingale and likelihood-remainder hypotheses.  This statement is not
qubit-specific; qubit protocols enter only when these hypotheses and the
information matrix `M` are instantiated. -/
theorem adaptive_localAsymptoticMinimax_of_martingale_conditions
    {D : Type*} [Fintype D] [DecidableEq D]
    {Omega : Type} [MeasurableSpace Omega]
    (P : ℕ → LANParameter D → Measure Omega)
    (hP : ∀ n h, IsProbabilityMeasure (P n h))
    (mu : Measure Omega) (hmu : IsProbabilityMeasure mu)
    (hbase : ∀ n, P n 0 = mu)
    (filtration : ℕ → Filtration ℕ inferInstance)
    (increment : ℕ → ℕ → Omega → MartingaleScoreSpace D)
    (M : Matrix D D ℝ) (hM : M.PosDef)
    (hMDS : (fixedSampleMartingaleProblem mu hmu filtration increment).IsSquareIntegrableMartingaleDifferenceArray)
    (hLindeberg : (fixedSampleMartingaleProblem mu hmu filtration increment).HasConditionalLindeberg)
    (hCovariance : (fixedSampleMartingaleProblem mu hmu filtration increment).ConditionalCovarianceConverges M)
    (hTerminalMeasurable : ∀ n,
      AEMeasurable
        ((fixedSampleMartingaleProblem mu hmu filtration increment).terminalSum n) mu)
    (hDomination : ∀ n h, (P n h).AbsolutelyContinuous (P n 0))
    (hRemainder : LANRemainderConvergesInProbability
      (fixedSampleExperiment P hP) M
      (fixedSampleMartingaleProblem mu hmu filtration increment).terminalSum)
    (T : (n : ℕ) →
      Statistic (fixedSampleExperiment P hP n) (LANParameter D)) :
    ENNReal.ofReal (Matrix.trace M⁻¹) ≤
      asymptoticFiniteLocalQuadraticRisk (fixedSampleExperiment P hP) T := by
  apply gaussianScore_localAsymptoticMinimax_quadratic M hM
  exact adaptiveExperimentsConverge_gaussianScore_of_martingale_conditions
    P hP mu hmu hbase filtration increment M hM hMDS hLindeberg hCovariance
      hTerminalMeasurable hDomination hRemainder

end

end QubitOracle.Paper
