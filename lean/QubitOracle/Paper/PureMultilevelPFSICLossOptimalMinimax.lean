import QubitOracle.GillMassarBridge
import QubitOracle.Paper.AdaptiveMinimaxAssembly
import QubitOracle.Paper.AdaptiveMLEEfficiency
import QubitOracle.Paper.CanonicalTerminalInference
import QubitOracle.Paper.PureMultilevelGillMassarOptimization
import QubitOracle.Paper.PureMultilevelLossConstants

/-!
# Loss-optimal minimax inference for a multilevel pure-state PFSIC design

For a Hilbert space of dimension `d + 1`, the real tangent dimension is
`2 * d`.  In the normalized pure-state chart the optimal one-copy Fisher
information is `(1 / 2) I`; its inverse covariance is `2 I`, and the Gaussian
quadratic benchmark is `4 * d`.

This module proves four separate claims.

1. The half-QFI information matrix is positive definite, has inverse `2 I`,
   and has inverse trace `4 * d`.
2. The Gill--Massar trace budget makes this information shape optimal for
   every nonnegative isotropic quadratic tangent loss.
3. Explicit martingale, likelihood-remainder, score-root, Hessian, capped-risk,
   and tail hypotheses imply LAN, an all-estimator local-minimax lower bound,
   asymptotic linearity, the efficient Gaussian limit, and equality in the
   coordinate minimax bound.
4. The exact pure-projector identities turn the coordinate benchmark into
   the physical constants `d` for squared Bures/ordinary infidelity and
   `2 * d` for squared Frobenius loss.

No LAN, minimax, or estimator-efficiency conclusion is assumed by the main
theorem.  Its analytic hypotheses are the primitive conditions consumed by
the existing Hall--Heyde, van der Vaart, Pollard, and score-root interfaces.
-/

namespace QubitOracle.Paper
namespace PureMultilevelPFSICLossOptimalMinimax

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace Topology

noncomputable section

/-- Real tangent coordinates of a pure state in Hilbert dimension `d + 1`. -/
abbrev PureTangentIndex (d : Nat) := QubitOracle.TangentIndex d

/-- PFSIC information in the normalized pure-state chart: one half QFI. -/
def pfsicInformation (d : Nat) :
    Matrix (PureTangentIndex d) (PureTangentIndex d) Real :=
  rankOneInformationMatrix (PureTangentIndex d)

/-- Covariance of an efficient estimator under the PFSIC experiment. -/
def pfsicCovariance (d : Nat) :
    Matrix (PureTangentIndex d) (PureTangentIndex d) Real :=
  rankOneLimitCovariance (PureTangentIndex d)

theorem pfsicInformation_eq_half_identity (d : Nat) :
    pfsicInformation d =
      (1 / 2 : Real) •
        (1 : Matrix (PureTangentIndex d) (PureTangentIndex d) Real) := by
  rfl

theorem pfsicCovariance_eq_two_identity (d : Nat) :
    pfsicCovariance d =
      (2 : Real) •
        (1 : Matrix (PureTangentIndex d) (PureTangentIndex d) Real) := by
  rfl

theorem pfsicInformation_posDef (d : Nat) :
    (pfsicInformation d).PosDef := by
  simpa [pfsicInformation] using
    rankOneInformationMatrix_posDef (PureTangentIndex d)

theorem pfsicInformation_inv (d : Nat) :
    (pfsicInformation d)⁻¹ = pfsicCovariance d := by
  simpa [pfsicInformation, pfsicCovariance] using
    rankOneInformationMatrix_inv (PureTangentIndex d)

/-- The full `2d`-coordinate Gaussian squared-norm benchmark is `4d`. -/
theorem pfsicInformation_trace_inv (d : Nat) :
    Matrix.trace (pfsicInformation d)⁻¹ = 4 * (d : Real) := by
  rw [pfsicInformation_inv, pfsicCovariance,
    rankOneLimitCovariance, Matrix.trace_smul, Matrix.trace_one,
    QubitOracle.tangentIndex_card]
  simp only [Nat.cast_mul, Nat.cast_ofNat, smul_eq_mul]
  ring

/-- The Gaussian benchmark gives `d` for squared Bures/ordinary infidelity
and `2d` for squared Frobenius loss. -/
theorem pfsic_physical_loss_constants (d : Nat) :
    (1 / 4 : Real) * Matrix.trace (pfsicInformation d)⁻¹ = (d : Real) ∧
      (1 / 2 : Real) * Matrix.trace (pfsicInformation d)⁻¹ =
        2 * (d : Real) := by
  rw [pfsicInformation_trace_inv]
  constructor <;> ring

/-! ## Design optimality from the Gill--Massar budget -/

/-- A concrete equal-two-basis PFSIC realizes the half-QFI information and is
optimal over every regular finite one-copy POVM for isotropic tangent loss. -/
theorem pfsicInformation_optimal_over_finitePOVM
    {d : Nat} {O : Type} [Fintype O]
    (F : QubitOracle.OracleFrame d) (g : Real) (hg : 0 ≤ g)
    (P : QubitOracle.FinitePOVM (Fin (d + 1)) O)
    (hP : (QubitOracle.referenceFisher P).PosDef) :
    QubitOracle.isotropicRisk g (pfsicInformation d) ≤
      QubitOracle.isotropicRisk g (QubitOracle.referenceFisher P) := by
  simpa [pfsicInformation, rankOneInformationMatrix,
    QubitOracle.equalMixtureFisher_eq_half_identity F] using
    QubitOracle.twoBasis_optimal_over_finitePOVM F g hg P hP

/-- Equality in the regular finite-POVM design bound holds exactly at
half-QFI information. -/
theorem finitePOVM_ties_pfsic_iff_half_qfi
    {d : Nat} {O : Type} [Fintype O]
    (F : QubitOracle.OracleFrame d) (g : Real) (hg : 0 < g)
    (P : QubitOracle.FinitePOVM (Fin (d + 1)) O)
    (hP : (QubitOracle.referenceFisher P).PosDef) :
    QubitOracle.isotropicRisk g (QubitOracle.referenceFisher P) =
        QubitOracle.isotropicRisk g (pfsicInformation d) ↔
      QubitOracle.referenceFisher P = pfsicInformation d := by
  simpa [pfsicInformation, rankOneInformationMatrix,
    QubitOracle.equalMixtureFisher_eq_half_identity F] using
    QubitOracle.finitePOVM_ties_twoBasis_iff_isotropic F g hg P hP

theorem pfsic_frobenius_quadratic_constant
    {d : Nat} (F : QubitOracle.OracleFrame d) :
    QubitOracle.isotropicRisk (1 / 2 : Real) (pfsicInformation d) =
      2 * d := by
  simpa [pfsicInformation, rankOneInformationMatrix,
    QubitOracle.equalMixtureFisher_eq_half_identity F] using
    QubitOracle.equalMixture_frobeniusRisk F

theorem pfsic_bures_infidelity_quadratic_constant
    {d : Nat} (F : QubitOracle.OracleFrame d) :
    QubitOracle.isotropicRisk (1 / 4 : Real) (pfsicInformation d) = d := by
  simpa [pfsicInformation, rankOneInformationMatrix,
    QubitOracle.equalMixtureFisher_eq_half_identity F] using
    QubitOracle.equalMixture_buresQuadraticRisk F

/-! ## LAN lower bound for every estimator -/

/-- Once the adaptive experiments converge to the half-QFI Gaussian score
experiment, every estimator sequence obeys the sharp `4d` coordinate lower
bound.  No regularity assumption is imposed on the estimator. -/
theorem pfsic_allEstimator_coordinateLocalMinimax_lowerBound
    {d : Nat}
    (E : Nat → StatisticalExperiment (LANParameter (PureTangentIndex d)))
    (hExperiment : ExperimentsConverge E
      (gaussianScoreExperiment (pfsicInformation d)))
    (T : (n : Nat) → Statistic (E n) (LANParameter (PureTangentIndex d))) :
    ENNReal.ofReal (4 * (d : Real)) ≤
      asymptoticFiniteLocalQuadraticRisk E T := by
  have h := gaussianScore_localAsymptoticMinimax_quadratic
    (pfsicInformation d) (pfsicInformation_posDef d) E hExperiment T
  rwa [pfsicInformation_trace_inv] at h

/-! ## Complete explicit-condition LAN, minimax, and attainment theorem -/

/-- Main source-relative endpoint for the projected-pilot/frozen-PFSIC
architecture.

The hypotheses are deliberately below the level of LAN or minimax: they are
the martingale-difference, Lindeberg, covariance, likelihood-remainder,
score-root, Hessian, Taylor, capped-risk, and uniform-tail conditions that a
concrete protocol must verify.  From them Lean derives LAN itself, the lower
bound for every estimator, and equality for the displayed score-root
estimator. -/
theorem twoStagePFSIC_martingaleLAN_minimax_and_attainment
    {d : Nat} {Omega : Type} [MeasurableSpace Omega]
    (P : Nat → LANParameter (PureTangentIndex d) → Measure Omega)
    (hP : ∀ n h, IsProbabilityMeasure (P n h))
    (mu : Measure Omega) [hmu : IsProbabilityMeasure mu]
    (hbase : ∀ n, P n 0 = mu)
    (filtration : Nat → Filtration Nat
      (inferInstance : MeasurableSpace Omega))
    (increment : Nat → Nat → Omega →
      MartingaleScoreSpace (PureTangentIndex d))
    (hMDS : MartingaleCLTProblem.IsSquareIntegrableMartingaleDifferenceArray
      (fixedSampleMartingaleProblem (D := PureTangentIndex d)
        mu hmu filtration increment))
    (hLindeberg : MartingaleCLTProblem.HasConditionalLindeberg
      (fixedSampleMartingaleProblem (D := PureTangentIndex d)
        mu hmu filtration increment))
    (hCovariance : MartingaleCLTProblem.ConditionalCovarianceConverges
      (fixedSampleMartingaleProblem (D := PureTangentIndex d)
        mu hmu filtration increment) (pfsicInformation d))
    (hTerminalMeasurable : ∀ n,
      AEMeasurable
        ((fixedSampleMartingaleProblem (D := PureTangentIndex d)
          mu hmu filtration increment).terminalSum n) mu)
    (hDomination : ∀ n h, P n h ≪ P n 0)
    (hLANRemainder : LANRemainderConvergesInProbability
      (fixedSampleExperiment (D := PureTangentIndex d) P hP)
      (pfsicInformation d)
      (fixedSampleMartingaleProblem (D := PureTangentIndex d)
        mu hmu filtration increment).terminalSum)
    (problem : AdaptiveScoreRootProblem (PureTangentIndex d) Omega)
    (hroot : problem.IsScoreRoot mu)
    (htaylor : problem.HasScoreTaylorExpansion mu
      (fixedSampleMartingaleProblem (D := PureTangentIndex d)
        mu hmu filtration increment).terminalSum)
    (hHessian : problem.HasUniformHessianLinearizationAtRoot mu
      (pfsicInformation d))
    (hTaylorRemainder : TendstoInMeasure mu problem.taylorRemainder atTop 0)
    (hResidualMeasurable : ∀ n,
      AEMeasurable (problem.asymptoticLinearResidual
        (pfsicInformation d)
        (fixedSampleMartingaleProblem (D := PureTangentIndex d)
          mu hmu filtration increment).terminalSum n) mu)
    (hEstimatorMeasurable : ∀ n, Measurable (problem.localError n))
    (hCapped : ∀ I : Finset (LANParameter (PureTangentIndex d)), I.Nonempty →
      CappedFiniteLocalRisksConvergeToCenteredGaussian
        (pfsicInformation d)
        (fixedSampleExperiment (D := PureTangentIndex d) P hP)
        (problem.statistic P hP hEstimatorMeasurable) I)
    (hTail : ∀ I : Finset (LANParameter (PureTangentIndex d)), I.Nonempty →
      HasUniformFiniteLocalQuadraticTails
        (fixedSampleExperiment (D := PureTangentIndex d) P hP)
        (problem.statistic P hP hEstimatorMeasurable) I) :
    IsLANSequence
        (fixedSampleExperiment (D := PureTangentIndex d) P hP)
        (pfsicInformation d)
        (fixedSampleMartingaleProblem (D := PureTangentIndex d)
          mu hmu filtration increment).terminalSum ∧
      (∀ T : (n : Nat) → Statistic
          (fixedSampleExperiment (D := PureTangentIndex d) P hP n)
          (LANParameter (PureTangentIndex d)),
        ENNReal.ofReal (4 * (d : Real)) ≤
          asymptoticFiniteLocalQuadraticRisk
            (fixedSampleExperiment (D := PureTangentIndex d) P hP) T) ∧
      problem.HasAsymptoticLinearRepresentation mu (pfsicInformation d)
        (fixedSampleMartingaleProblem (D := PureTangentIndex d)
          mu hmu filtration increment).terminalSum ∧
      TendstoInDistribution problem.localError atTop
        (fun z => lanMatrixAction (pfsicCovariance d) z)
        (fun _ => mu) (multivariateGaussian 0 (pfsicInformation d)) ∧
      asymptoticFiniteLocalQuadraticRisk
          (fixedSampleExperiment (D := PureTangentIndex d) P hP)
          (problem.statistic P hP hEstimatorMeasurable) =
        ENNReal.ofReal (4 * (d : Real)) := by
  have hLAN := adaptiveLANSequence_of_martingale_conditions
    P hP mu hmu hbase filtration increment
    (pfsicInformation d) (pfsicInformation_posDef d)
    hMDS hLindeberg hCovariance hTerminalMeasurable
    hDomination hLANRemainder
  have hLower : ∀ T : (n : Nat) → Statistic
      (fixedSampleExperiment (D := PureTangentIndex d) P hP n)
      (LANParameter (PureTangentIndex d)),
      ENNReal.ofReal (4 * (d : Real)) ≤
        asymptoticFiniteLocalQuadraticRisk
          (fixedSampleExperiment (D := PureTangentIndex d) P hP) T := by
    intro T
    have h := adaptive_localAsymptoticMinimax_of_martingale_conditions
      P hP mu hmu hbase filtration increment
      (pfsicInformation d) (pfsicInformation_posDef d)
      hMDS hLindeberg hCovariance hTerminalMeasurable
      hDomination hLANRemainder T
    rwa [pfsicInformation_trace_inv] at h
  have hEff := adaptiveMartingaleLAN_scoreRoot_attains_minimax
    P hP mu hbase filtration increment
    (pfsicInformation d) (pfsicInformation_posDef d)
    hMDS hLindeberg hCovariance hTerminalMeasurable
    hDomination hLANRemainder problem hroot htaylor hHessian
    hTaylorRemainder hResidualMeasurable hEstimatorMeasurable hCapped hTail
  rcases hEff with ⟨hLinear, hGaussian, hAttains⟩
  have hGaussian' : TendstoInDistribution problem.localError atTop
      (fun z => lanMatrixAction (pfsicCovariance d) z)
      (fun _ => mu) (multivariateGaussian 0 (pfsicInformation d)) := by
    simpa only [pfsicInformation_inv] using hGaussian
  have hRisk : asymptoticFiniteLocalQuadraticRisk
      (fixedSampleExperiment (D := PureTangentIndex d) P hP)
      (problem.statistic P hP hEstimatorMeasurable) =
        ENNReal.ofReal (4 * (d : Real)) := by
    unfold AttainsGaussianLocalAsymptoticMinimaxBound at hAttains
    rwa [pfsicInformation_trace_inv] at hAttains
  exact ⟨hLAN, hLower, hLinear, hGaussian', hRisk⟩

end

end PureMultilevelPFSICLossOptimalMinimax
end QubitOracle.Paper
