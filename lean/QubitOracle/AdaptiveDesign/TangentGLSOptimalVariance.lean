import QubitOracle.AdaptiveDesign.TangentGLSNormalizedError
import QubitOracle.AdaptiveDesign.EfficientBornScoreCLT
import QubitOracle.AdaptiveDesign.TangentGLSVarianceStatement
import QubitOracle.GillMassarBridge

/-!
# Optimal asymptotic covariance of the implemented all-record estimator

This file proves the previously stated `OptimalVarianceStatement` for the
literal raw-estimate / leading-ray / protected tangent-GLS / normalization
algorithm. The fitted weights and preliminary estimator use the same data.
The proof establishes all estimator-specific remainder bounds, information
limits and measurability. The finite adaptive response CLT is proved
directly. The audited endpoint has no scientific axiom dependencies.

The phase-pair corollary takes an identifying, reference-regular rank-one
seed. Its Fisher identity is a theorem, not a further supplied assumption.
The conclusion is a pointwise Gaussian limit; no expected-loss convergence
or uniform minimax statement is asserted here.
`PureAmplitudeEndpoints` transfers this result to the exact amplitude
chart printed in the paper.
-/
namespace QubitOracle.AdaptiveDesign.TangentGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive
open GeneralPOVM Filter MeasureTheory ProbabilityTheory ProbabilityCalculus
open scoped BigOperators Topology InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

variable {d : ℕ} {O : Type} [Fintype O]

theorem trueCoordinate_apply (truth : PureVector d) (A : HermitianSpace (d+1)) :
    trueCoordinate truth A = WithLp.toLp 2 (matrixGradient
      ((trueFrame d truth).conjTranspose * toMatrix A * trueFrame d truth)) := by
  change WithLp.toLp 2 (matrixGradient
    ((trueFrame d truth).conjTranspose * toMatrix A * (trueFrame d truth).conjTranspose.conjTranspose)) = _
  rw [Matrix.conjTranspose_conjTranspose]

variable [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]

theorem trueFrameCoordinates_actual
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) (n : ℕ) (path : AdaptiveInfinitePath O) :
    trueFrameCoordinates truth (actualEstimatedState P hI hp regularization ridge hr hη batchSize path n) =
      (2 : ℝ) • trueCoordinate truth (actualProjectorError P hI hp truth regularization ridge hr hη batchSize n path) := by
  rw [trueCoordinate_apply]
  rfl

theorem trueCoordinate_ambientScore (P : FinitePOVM (Fin (d+1)) O) (truth : PureVector d)
    (floor : ℝ) (U : GlobalPFSICBorn.Action d) (y : O) :
    trueCoordinate truth (ambientScoreResponse P truth floor U y) =
      ProtectedBornScore.response P truth floor U y := by
  simp only [ambientScoreResponse, centeredLookup, map_sub, map_sum, map_smul,
    trueCoordinate_responseVector, bornProbability_pure_eq_mass,
    ProtectedBornScore.response, ProtectedBornScore.score, ProtectedBornScore.rawScore,
    ProtectedBornScore.scoreMean, ProtectedBornScore.gradientVector, denominator]

theorem fullScore_eq_coordinate
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P)
    (truth : PureVector d) (regularization : ℝ) (hr : 0 < regularization)
    (batchSize : ℕ → ℕ) (n : ℕ) (path : AdaptiveInfinitePath O) :
    EfficientBornScoreCLT.fullScore P hI truth regularization hr batchSize n path =
      (2 : ℝ) • trueCoordinate truth ((Real.sqrt (n : ℝ))⁻¹ • tangentProjector truth
        (actualScoreSum P hI truth (referenceFloor P) regularization hr batchSize n path)) := by
  simp only [map_smul, trueCoordinate_projection, actualScoreSum, map_sum]
  simp only [EfficientBornScoreCLT.fullScore, AdaptiveRidgeConsistency.actualVectorResponse,
    EfficientBornScoreCLT.response, ← trueCoordinate_ambientScore, ← Finset.smul_sum]
  module

theorem actual_coordinates_measurable
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) (n : ℕ) :
    Measurable (fun path => Real.sqrt (n : ℝ) • trueFrameCoordinates truth
      (actualEstimatedState P hI hp regularization ridge hr hη batchSize path n)) := by
  exact (FiniteHistoryStatistics.actualStatistic_stronglyMeasurable P hI regularization hr batchSize n
    (fun raw data => Real.sqrt (n : ℝ) • trueFrameCoordinates truth
      (rankOneDensity (estimateFromRaw raw data (referenceFloor P) ridge (referenceFloor_pos P hp) hη).val))).measurable

theorem actual_coordinates_minus_score_zero
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P) (hF : FisherSymmetric P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth)
      (fun (n : ℕ) path => Real.sqrt (n : ℝ) • trueFrameCoordinates truth
        (actualEstimatedState P hI hp regularization ridge hr hη batchSize path n) -
        EfficientBornScoreCLT.fullScore P hI truth regularization hr batchSize n path) atTop (fun _ => 0) := by
  have hh := continuousAt_const
    (actualProjectorError_linearization P hI hp hF truth regularization ridge hr hη batchSize hpositive)
    (show ContinuousAt (fun x : HermitianSpace (d+1) => (2 : ℝ) • trueCoordinate truth x) 0 by fun_prop)
  have he (n : ℕ) (path : AdaptiveInfinitePath O) :
      (2 : ℝ) • trueCoordinate truth
        (Real.sqrt ((n+1 : ℕ) : ℝ) • actualProjectorError P hI hp truth regularization ridge hr hη batchSize (n+1) path -
          (Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹ • tangentProjector truth
            (actualScoreSum P hI truth (referenceFloor P) regularization hr batchSize (n+1) path)) =
      Real.sqrt ((n+1 : ℕ) : ℝ) • trueFrameCoordinates truth
        (actualEstimatedState P hI hp regularization ridge hr hη batchSize path (n+1)) -
        EfficientBornScoreCLT.fullScore P hI truth regularization hr batchSize (n+1) path := by
    rw [trueFrameCoordinates_actual, fullScore_eq_coordinate]
    simp only [map_sub, smul_sub, map_smul]
    module
  simp only [map_zero, smul_zero] at hh
  have hshift := hh.congr (fun n => Eventually.of_forall (fun path => he n path))
    EventuallyEq.rfl
  intro ε hε
  exact (tendsto_add_atTop_iff_nat 1).mp (hshift ε hε)

/-- The final normalized estimator attains covariance `2 H(P₀)⁻¹` in the
paper's QFI-normalized true tangent coordinates. Every data-specific
hypothesis used to transfer the score CLT has been proved above. -/
theorem optimalVariance
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P) (hF : FisherSymmetric P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    OptimalVarianceStatement P hI hp regularization ridge hr hη batchSize truth := by
  unfold OptimalVarianceStatement
  exact tendstoInDistribution_of_tendstoInMeasure_sub _ _
    (EfficientBornScoreCLT.fullScore_clt P hI hp hF truth regularization hr batchSize hpositive)
    (actual_coordinates_minus_score_zero P hI hp hF truth regularization ridge hr hη batchSize hpositive)
    (fun n => (actual_coordinates_measurable P hI hp truth regularization ridge hr hη batchSize n).aemeasurable)

/-- Phase-pair construction: C1, C2 and rank one on the seed suffice; the
Fisher-symmetry identity is supplied by the proved phase-pair lemma. -/
theorem phasePair_optimalVariance
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P) (hR : PhasePair.RankOne P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    OptimalVarianceStatement (PhasePair.paired P) (PhasePair.paired_identifying P hI)
      (PhasePair.paired_regular P hp) regularization ridge hr hη batchSize truth :=
  optimalVariance (PhasePair.paired P) (PhasePair.paired_identifying P hI)
    (PhasePair.paired_regular P hp) (PhasePair.paired_fisher_of_rankOne P hp hR)
    truth regularization ridge hr hη batchSize hpositive

/-- The weighted trace of the proved Gaussian covariance is the sharp
isotropic design value. This is a covariance criterion, not a limit of
expected loss. -/
theorem limitingCovariance_weightedTrace (g : ℝ) :
    g * Matrix.trace ((2 : ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)) = 4*g*d := by
  rw [Matrix.trace_smul, Matrix.trace_one, tangentIndex_card]
  simp only [smul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- Optimality for isotropic local quadratic losses among all finite
single-copy POVMs with positive definite reference Fisher information.
The finite-dimensional Gill--Massar bound is proved, not axiomatized. -/
theorem limitingCovariance_optimal {Y : Type} [Fintype Y]
    (competitor : FinitePOVM (Fin (d+1)) Y) (hpos : (referenceFisher competitor).PosDef)
    (g : ℝ) (hg : 0 ≤ g) :
    g * Matrix.trace ((2 : ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)) ≤
      isotropicRisk g (referenceFisher competitor) := by
  rw [limitingCovariance_weightedTrace]
  exact finitePOVM_risk_lower_bound g competitor hg hpos

end
end QubitOracle.AdaptiveDesign.TangentGLS
