-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMFinalLinearization
import QubitOracle.AdaptiveDesign.PVMUnweightedScoreCLT
import QubitOracle.AdaptiveDesign.PVMCorrectedConsistency
import QubitOracle.AdaptiveDesign.TangentGLSOptimalVariance

/-! The actual exploration-pilot / tangent-LS / normalized estimator has
optimal Gaussian covariance under sqrt(n)/E_n -> 0. The bounded-response
CLT is proved directly; the endpoint has no scientific axioms. -/
namespace QubitOracle.AdaptiveDesign.PVMPilotGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive TangentGLS
open Filter MeasureTheory ProbabilityTheory ProbabilityCalculus
open scoped BigOperators InnerProductSpace Topology
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
variable [PVMPilotSchedule.Schedule]
variable {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d]

lemma trueCoordinates_actual (truth : PureVector d) (ridge : ℝ) (hr : 0 < ridge)
    (batchSize : ℕ → ℕ) (n : ℕ) (path : AdaptiveInfinitePath (PVMPilotAdaptive.PVMOutcome d)) :
    trueFrameCoordinates truth (actualEstimatedState ridge hr batchSize path n) =
      (2:ℝ) • trueCoordinate truth (projectorError truth ridge hr batchSize n path) := by
  rw [trueCoordinate_apply]
  rfl

lemma corrected_coordinates_measurable (truth : PureVector d) (ridge : ℝ) (hr : 0 < ridge)
    (batchSize : ℕ → ℕ) (n : ℕ) :
    Measurable (fun path => Real.sqrt (n:ℝ) • trueFrameCoordinates truth
      (actualEstimatedState ridge hr batchSize path n)) := by
  exact (actualStatistic_stronglyMeasurable batchSize n (fun raw data => Real.sqrt (n:ℝ) •
    trueFrameCoordinates truth (rankOneDensity
      (estimateFromRaw raw data (floor d) ridge (floor_pos d) hr).val))).measurable

lemma corrected_coordinates_minus_score_zero (truth : PureVector d) (ridge : ℝ) (hr : 0 < ridge)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) (hbudget : PVMPilotSchedule.OneStepBudget) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth))
      (fun (n : ℕ) path => Real.sqrt (n:ℝ) • trueFrameCoordinates truth (actualEstimatedState ridge hr batchSize path n)-
        fullScore truth batchSize n path) atTop (fun _ => 0) := by
  have hh := continuousAt_const (projectorError_linearization truth ridge hr batchSize hpositive hbudget)
    (show ContinuousAt (fun x : HermitianSpace (d+1) => (2:ℝ) • trueCoordinate truth x) 0 by fun_prop)
  simp only [map_zero,smul_zero] at hh
  have he (n : ℕ) (path : AdaptiveInfinitePath (PVMPilotAdaptive.PVMOutcome d)) :
      (2:ℝ) • trueCoordinate truth
        (Real.sqrt ((n+1:ℕ):ℝ) • projectorError truth ridge hr batchSize (n+1) path-
          ((d+1:ℝ)/Real.sqrt ((n+1:ℕ):ℝ)) • tangentProjector truth (scoreSum truth batchSize (n+1) path)) =
      Real.sqrt ((n+1:ℕ):ℝ) • trueFrameCoordinates truth (actualEstimatedState ridge hr batchSize path (n+1))-
        fullScore truth batchSize (n+1) path := by
    rw [trueCoordinates_actual,fullScore_eq_coordinate]
    simp only [map_sub,smul_sub,map_smul]
    module
  have hshift := hh.congr (fun n => Eventually.of_forall (fun path => he n path)) EventuallyEq.rfl
  intro ε hε
  exact (tendsto_add_atTop_iff_nat 1).mp (hshift ε hε)

/-- Pointwise optimal asymptotic covariance of the literal estimator.
No estimator consistency, covariance limit, or asymptotic linearity is
supplied as a hypothesis: all are proved from the actual Born experiment. -/
theorem optimalVariance (truth : PureVector d) (ridge : ℝ) (hr : 0 < ridge)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) (hbudget : PVMPilotSchedule.OneStepBudget) :
    TendstoInDistribution
      (fun (n : ℕ) path => Real.sqrt (n:ℝ) • trueFrameCoordinates truth (actualEstimatedState ridge hr batchSize path n))
      atTop id
      (fun _ => adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth))
      (multivariateGaussian 0 ((2:ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) := by
  exact tendstoInDistribution_of_tendstoInMeasure_sub _ _ (fullScore_clt truth batchSize hpositive)
    (corrected_coordinates_minus_score_zero truth ridge hr batchSize hpositive hbudget)
    (fun n => (corrected_coordinates_measurable truth ridge hr batchSize n).aemeasurable)

end
end QubitOracle.AdaptiveDesign.PVMPilotGLS

-/
