-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMEstimatorFourthMoment
import QubitOracle.AdaptiveDesign.PurePOVMMeanLoss

/-! Corollary 5.6, exploration-PVM branch: expected physical losses for
the implemented estimator, without an assumed estimator moment bound. -/
namespace QubitOracle.AdaptiveDesign.PurePVMMeanLoss
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive
open TangentGLS PVMPilotGLS Filter MeasureTheory PVMPilotSchedule
open PureMultilevelLossConstants PureMultilevelDeterministicGeometry
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
variable [PVMPilotSchedule.Schedule]
variable {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d]

theorem pvm (truth : PureVector d) (ridge : ℝ) (hr : 0 < ridge)
    (batchSize : ℕ → ℕ) (hp : ∀ j, 0 < batchSize j)
    (hbudget : OneStepBudget) (hbatch : BatchMomentCondition batchSize) :
    let μ := adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth)
    Tendsto (fun n : ℕ => (n:ℝ)*∫ path, ‖projectorError truth ridge hr batchSize n path‖^2 ∂μ)
      atTop (𝓝 (2*(d:ℝ))) ∧
    Tendsto (fun n : ℕ => (n:ℝ)*∫ path,
      pureMultilevelBuresSq truth.val (PVMPilotGLS.actualEstimate ridge hr batchSize path n).val ∂μ)
      atTop (𝓝 (d:ℝ)) := by
  apply PurePOVMMeanLoss.both_mean_losses truth
    (fun n path => PVMPilotGLS.actualEstimate ridge hr batchSize path n)
  · intro n
    exact PVMPilotGLS.actualStatistic_stronglyMeasurable batchSize n (fun raw data =>
      (pureParameter d (estimateFromRaw raw data (floor d) ridge (floor_pos d) hr)).val)
  · exact corrected_consistent truth ridge hr batchSize hp
  · exact corrected_fourthMoment truth ridge hr batchSize hp hbudget hbatch
  · exact (PureLossDistributions.pvm truth ridge hr batchSize hp hbudget).2

end
end QubitOracle.AdaptiveDesign.PurePVMMeanLoss

-/
