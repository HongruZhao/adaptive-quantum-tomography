import QubitOracle.AdaptiveDesign.PureAmplitudeChart
import QubitOracle.AdaptiveDesign.TangentGLSStrongConsistency
import QubitOracle.AdaptiveDesign.TangentGLSOptimalVariance
-- import QubitOracle.AdaptiveDesign.PVMOptimalVariance -- Section 5 disabled

/-! Actual-algorithm central limit theorems in the paper's amplitude
chart. These endpoints discharge the consistency and measurability
premises of the chart-transfer theorem for the recorded Born experiment. -/
namespace QubitOracle.AdaptiveDesign
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive
open Filter MeasureTheory ProbabilityTheory TangentGLS
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace TangentGLS
variable {d : ℕ} {O : Type} [Fintype O]
  [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]

theorem amplitude_optimalVariance
    (P : FinitePOVM (Fin (d+1)) O) (hI : GeneralPOVM.Identifying P)
    (hp : GeneralPOVM.Regular P) (hF : GeneralPOVM.FisherSymmetric P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    TendstoInDistribution
      (fun (n : ℕ) path => Real.sqrt (n:ℝ) • amplitudeCoordinates truth
        (pureParameter d (actualEstimate P hI hp regularization ridge hr hη batchSize path n)).val)
      atTop id
      (fun _ => adaptiveInfiniteTrajectoryMeasure (GeneralPOVM.adaptiveProtocol P hI regularization hr batchSize) truth)
      (multivariateGaussian 0 ((2:ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) := by
  apply amplitude_clt_of_projector_clt truth
  · intro n
    exact FiniteHistoryStatistics.actualStatistic_stronglyMeasurable P hI regularization hr batchSize n
      (fun raw data => (pureParameter d
        (estimateFromRaw raw data (referenceFloor P) ridge (referenceFloor_pos P hp) hη)).val)
  · exact corrected_stronglyConsistent P hI hp truth regularization ridge hr hη batchSize
  · have hh := optimalVariance P hI hp hF truth regularization ridge hr hη batchSize hpositive
    unfold OptimalVarianceStatement at hh
    simpa only [trueFrameCoordinates_actual, actualProjectorError] using hh

theorem phasePair_amplitude_optimalVariance
    (P : FinitePOVM (Fin (d+1)) O) (hI : GeneralPOVM.Identifying P)
    (hp : GeneralPOVM.Regular P) (hR : PhasePair.RankOne P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    TendstoInDistribution
      (fun (n : ℕ) path => Real.sqrt (n:ℝ) • amplitudeCoordinates truth
        (pureParameter d (actualEstimate (PhasePair.paired P) (PhasePair.paired_identifying P hI)
          (PhasePair.paired_regular P hp) regularization ridge hr hη batchSize path n)).val)
      atTop id
      (fun _ => adaptiveInfiniteTrajectoryMeasure
        (GeneralPOVM.adaptiveProtocol (PhasePair.paired P) (PhasePair.paired_identifying P hI)
          regularization hr batchSize) truth)
      (multivariateGaussian 0 ((2:ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) :=
  amplitude_optimalVariance (PhasePair.paired P) (PhasePair.paired_identifying P hI)
    (PhasePair.paired_regular P hp) (PhasePair.paired_fisher_of_rankOne P hp hR)
    truth regularization ridge hr hη batchSize hpositive
end TangentGLS

-- Section 5 proof route commented at the user request, 5 October 2026.
/-
namespace PVMPilotGLS
variable [PVMPilotSchedule.Schedule]
variable {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d]

theorem amplitude_optimalVariance (truth : PureVector d) (ridge : ℝ) (hr : 0 < ridge)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) (hbudget : PVMPilotSchedule.OneStepBudget) :
    TendstoInDistribution
      (fun (n : ℕ) path => Real.sqrt (n:ℝ) • amplitudeCoordinates truth
        (pureParameter d (actualEstimate ridge hr batchSize path n)).val)
      atTop id
      (fun _ => adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth))
      (multivariateGaussian 0 ((2:ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) := by
  apply amplitude_clt_of_projector_clt truth
  · intro n
    exact actualStatistic_stronglyMeasurable batchSize n
      (fun raw data => (pureParameter d
        (estimateFromRaw raw data (floor d) ridge (floor_pos d) hr)).val)
  · exact corrected_consistent truth ridge hr batchSize hpositive
  · have hh := optimalVariance truth ridge hr batchSize hpositive hbudget
    simpa only [trueCoordinates_actual, projectorError] using hh
end PVMPilotGLS
-/


end
end QubitOracle.AdaptiveDesign
