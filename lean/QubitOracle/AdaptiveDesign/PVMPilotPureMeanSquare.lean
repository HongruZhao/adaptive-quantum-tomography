-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMPilotMeanSquare
import QubitOracle.AdaptiveDesign.PVMPilotPreliminary

namespace QubitOracle.AdaptiveDesign.PVMPilotGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive TangentGLS
open MeasureTheory
noncomputable section
variable [PVMPilotSchedule.Schedule]
variable {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d]

lemma preliminary_square_integrable (batchSize : ℕ → ℕ) (truth : PureVector d) (n : ℕ) :
    Integrable (fun path => ‖actualPreliminaryError batchSize truth n path‖^2)
      (adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth)) := by
  apply Integrable.of_bound
    (actualStatistic_stronglyMeasurable batchSize n (fun raw _ =>
      ‖(pureParameter d (nearestVector d (toMatrix raw))).val-(pureParameter d truth).val‖^2)).aestronglyMeasurable 4
  filter_upwards [] with path
  rw [norm_pow,norm_norm]
  have hh := preliminaryError_norm_le_two (actualPreliminary batchSize path n) truth
  have hn := norm_nonneg (actualPreliminaryError batchSize truth n path)
  change ‖actualPreliminaryError batchSize truth n path‖ ≤ 2 at hh
  change ‖actualPreliminaryError batchSize truth n path‖^2 ≤ 4
  nlinarith

/-- The pure projection has the same exploration mean-square rate. -/
theorem preliminary_meanSquare (batchSize : ℕ → ℕ) (truth : PureVector d) (n : ℕ) :
    ∫ path, ‖actualPreliminaryError batchSize truth n path‖^2
      ∂adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth) ≤
      4*((2*PVMPilotAdaptive.noiseMomentConstant d+2)/
        ((min 1 (PVMPilotBorn.coercivityConstant d))^2*PVMPilotSchedule.mass n)) := by
  let μ := adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth)
  have hi := PVMPilotAdaptive.raw_error_square_integrable batchSize (pureParameter d truth) n
  calc
    _ ≤ ∫ path, 4*‖PVMPilotAdaptive.rawEstimator d batchSize path n-(pureParameter d truth).val‖^2 ∂μ := by
      apply integral_mono (preliminary_square_integrable batchSize truth n) (hi.const_mul 4)
      intro path
      have hh := actualPreliminaryError_norm_bound batchSize truth n path
      have hn := norm_nonneg (actualPreliminaryError batchSize truth n path)
      nlinarith [norm_nonneg (PVMPilotAdaptive.rawEstimator d batchSize path n-(pureParameter d truth).val)]
    _ = 4*(∫ path, ‖PVMPilotAdaptive.rawEstimator d batchSize path n-(pureParameter d truth).val‖^2 ∂μ) :=
      integral_const_mul 4 _
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (PVMPilotAdaptive.rawEstimator_meanSquare batchSize (pureParameter d truth) n)
        (show (0:ℝ)≤4 by norm_num)
      simpa only [pureParameter_norm,one_pow,mul_one] using hh

end
end QubitOracle.AdaptiveDesign.PVMPilotGLS

-/
