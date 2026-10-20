-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMGeneralGLSEstimator

namespace QubitOracle.AdaptiveDesign.PVMGeneralGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController TangentGLS
open Filter MeasureTheory ProbabilityTheory BoundedResponseQuarterRate ProbabilityCalculus
open scoped BigOperators InnerProductSpace Topology Matrix.Norms.Frobenius
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
variable [PVMExplorationSchedule.Schedule]
variable {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d]

def actualPreliminaryError (batchSize : ℕ → ℕ) (truth : PureVector d)
    (n : ℕ) (path : AdaptiveInfinitePath (PVMGeneralAdaptive.PVMOutcome d)) : HermitianSpace (d+1) :=
  (P2Adaptive.pureParameter d (actualPreliminary batchSize path n)).val -
    (P2Adaptive.pureParameter d truth).val

theorem actualPreliminaryError_norm_bound
    (batchSize : ℕ → ℕ) (truth : PureVector d)
    (n : ℕ) (path : AdaptiveInfinitePath (PVMGeneralAdaptive.PVMOutcome d)) :
    ‖actualPreliminaryError batchSize truth n path‖ ≤
      2 * ‖PVMGeneralAdaptive.rawEstimator d batchSize path n -
        (P2Adaptive.pureParameter d truth).val‖ := by
  have hb := projectedMatrix_error_le_two d truth
    (toMatrix (PVMGeneralAdaptive.rawEstimator d batchSize path n))
  have h1 := toMatrix_norm (actualPreliminaryError batchSize truth n path)
  have h2 := toMatrix_norm (PVMGeneralAdaptive.rawEstimator d batchSize path n -
    (P2Adaptive.pureParameter d truth).val)
  change ‖projectedMatrix d (toMatrix (PVMGeneralAdaptive.rawEstimator d batchSize path n)) -
    rankOneDensity truth.val‖ = _ at h1
  change ‖toMatrix (PVMGeneralAdaptive.rawEstimator d batchSize path n) -
    rankOneDensity truth.val‖ = _ at h2
  rw [h1,h2] at hb
  exact hb

theorem actualPreliminaryError_consistent
    (batchSize : ℕ → ℕ) (truth : PureVector d) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure
      (PVMGeneralAdaptive.adaptiveProtocol d batchSize) (P2Adaptive.pureParameter d truth),
      Tendsto (fun n => actualPreliminaryError batchSize truth n path) atTop (𝓝 0) := by
  filter_upwards [PVMGeneralAdaptive.rawEstimator_consistent d batchSize (P2Adaptive.pureParameter d truth)] with path hp
  have hnorm : Tendsto (fun n => 2 * ‖PVMGeneralAdaptive.rawEstimator d batchSize path n -
      (P2Adaptive.pureParameter d truth).val‖) atTop (𝓝 0) := by
    simpa using (hp.sub_const (P2Adaptive.pureParameter d truth).val).norm.const_mul 2
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun n => actualPreliminaryError_norm_bound batchSize truth n path) hnorm

theorem actualPreliminaryError_quarterRate
    (batchSize : ℕ → ℕ) (truth : PureVector d) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure
      (PVMGeneralAdaptive.adaptiveProtocol d batchSize) (P2Adaptive.pureParameter d truth))
      (fun n path => quarterScale n • actualPreliminaryError batchSize truth (n+1) path)
      atTop (fun _ => 0) := by
  apply ProbabilityZeroAlgebra.dominated
    (PVMGeneralAdaptive.rawEstimator_quarterRate d batchSize (P2Adaptive.pureParameter d truth))
    2 (by norm_num)
  intro n path
  rw [norm_smul, norm_smul]
  have hb := projectedMatrix_error_le_two d truth
    (toMatrix (PVMGeneralAdaptive.rawEstimator d batchSize path (n+1)))
  have h1 : ‖actualPreliminaryError batchSize truth (n+1) path‖ =
      ‖projectedMatrix d (toMatrix (PVMGeneralAdaptive.rawEstimator d batchSize path (n+1))) -
        rankOneDensity truth.val‖ := (toMatrix_norm
          (actualPreliminaryError batchSize truth (n+1) path)).symm
  rw [h1]
  have h2 : ‖toMatrix (PVMGeneralAdaptive.rawEstimator d batchSize path (n+1)) -
      rankOneDensity truth.val‖ =
    ‖PVMGeneralAdaptive.rawEstimator d batchSize path (n+1) -
      (P2Adaptive.pureParameter d truth).val‖ := toMatrix_norm
        (PVMGeneralAdaptive.rawEstimator d batchSize path (n+1) -
          (P2Adaptive.pureParameter d truth).val)
  rw [h2] at hb
  nlinarith [norm_nonneg (quarterScale n)]

/-- The squared preliminary error is negligible at the root-n scale. -/
theorem actualPreliminaryError_square_rootRate
    (batchSize : ℕ → ℕ) (truth : PureVector d) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure
      (PVMGeneralAdaptive.adaptiveProtocol d batchSize) (P2Adaptive.pureParameter d truth))
      (fun n path => Real.sqrt ((n+1 : ℕ) : ℝ) *
        ‖actualPreliminaryError batchSize truth (n+1) path‖^2)
      atTop (fun _ => 0) := by
  have hq := square_norm_zero (actualPreliminaryError_quarterRate batchSize truth)
  simpa only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, quarterScale_sq] using hq

end
end QubitOracle.AdaptiveDesign.PVMGeneralGLS

-/
