import QubitOracle.AdaptiveDesign.AdaptiveRidgeConsistency
import QubitOracle.AdaptiveDesign.BoundedResponseQuarterRate
import QubitOracle.AdaptiveDesign.FiniteDimensionalResponseRates
import QubitOracle.AdaptiveDesign.GeneralPOVMAdaptive
import QubitOracle.AdaptiveDesign.GeneralPOVMModel
import QubitOracle.AdaptiveDesign.GeneralPOVMQuarterRate
import QubitOracle.AdaptiveDesign.GlobalPFSICBornModel
import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel
import QubitOracle.AdaptiveDesign.P2AdaptiveTheorem
import QubitOracle.AdaptiveDesign.ProbabilityCalculus
import QubitOracle.AdaptiveDesign.ProbabilityZeroAlgebra
import QubitOracle.AdaptiveDesign.PureMatrixController
import QubitOracle.AdaptiveDesign.TangentGLSAmbient
import QubitOracle.AdaptiveDesign.TangentGLSBounds
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.AdaptiveTrajectoryExperiment
import QubitOracle.Paper.PureStateFoundations
/-! Actual preliminary and ambient response rates under the Born path law. -/

namespace QubitOracle.AdaptiveDesign.TangentGLS

open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController
open Filter MeasureTheory ProbabilityTheory
open AdaptiveRidgeConsistency BoundedResponseQuarterRate ProbabilityCalculus
open scoped BigOperators InnerProductSpace ComplexOrder Topology Matrix.Norms.Frobenius
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {d : ℕ} {O : Type} [Fintype O]
  [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]

def actualPreliminary (P : FinitePOVM (Fin (d+1)) O) (hI : GeneralPOVM.Identifying P)
    (regularization : ℝ) (hr : 0 < regularization) (batchSize : ℕ → ℕ)
    (path : AdaptiveInfinitePath O) (n : ℕ) : PureVector d :=
  nearestVector d (toMatrix (GeneralPOVM.rawEstimator P hI regularization hr batchSize path n))

def actualPreliminaryError (P : FinitePOVM (Fin (d+1)) O) (hI : GeneralPOVM.Identifying P)
    (regularization : ℝ) (hr : 0 < regularization) (batchSize : ℕ → ℕ) (truth : PureVector d)
    (n : ℕ) (path : AdaptiveInfinitePath O) : HermitianSpace (d+1) :=
  (P2Adaptive.pureParameter d (actualPreliminary P hI regularization hr batchSize path n)).val -
    (P2Adaptive.pureParameter d truth).val

theorem actualPreliminaryError_norm_bound
    (P : FinitePOVM (Fin (d+1)) O) (hI : GeneralPOVM.Identifying P)
    (regularization : ℝ) (hr : 0 < regularization) (batchSize : ℕ → ℕ) (truth : PureVector d)
    (n : ℕ) (path : AdaptiveInfinitePath O) :
    ‖actualPreliminaryError P hI regularization hr batchSize truth n path‖ ≤
      2 * ‖GeneralPOVM.rawEstimator P hI regularization hr batchSize path n -
        (P2Adaptive.pureParameter d truth).val‖ := by
  have hb := projectedMatrix_error_le_two d truth
    (toMatrix (GeneralPOVM.rawEstimator P hI regularization hr batchSize path n))
  have h1 := toMatrix_norm (actualPreliminaryError P hI regularization hr batchSize truth n path)
  have h2 := toMatrix_norm (GeneralPOVM.rawEstimator P hI regularization hr batchSize path n -
    (P2Adaptive.pureParameter d truth).val)
  change ‖projectedMatrix d (toMatrix (GeneralPOVM.rawEstimator P hI regularization hr batchSize path n)) -
    rankOneDensity truth.val‖ = _ at h1
  change ‖toMatrix (GeneralPOVM.rawEstimator P hI regularization hr batchSize path n) -
    rankOneDensity truth.val‖ = _ at h2
  rw [h1,h2] at hb
  exact hb

theorem actualPreliminaryError_consistent
    (P : FinitePOVM (Fin (d+1)) O) (hI : GeneralPOVM.Identifying P)
    (regularization : ℝ) (hr : 0 < regularization) (batchSize : ℕ → ℕ) (truth : PureVector d) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure
      (GeneralPOVM.adaptiveProtocol P hI regularization hr batchSize) truth,
      Tendsto (fun n => actualPreliminaryError P hI regularization hr batchSize truth n path) atTop (𝓝 0) := by
  filter_upwards [GeneralPOVM.rawEstimator_consistent P hI regularization hr batchSize truth] with path hp
  have hnorm : Tendsto (fun n => 2 * ‖GeneralPOVM.rawEstimator P hI regularization hr batchSize path n -
      (P2Adaptive.pureParameter d truth).val‖) atTop (𝓝 0) := by
    simpa using (hp.sub_const (P2Adaptive.pureParameter d truth).val).norm.const_mul 2
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun n => actualPreliminaryError_norm_bound P hI regularization hr batchSize truth n path) hnorm

theorem actualPreliminaryError_quarterRate
    (P : FinitePOVM (Fin (d+1)) O) (hI : GeneralPOVM.Identifying P)
    (regularization : ℝ) (hr : 0 < regularization) (batchSize : ℕ → ℕ) (truth : PureVector d) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure
      (GeneralPOVM.adaptiveProtocol P hI regularization hr batchSize) truth)
      (fun n path => quarterScale n • actualPreliminaryError P hI regularization hr batchSize truth (n+1) path)
      atTop (fun _ => 0) := by
  apply ProbabilityZeroAlgebra.dominated
    (GeneralPOVMQuarterRate.rawEstimator_quarterRate P hI regularization hr batchSize truth)
    2 (by norm_num)
  intro n path
  rw [norm_smul, norm_smul]
  have hb := projectedMatrix_error_le_two d truth
    (toMatrix (GeneralPOVM.rawEstimator P hI regularization hr batchSize path (n+1)))
  have h1 : ‖actualPreliminaryError P hI regularization hr batchSize truth (n+1) path‖ =
      ‖projectedMatrix d (toMatrix (GeneralPOVM.rawEstimator P hI regularization hr batchSize path (n+1))) -
        rankOneDensity truth.val‖ := (toMatrix_norm
          (actualPreliminaryError P hI regularization hr batchSize truth (n+1) path)).symm
  rw [h1]
  have h2 : ‖toMatrix (GeneralPOVM.rawEstimator P hI regularization hr batchSize path (n+1)) -
      rankOneDensity truth.val‖ =
    ‖GeneralPOVM.rawEstimator P hI regularization hr batchSize path (n+1) -
      (P2Adaptive.pureParameter d truth).val‖ := toMatrix_norm
        (GeneralPOVM.rawEstimator P hI regularization hr batchSize path (n+1) -
          (P2Adaptive.pureParameter d truth).val)
  rw [h2] at hb
  nlinarith [norm_nonneg (quarterScale n)]

/-- The squared preliminary error is negligible at the root-n scale. -/
theorem actualPreliminaryError_square_rootRate
    (P : FinitePOVM (Fin (d+1)) O) (hI : GeneralPOVM.Identifying P)
    (regularization : ℝ) (hr : 0 < regularization) (batchSize : ℕ → ℕ) (truth : PureVector d) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure
      (GeneralPOVM.adaptiveProtocol P hI regularization hr batchSize) truth)
      (fun n path => Real.sqrt ((n+1 : ℕ) : ℝ) *
        ‖actualPreliminaryError P hI regularization hr batchSize truth (n+1) path‖^2)
      atTop (fun _ => 0) := by
  have hq := square_norm_zero (actualPreliminaryError_quarterRate P hI regularization hr batchSize truth)
  simpa only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, quarterScale_sq] using hq

theorem actual_ambientScore_rootTight
    (P : FinitePOVM (Fin (d+1)) O) (hI : GeneralPOVM.Identifying P)
    (truth : PureVector d) (floor : ℝ) (hf : 0 < floor)
    (regularization : ℝ) (hr : 0 < regularization) (batchSize : ℕ → ℕ) :
    TightNorm (adaptiveInfiniteTrajectoryMeasure
      (GeneralPOVM.adaptiveProtocol P hI regularization hr batchSize) truth)
      (fun n path => (Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹ • ∑ k ∈ Finset.range (n+1),
        actualVectorResponse (GeneralPOVM.adaptiveProtocol P hI regularization hr batchSize)
          (ambientScoreResponse P truth floor) k path) atTop := by
  apply FiniteDimensionalResponseRates.actualResponse_rootTight_normed _ _ _
    (ambientScoreResponse_mean P truth floor) (2*(floor⁻¹*GeneralPOVM.responseBound P))
    (by have hb := GeneralPOVM.responseBound_nonnegative P; positivity)
    (ambientScoreResponse_bound P truth floor hf)

theorem actual_ambientDerivative_quarterRate
    (P : FinitePOVM (Fin (d+1)) O) (hI : GeneralPOVM.Identifying P)
    (truth : PureVector d) (floor : ℝ) (hf : 0 < floor)
    (regularization : ℝ) (hr : 0 < regularization) (batchSize : ℕ → ℕ) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure
      (GeneralPOVM.adaptiveProtocol P hI regularization hr batchSize) truth)
      (fun n path => (quarterScale n / ((n+1 : ℕ) : ℝ)) • ∑ k ∈ Finset.range (n+1),
        actualVectorResponse (GeneralPOVM.adaptiveProtocol P hI regularization hr batchSize)
          (ambientDerivativeResponse P truth floor) k path) atTop (fun _ => 0) := by
  apply FiniteDimensionalResponseRates.actualResponse_quarterRate_normed _ _ _
    (ambientDerivativeResponse_mean P truth floor) (2*((floor^2)⁻¹*(GeneralPOVM.responseBound P)^2))
    (by positivity) (ambientDerivativeResponse_bound P truth floor hf)

end
end QubitOracle.AdaptiveDesign.TangentGLS
