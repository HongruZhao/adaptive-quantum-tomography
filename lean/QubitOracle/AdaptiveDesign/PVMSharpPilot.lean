-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMSharpMoments
import QubitOracle.AdaptiveDesign.AdaptiveExactMoments
import QubitOracle.AdaptiveDesign.PVMPilotMeanSquare

/-! Coefficient-one finite-sample exploration bounds for the actual
adaptive ridge pilot. The complete copy sequence, including copy zero,
is governed by the protocol's Ionescu--Tulcea law. -/
namespace QubitOracle.AdaptiveDesign.PVMSharpPilot
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian GlobalPFSICBorn
open PVMGeometry PVMGeneralGeometry PVMPilotBorn PVMPilotSchedule PVMPilotRegression
open PVMPilotAdaptive AdaptiveBudgetMoments CoerciveLeastSquares
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable [PVMPilotSchedule.Schedule] {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d]

def budget (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, epsilon k
lemma budget_nonnegative (n : ℕ) : 0≤budget n :=
  Finset.sum_nonneg (fun k _ => epsilon_nonnegative k)

theorem gram_coercive (U : ℕ → Action d) (n : ℕ) :
    Coercive (ridgeGram (fun k => frame k (U k)) 1 n)
      (1+PVMPilotBorn.coercivityConstant d*budget n) := by
  intro x
  rw [ridgeGram_apply,one_smul,inner_add_right,real_inner_self_eq_norm_sq,inner_sum]
  have h := Finset.sum_le_sum (s:=Finset.range n) (fun k _ => frame_coercive k (U k) x)
  simp only [← Finset.sum_mul,← Finset.mul_sum] at h
  dsimp [budget]
  nlinarith

theorem pilotNoise_secondMoment_sharp (batchSize : ℕ → ℕ)
    (theta : PhysicalParameter (d+1)) (n : ℕ) :
    (∫ path, ‖pilotNoise batchSize theta n path‖^2
      ∂adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol d batchSize) theta) ≤ budget n :=
  AdaptiveExactMoments.vectorSum_secondMoment_sharp
    (adaptiveProtocol d batchSize) theta (fun _ _ => rfl)
    (noise theta) (noise_mean theta) (2*basisBound d) (noise_bound theta)
    epsilon (PVMSharpMoments.noise_norm_square_le theta) n

theorem raw_error_bound_sharp (batchSize : ℕ → ℕ)
    (theta : PhysicalParameter (d+1)) (n : ℕ) (path : AdaptiveInfinitePath (PVMOutcome d)) :
    ‖rawEstimator d batchSize path n-theta.1‖ ≤
      ‖pilotNoise batchSize theta n path-theta.1‖ /
        (1+PVMPilotBorn.coercivityConstant d*budget n) := by
  let fr := fun k => frame k (actualState d batchSize path k).action
  let re := fun k => response (actualState d batchSize path k).action (path k)
  have hc : 0<1+PVMPilotBorn.coercivityConstant d*budget n :=
    by have hκ := PVMPilotBorn.coercivityConstant_pos d; have hE := budget_nonnegative n; positivity
  have h := norm_le_residual_div _ _ hc
    (gram_coercive (fun k => (actualState d batchSize path k).action) n)
    _ _ (ridgeEstimate_errorEquation fr re theta.1 1 0 zero_lt_one le_rfl
      (fun k => frame_nonnegative k _) n)
  simp only [one_smul] at h
  unfold rawEstimator actualState
  rw [ScheduledRidgeController.pathState_estimate_eq_ridgeEstimate]
  exact h

theorem rawEstimator_meanSquare_sharp (batchSize : ℕ → ℕ)
    (theta : PhysicalParameter (d+1)) (n : ℕ) :
    (∫ path, ‖rawEstimator d batchSize path n-theta.1‖^2
      ∂adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol d batchSize) theta) ≤
      (budget n+‖theta.1‖^2)/(1+PVMPilotBorn.coercivityConstant d*budget n)^2 := by
  let μ := adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol d batchSize) theta
  have hshift := AdaptiveExactMoments.vectorSum_shift_secondMoment
    (adaptiveProtocol d batchSize) theta (noise theta) (noise_mean theta)
    (2*basisBound d) (noise_bound theta) n theta.1
  change (∫ path, ‖pilotNoise batchSize theta n path-theta.1‖^2 ∂μ)=
    (∫ path, ‖pilotNoise batchSize theta n path‖^2 ∂μ)+‖theta.1‖^2 at hshift
  have hs : Integrable (fun path => ‖pilotNoise batchSize theta n path-theta.1‖^2) μ := by
    have hsq := vectorSum_square_integrable (adaptiveProtocol d batchSize) theta
      (noise theta) (2*basisBound d) (noise_bound theta) n
    have hi : Integrable (fun path => ⟪theta.1,pilotNoise batchSize theta n path⟫_ℝ) μ := by
      simp only [pilotNoise,vectorSum,inner_sum]
      apply integrable_finset_sum
      intro k hk
      exact AdaptiveResponseStrongLaw.actualResponse_integrable
        (adaptiveProtocol d batchSize) theta _ (‖theta.1‖*(2*basisBound d))
        (fun a y => (norm_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left (noise_bound theta a y) (norm_nonneg _))) k
    simp only [norm_sub_sq_real]
    simp_rw [show ∀ x : HermitianSpace (d+1), ⟪x,theta.1⟫_ℝ=⟪theta.1,x⟫_ℝ
      from fun x => (real_inner_comm x theta.1).symm]
    exact (hsq.sub (hi.const_mul 2)).add (integrable_const _)
  calc
    _ ≤ ∫ path, ‖pilotNoise batchSize theta n path-theta.1‖^2 /
        (1+PVMPilotBorn.coercivityConstant d*budget n)^2 ∂μ := by
      apply integral_mono (raw_error_square_integrable batchSize theta n) (hs.div_const _)
      intro path
      simpa only [div_pow] using pow_le_pow_left₀ (norm_nonneg _)
        (raw_error_bound_sharp batchSize theta n path) 2
    _ = ((∫ path, ‖pilotNoise batchSize theta n path‖^2 ∂μ)+‖theta.1‖^2)/
        (1+PVMPilotBorn.coercivityConstant d*budget n)^2 := by rw [integral_div,hshift]
    _ ≤ _ := div_le_div_of_nonneg_right
      (add_le_add (pilotNoise_secondMoment_sharp batchSize theta n) le_rfl) (sq_nonneg _)

theorem pure_rawEstimator_meanSquare (batchSize : ℕ → ℕ)
    (truth : PureMatrixController.PureVector d) (n : ℕ) :
    (∫ path, ‖rawEstimator d batchSize path n-(P2Adaptive.pureParameter d truth).val‖^2
      ∂adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol d batchSize) (P2Adaptive.pureParameter d truth)) ≤
      (1+budget n)/(1+PVMPilotBorn.coercivityConstant d*budget n)^2 := by
  have h := rawEstimator_meanSquare_sharp batchSize (P2Adaptive.pureParameter d truth) n
  simpa [TangentGLS.pureParameter_norm,add_comm] using h

end
end QubitOracle.AdaptiveDesign.PVMSharpPilot

-/
