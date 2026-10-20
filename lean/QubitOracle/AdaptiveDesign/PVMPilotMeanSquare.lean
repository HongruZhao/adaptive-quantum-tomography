-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMPilotMeasurability

/-! An explicit mean-square bound, hence the E_n^(-1/2) preliminary rate. -/
namespace QubitOracle.AdaptiveDesign.PVMPilotAdaptive
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian GlobalPFSICBorn PureMatrixController
open Filter MeasureTheory ProbabilityTheory CoerciveLeastSquares AdaptiveBudgetMoments
open PVMPilotSchedule PVMGeometry
open scoped BigOperators Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
variable [PVMPilotSchedule.Schedule]
variable {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d]

def pilotNoise (batchSize : ℕ → ℕ) (theta : PhysicalParameter (d+1))
    (n : ℕ) (path : AdaptiveInfinitePath (PVMOutcome d)) : HermitianSpace (d+1) :=
  vectorSum (adaptiveProtocol d batchSize) (PVMPilotRegression.noise theta) n path

lemma pilotNoise_bound (batchSize : ℕ → ℕ) (theta : PhysicalParameter (d+1))
    (n : ℕ) (path : AdaptiveInfinitePath (PVMOutcome d)) :
    ‖pilotNoise batchSize theta n path‖ ≤ n*(2*basisBound d) := by
  unfold pilotNoise vectorSum
  apply (norm_sum_le _ _).trans
  have h := Finset.sum_le_sum (s:=Finset.range n) (fun k _ =>
    PVMPilotRegression.noise_bound theta
      ((adaptiveProtocol d batchSize).design k (adaptiveInfinitePathPrefix k path)) (path k))
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    AdaptiveRidgeConsistency.actualVectorResponse] using h

lemma raw_error_bound (batchSize : ℕ → ℕ) (theta : PhysicalParameter (d+1))
    (n : ℕ) (path : AdaptiveInfinitePath (PVMOutcome d)) :
    ‖rawEstimator d batchSize path n-theta.1‖ ≤
      ‖pilotNoise batchSize theta n path-theta.1‖ /
        (min 1 (PVMPilotBorn.coercivityConstant d)*mass n) := by
  let fr := fun k => PVMPilotRegression.frame k (actualState d batchSize path k).action
  let re := fun k => PVMPilotRegression.response (actualState d batchSize path k).action (path k)
  have hκ := PVMPilotBorn.coercivityConstant_pos d
  have hb := norm_le_residual_div _ _ (mul_pos (lt_min zero_lt_one hκ) (mass_pos n))
    (PVMPilotSchedule.gram_coercive fr _ hκ (fun k => PVMPilotRegression.frame_coercive k _) n)
    _ _ (ridgeEstimate_errorEquation fr re theta.1 1 0 zero_lt_one le_rfl
      (fun k => PVMPilotRegression.frame_nonnegative k _) n)
  simp only [one_smul] at hb
  unfold rawEstimator actualState
  rw [ScheduledRidgeController.pathState_estimate_eq_ridgeEstimate]
  exact hb

lemma raw_error_square_le (batchSize : ℕ → ℕ) (theta : PhysicalParameter (d+1))
    (n : ℕ) (path : AdaptiveInfinitePath (PVMOutcome d)) :
    ‖rawEstimator d batchSize path n-theta.1‖^2 ≤
      (2*‖pilotNoise batchSize theta n path‖^2+2*‖theta.1‖^2)/
      ((min 1 (PVMPilotBorn.coercivityConstant d))^2*mass n^2) := by
  have h := raw_error_bound batchSize theta n path
  have hm : 0 < min 1 (PVMPilotBorn.coercivityConstant d)*mass n :=
    mul_pos (lt_min zero_lt_one (PVMPilotBorn.coercivityConstant_pos d)) (mass_pos n)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [div_pow, mul_pow] at hsq
  apply hsq.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  have ht := norm_sub_le (pilotNoise batchSize theta n path) theta.1
  nlinarith [norm_nonneg (pilotNoise batchSize theta n path-theta.1),
    norm_nonneg (pilotNoise batchSize theta n path), norm_nonneg theta.1,
    sq_nonneg (‖pilotNoise batchSize theta n path‖-‖theta.1‖)]

lemma raw_error_square_integrable (batchSize : ℕ → ℕ) (theta : PhysicalParameter (d+1)) (n : ℕ) :
    Integrable (fun path => ‖rawEstimator d batchSize path n-theta.1‖^2)
      (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol d batchSize) theta) := by
  have hm := mul_pos (lt_min zero_lt_one (PVMPilotBorn.coercivityConstant_pos d)) (mass_pos n)
  apply Integrable.of_bound
    (PVMPilotGLS.actualStatistic_stronglyMeasurable batchSize n
      (fun raw _ => ‖raw-theta.1‖^2)).aestronglyMeasurable
    (((n*(2*basisBound d)+‖theta.1‖)/(min 1 (PVMPilotBorn.coercivityConstant d)*mass n))^2)
  filter_upwards [] with path
  change ‖‖rawEstimator d batchSize path n-theta.1‖^2‖ ≤ _
  rw [norm_pow, norm_norm]
  apply pow_le_pow_left₀ (norm_nonneg _)
  apply (raw_error_bound batchSize theta n path).trans
  apply div_le_div_of_nonneg_right _ hm.le
  exact (norm_sub_le _ _).trans (add_le_add (pilotNoise_bound batchSize theta n path) (le_refl _))

def noiseMomentConstant (d : ℕ) : ℝ :=
  (Module.finrank ℝ (HermitianSpace (d+1)))*(2*(basisBound d)^2+2*(2*basisBound d)^2)

lemma pilotNoise_secondMoment (batchSize : ℕ → ℕ) (theta : PhysicalParameter (d+1)) (n : ℕ) :
    ∫ path, ‖pilotNoise batchSize theta n path‖^2
      ∂adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol d batchSize) theta ≤ noiseMomentConstant d*mass n := by
  exact vectorSum_secondMoment (adaptiveProtocol d batchSize) theta (fun _ _ => rfl)
    (PVMPilotRegression.noise theta) (PVMPilotRegression.noise_mean theta)
    (2*basisBound d) (PVMPilotRegression.noise_bound theta)
    epsilon epsilon_nonnegative ((basisBound d)^2) (sq_nonneg _)
    (fun u a => by
      change (∫ y, ⟪u,PVMPilotRegression.noise theta a y⟫_ℝ^2 ∂PVMPilotBorn.bornKernel theta a) ≤ _
      simpa only [mul_pow,mul_assoc] using PVMPilotRegression.noise_secondMoment theta a u) n

/-- Quantitative preliminary theorem for the actual estimator, not a supplied rate. -/
theorem rawEstimator_meanSquare (batchSize : ℕ → ℕ) (theta : PhysicalParameter (d+1)) (n : ℕ) :
    ∫ path, ‖rawEstimator d batchSize path n-theta.1‖^2
      ∂adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol d batchSize) theta ≤
      (2*noiseMomentConstant d+2*‖theta.1‖^2)/
        ((min 1 (PVMPilotBorn.coercivityConstant d))^2*mass n) := by
  let μ := adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol d batchSize) theta
  have hi := vectorSum_square_integrable (adaptiveProtocol d batchSize) theta
    (PVMPilotRegression.noise theta) (2*basisBound d) (PVMPilotRegression.noise_bound theta) n
  change Integrable (fun path => ‖pilotNoise batchSize theta n path‖^2) μ at hi
  have hm := mass_pos n
  have hc := lt_min zero_lt_one (PVMPilotBorn.coercivityConstant_pos d)
  calc
    _ ≤ ∫ path, (2*‖pilotNoise batchSize theta n path‖^2+2*‖theta.1‖^2)/
        ((min 1 (PVMPilotBorn.coercivityConstant d))^2*mass n^2) ∂μ := by
      apply integral_mono (raw_error_square_integrable batchSize theta n)
        (((hi.const_mul 2).add (integrable_const _)).div_const _)
      intro path
      exact raw_error_square_le batchSize theta n path
    _ = (2*(∫ path, ‖pilotNoise batchSize theta n path‖^2 ∂μ)+2*‖theta.1‖^2)/
        ((min 1 (PVMPilotBorn.coercivityConstant d))^2*mass n^2) := by
      rw [integral_div, integral_add (hi.const_mul 2) (integrable_const _), integral_const_mul]
      simp [μ]
    _ ≤ (2*noiseMomentConstant d*mass n+2*‖theta.1‖^2*mass n)/
        ((min 1 (PVMPilotBorn.coercivityConstant d))^2*mass n^2) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hn := pilotNoise_secondMoment batchSize theta n
      have h1 := mul_le_mul_of_nonneg_left (mass_ge_one n) (sq_nonneg ‖theta.1‖)
      nlinarith
    _ = _ := by field_simp

end
end QubitOracle.AdaptiveDesign.PVMPilotAdaptive

-/
