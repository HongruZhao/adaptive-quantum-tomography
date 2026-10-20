-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.AdaptiveBudgetHigherMoments
import QubitOracle.AdaptiveDesign.PVMPilotPureMeanSquare

/-! All fixed integer moments of the implemented exploration pilot, with
the correct square-root exploration-budget scale. -/
namespace QubitOracle.AdaptiveDesign.PVMPilotHigherMoments
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian GlobalPFSICBorn PureMatrixController P2Adaptive
open Filter MeasureTheory ProbabilityTheory PVMPilotSchedule PVMGeometry
open PVMPilotAdaptive PVMPilotGLS AdaptiveResponseMoments
open scoped BigOperators Topology InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
variable [PVMPilotSchedule.Schedule]
variable {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d]

theorem noise (batchSize : ℕ → ℕ) (theta : PhysicalParameter (d+1)) (p : ℕ) :
    UniformMoment (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol d batchSize) theta)
      (fun n path => (Real.sqrt (mass (n+1)))⁻¹ • pilotNoise batchSize theta (n+1) path) p := by
  exact AdaptiveBudgetHigherMoments.vector (adaptiveProtocol d batchSize) theta (fun _ _ => rfl)
    (PVMPilotRegression.noise theta) (PVMPilotRegression.noise_mean theta)
    (2*basisBound d) (by have h := basisBound_nonnegative d; positivity)
    (PVMPilotRegression.noise_bound theta) epsilon epsilon_nonnegative
    ((basisBound d)^2) (sq_nonneg _) (fun u a => by
      change (∫ y, ⟪u,PVMPilotRegression.noise theta a y⟫_ℝ^2 ∂PVMPilotBorn.bornKernel theta a) ≤ _
      simpa only [mul_pow,mul_assoc] using PVMPilotRegression.noise_secondMoment theta a u) p

theorem raw (batchSize : ℕ → ℕ) (theta : PhysicalParameter (d+1)) (p : ℕ) :
    UniformMoment (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol d batchSize) theta)
      (fun n path => Real.sqrt (mass (n+1)) • (rawEstimator d batchSize path (n+1)-theta.val)) p := by
  let μ := adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol d batchSize) theta
  let κ := min 1 (PVMPilotBorn.coercivityConstant d)
  have hκ : 0 < κ := lt_min zero_lt_one (PVMPilotBorn.coercivityConstant_pos d)
  have hS := noise batchSize theta p
  have hB : UniformMoment μ (fun n (_ : AdaptiveInfinitePath (PVMOutcome d)) =>
      (Real.sqrt (mass (n+1)))⁻¹ • (-theta.val)) p := by
    apply uniformMoment_of_bound _ (fun _ => aestronglyMeasurable_const) ‖theta.val‖ (norm_nonneg _)
    intro n path
    rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hsqrt : 1 ≤ Real.sqrt (mass (n+1)) := by
      rw [Real.le_sqrt (by norm_num) (mass_pos (n+1)).le]
      simpa using mass_ge_one (n+1)
    exact mul_le_of_le_one_left (norm_nonneg _) ((inv_le_one₀ (by positivity)).mpr hsqrt)
  have hSB : UniformMoment μ
      (fun n path => (Real.sqrt (mass (n+1)))⁻¹ • (pilotNoise batchSize theta (n+1) path-theta.val)) p := by
    simpa only [smul_add, smul_neg, sub_eq_add_neg] using hS.add hB
  apply hSB.of_dominated _ (fun n =>
    (actualStatistic_stronglyMeasurable batchSize (n+1)
      (fun raw _ => Real.sqrt (mass (n+1)) • (raw-theta.val))).aestronglyMeasurable)
    κ⁻¹ (inv_nonneg.mpr hκ.le)
  intro n path
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (by positivity)]
  calc
    _ ≤ Real.sqrt (mass (n+1))*(‖pilotNoise batchSize theta (n+1) path-theta.val‖/(κ*mass (n+1))) :=
      mul_le_mul_of_nonneg_left (raw_error_bound batchSize theta (n+1) path) (Real.sqrt_nonneg _)
    _ = _ := by
      have hs := Real.sq_sqrt (mass_pos (n+1)).le
      have hs0 : Real.sqrt (mass (n+1)) ≠ 0 := (Real.sqrt_pos.mpr (mass_pos (n+1))).ne'
      field_simp [(mass_pos (n+1)).ne',hκ.ne',hs0]
      rw [hs]
      ring

theorem preliminary (batchSize : ℕ → ℕ) (truth : PureVector d) (p : ℕ) :
    UniformMoment
      (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol d batchSize) (pureParameter d truth))
      (fun n path => Real.sqrt (mass (n+1)) • actualPreliminaryError batchSize truth (n+1) path) p := by
  apply (raw batchSize (pureParameter d truth) p).of_dominated _
    (fun n => (actualStatistic_stronglyMeasurable batchSize (n+1)
      (fun raw _ => Real.sqrt (mass (n+1)) •
        ((pureParameter d (nearestVector d (toMatrix raw))).val-(pureParameter d truth).val))).aestronglyMeasurable)
    2 (by norm_num)
  intro n path
  simp only [norm_smul]
  have h := mul_le_mul_of_nonneg_left (actualPreliminaryError_norm_bound batchSize truth (n+1) path)
    (norm_nonneg (Real.sqrt (mass (n+1))))
  convert h using 1 <;> first | rfl | ring

end
end QubitOracle.AdaptiveDesign.PVMPilotHigherMoments

-/
