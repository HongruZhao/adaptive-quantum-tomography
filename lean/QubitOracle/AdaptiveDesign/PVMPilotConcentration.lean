-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.AdaptiveBudgetVectorConcentration
import QubitOracle.AdaptiveDesign.PVMPilotHigherMoments

/-! Exponential localization of the actual exploration-only preliminary
estimator for an arbitrary fixed identifying projective library. -/
namespace QubitOracle.AdaptiveDesign.PVMPilotConcentration
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian GlobalPFSICBorn PureMatrixController P2Adaptive
open MeasureTheory ProbabilityTheory PVMPilotSchedule PVMGeometry TangentGLS
open PVMPilotAdaptive PVMPilotGLS
open scoped BigOperators Topology InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable [PVMPilotSchedule.Schedule]
variable {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d]

theorem noise (batchSize : ℕ → ℕ) (theta : PhysicalParameter (d+1)) (δ : ℝ) (hδ : 0 < δ) :
    ∃ B c : ℝ, 0 < B ∧ 0 < c ∧ ∀ n,
      (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol d batchSize) theta).real
        {path | δ*mass (n+1) ≤ ‖pilotNoise batchSize theta (n+1) path‖} ≤
      B*Real.exp (-c*mass (n+1)) := by
  exact AdaptiveBudgetConcentration.vector (adaptiveProtocol d batchSize) theta (fun _ _ => rfl)
    (PVMPilotRegression.noise theta) (PVMPilotRegression.noise_mean theta)
    (2*basisBound d) (by have h := basisBound_nonnegative d; positivity)
    (PVMPilotRegression.noise_bound theta) epsilon epsilon_nonnegative
    ((basisBound d)^2) (sq_nonneg _) (fun u a => by
      change (∫ y, ⟪u,PVMPilotRegression.noise theta a y⟫_ℝ^2 ∂PVMPilotBorn.bornKernel theta a) ≤ _
      simpa only [mul_pow,mul_assoc] using PVMPilotRegression.noise_secondMoment theta a u) δ hδ

theorem preliminary (batchSize : ℕ → ℕ) (truth : PureVector d) (δ : ℝ) (hδ : 0 < δ) :
    ∃ B c : ℝ, 0 < B ∧ 0 < c ∧ ∀ n,
      (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol d batchSize) (pureParameter d truth)).real
        {path | δ ≤ ‖actualPreliminaryError batchSize truth (n+1) path‖} ≤
      B*Real.exp (-c*mass (n+1)) := by
  let μ := adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol d batchSize) (pureParameter d truth)
  let κ := min 1 (PVMPilotBorn.coercivityConstant d)
  have hκ : 0 < κ := lt_min zero_lt_one (PVMPilotBorn.coercivityConstant_pos d)
  obtain ⟨B,c,hB,hc,htail⟩ := noise batchSize (pureParameter d truth) (κ*δ/4) (by positivity)
  let T := 4/(κ*δ)
  refine ⟨B+Real.exp (c*T),c,add_pos hB (Real.exp_pos _),hc,fun n => ?_⟩
  by_cases hM : T ≤ mass (n+1)
  · have hsub : {path | δ ≤ ‖actualPreliminaryError batchSize truth (n+1) path‖} ⊆
        {path | (κ*δ/4)*mass (n+1) ≤ ‖pilotNoise batchSize (pureParameter d truth) (n+1) path‖} := by
      intro path hp
      have hpure := actualPreliminaryError_norm_bound batchSize truth (n+1) path
      have hraw := raw_error_bound batchSize (pureParameter d truth) (n+1) path
      have hn := norm_sub_le (pilotNoise batchSize (pureParameter d truth) (n+1) path)
        (pureParameter d truth).val
      rw [pureParameter_norm] at hn
      have hden : 0 < κ*mass (n+1) := mul_pos hκ (mass_pos _)
      have he : δ ≤ 2*((‖pilotNoise batchSize (pureParameter d truth) (n+1) path‖+1)/(κ*mass (n+1))) := by
        calc
          _ ≤ ‖actualPreliminaryError batchSize truth (n+1) path‖ := hp
          _ ≤ _ := hpure
          _ ≤ 2*(‖pilotNoise batchSize (pureParameter d truth) (n+1) path-(pureParameter d truth).val‖ /
              (κ*mass (n+1))) := mul_le_mul_of_nonneg_left hraw (by norm_num)
          _ ≤ _ := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hn hden.le) (by norm_num)
      have he' : δ*(κ*mass (n+1)) ≤ 2*(‖pilotNoise batchSize (pureParameter d truth) (n+1) path‖+1) := by
        apply (le_div_iff₀ hden).mp
        simpa only [mul_div_assoc] using he
      have hM' : 4 ≤ κ*δ*mass (n+1) := by
        have hh := (div_le_iff₀ (mul_pos hκ hδ)).mp hM
        nlinarith only [hh]
      change (κ*δ/4)*mass (n+1) ≤ _
      nlinarith only [he',hM']
    calc
      _ ≤ μ.real {path | (κ*δ/4)*mass (n+1) ≤ ‖pilotNoise batchSize (pureParameter d truth) (n+1) path‖} :=
        measureReal_mono hsub
      _ ≤ B*Real.exp (-c*mass (n+1)) := htail n
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Real.exp_pos _).le) (Real.exp_pos _).le
  · have hsmall : 1 ≤ Real.exp (c*T)*Real.exp (-c*mass (n+1)) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      nlinarith [lt_of_not_ge hM]
    calc
      _ ≤ 1 := measureReal_le_one
      _ ≤ Real.exp (c*T)*Real.exp (-c*mass (n+1)) := hsmall
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB.le) (Real.exp_pos _).le

theorem preliminary_all (batchSize : ℕ → ℕ) (truth : PureVector d) (δ : ℝ) (hδ : 0 < δ) :
    ∃ B c : ℝ, 0 < B ∧ 0 < c ∧ ∀ n,
      (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol d batchSize) (pureParameter d truth)).real
        {path | δ ≤ ‖actualPreliminaryError batchSize truth n path‖} ≤
      B*Real.exp (-c*mass n) := by
  obtain ⟨B,c,hB,hc,ht⟩ := preliminary batchSize truth δ hδ
  refine ⟨B+Real.exp c,c,add_pos hB (Real.exp_pos _),hc,fun n => ?_⟩
  cases n with
  | zero =>
    have hm : mass 0 = 1 := by simp [mass,ExplorationBudgetStrongLaw.mass]
    rw [hm,mul_one,add_mul,← Real.exp_add]
    simp only [add_neg_cancel,Real.exp_zero]
    exact measureReal_le_one.trans (le_add_of_nonneg_left (mul_nonneg hB.le (Real.exp_pos _).le))
  | succ n =>
    exact (ht n).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (Real.exp_pos _).le) (Real.exp_pos _).le)

end
end QubitOracle.AdaptiveDesign.PVMPilotConcentration

-/
