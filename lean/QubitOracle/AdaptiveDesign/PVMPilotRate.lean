-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMPilotAdaptiveTheorem

/-! The quarter-rate condition is sqrt(n)/E_n → 0, rather than n^(3/4)/E_n → 0. -/
namespace QubitOracle.AdaptiveDesign.PVMPilotSchedule
open Filter MeasureTheory ProbabilityTheory QubitOracle.Paper
open CoerciveLeastSquares AdaptiveRidgeConsistency AdaptiveBudgetMoments
open BoundedResponseQuarterRate
open scoped BigOperators Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
variable [Schedule]

lemma smaller_scale_zero (q : ℕ → ℝ) (hq0 : ∀ n, 0 ≤ q n)
    (hq : Tendsto (fun n => q n^2/mass n) atTop (𝓝 0)) :
    Tendsto (fun n => q n/mass n) atTop (𝓝 0) := by
  have hl := hq.add (tendsto_inv_atTop_zero.comp mass_tendsto)
  simp only [add_zero] at hl
  apply squeeze_zero (fun n => div_nonneg (hq0 n) (mass_pos n).le) _ hl
  intro n
  have hs : q n ≤ q n^2+1 := by nlinarith [sq_nonneg (q n-1)]
  have hh := div_le_div_of_nonneg_right hs (mass_pos n).le
  simpa only [Function.comp_def, add_div, one_div] using hh

variable {Theta Action Outcome E : Type}
  [MeasurableSpace Action] [MeasurableSpace Outcome]
  [Fintype Outcome] [MeasurableSingletonClass Outcome]
  [StandardBorelSpace Outcome] [Nonempty Outcome]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem scheduled_estimate_scaled_zero
    (kernel : Theta → Kernel (ℕ × Action) Outcome)
    (hk : ∀ theta, IsMarkovKernel (kernel theta))
    (theta : Theta) (frame : ℕ → Action → E →ₗ[ℝ] E)
    (response : ℕ → Action → Outcome → E)
    (truth : E) (controller : E → Action) (refresh : ℕ → Bool)
    (κ : ℝ) (hκ : 0 < κ) (hf0 : ∀ n a, Coercive (frame n a) 0)
    (hf : ∀ n a, Coercive (frame n a) (κ*epsilon n))
    (hm : ∀ n a, ∫ y, response n a y ∂kernel theta (n,a)=frame n a truth)
    (C : ℝ) (hb : ∀ n a y, ‖response n a y-frame n a truth‖ ≤ C)
    (V : ℝ) (hV : 0 ≤ V)
    (hv : ∀ u n a, ∫ y, ⟪u,response n a y-frame n a truth⟫_ℝ^2 ∂kernel theta (n,a)
      ≤ ‖u‖^2*V*epsilon n)
    (q : ℕ → ℝ) (hq0 : ∀ n, 0 ≤ q n)
    (hq : Tendsto (fun n => q n^2/mass n) atTop (𝓝 0)) :
    let p := ScheduledRidgeController.protocol kernel hk frame response controller refresh
      1 0 zero_lt_one le_rfl hf0
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure p theta)
      (fun n path => q n • ((ScheduledRidgeController.pathState frame response controller refresh
        1 0 zero_lt_one le_rfl hf0 path n).estimate zero_lt_one-truth)) atTop (fun _ => 0) := by
  intro p
  letI : IsMarkovKernel (kernel theta) := hk theta
  let g : (ℕ × Action) → Outcome → E := fun a y => response a.1 a.2 y-frame a.1 a.2 truth
  have hmean a : ∫ y, g a y ∂p.response theta a=0 := by
    change (∫ y, response a.1 a.2 y-frame a.1 a.2 truth ∂kernel theta a)=0
    rw [integral_sub Integrable.of_finite (integrable_const _), hm]
    simp
  have hn := scaled_vectorSum_zero p theta (fun _ _ => rfl) g hmean C
    (fun a y => hb a.1 a.2 y) epsilon epsilon_nonnegative V hV
    (fun u a => hv u a.1 a.2) q hq
  have hb' : TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure p theta)
      (fun n (_ : AdaptiveInfinitePath Outcome) => (q n/mass n) • (-truth)) atTop (fun _ => 0) := by
    apply ProbabilityZeroAlgebra.uniform_norm_bound (fun n => (q n/mass n)*‖truth‖)
      (by simpa using (smaller_scale_zero q hq0 hq).mul_const ‖truth‖)
    intro n path
    rw [norm_smul, norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (hq0 n) (mass_pos n).le)]
  have hr := ProbabilityZeroAlgebra.add hn hb'
  apply ProbabilityZeroAlgebra.dominated hr (min 1 κ)⁻¹
    (inv_pos.mpr (lt_min zero_lt_one hκ))
  intro n path
  let fr := fun k => frame k (ScheduledRidgeController.pathState frame response controller refresh
      1 0 zero_lt_one le_rfl hf0 path k).action
  let re := fun k => response k (ScheduledRidgeController.pathState frame response controller refresh
      1 0 zero_lt_one le_rfl hf0 path k).action (path k)
  have hbnd := norm_le_residual_div _ _ (mul_pos (lt_min zero_lt_one hκ) (mass_pos n))
    (gram_coercive fr κ hκ (fun k => hf k _) n) _ _
    (ridgeEstimate_errorEquation fr re truth 1 0 zero_lt_one le_rfl (fun k => hf0 k _) n)
  simp only [one_smul] at hbnd
  rw [ScheduledRidgeController.pathState_estimate_eq_ridgeEstimate,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (hq0 n)]
  calc
    _ ≤ q n * (‖(∑ k ∈ Finset.range n, innovation fr re truth k)-truth‖/(min 1 κ*mass n)) :=
      mul_le_mul_of_nonneg_left hbnd (hq0 n)
    _ = _ := by
      change q n * (‖(∑ k ∈ Finset.range n, innovation fr re truth k)-truth‖/(min 1 κ*mass n)) =
        (min 1 κ)⁻¹ * ‖(q n/mass n) • vectorSum p g n path + (q n/mass n) • (-truth)‖
      rw [← smul_add, ← sub_eq_add_neg, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (hq0 n) (mass_pos n).le)]
      change q n*(‖(∑ k ∈ Finset.range n, innovation fr re truth k)-truth‖/(min 1 κ*mass n)) =
        (min 1 κ)⁻¹*((q n/mass n)*‖(∑ k ∈ Finset.range n, innovation fr re truth k)-truth‖)
      field_simp

lemma quarter_condition (hbudget : OneStepBudget) :
    Tendsto (fun n : ℕ => (Real.sqrt (Real.sqrt (n:ℝ)))^2/mass n) atTop (𝓝 0) := by
  simp only [Real.sq_sqrt (Real.sqrt_nonneg _)]
  apply squeeze_zero (fun n => div_nonneg (Real.sqrt_nonneg _) (mass_pos n).le) _ hbudget
  intro n
  exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt (by linarith : (n:ℝ) ≤ n+1)) (mass_pos n).le

end
end QubitOracle.AdaptiveDesign.PVMPilotSchedule

namespace QubitOracle.AdaptiveDesign.PVMPilotAdaptive
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian GlobalPFSICBorn PureMatrixController P2Adaptive
open Filter MeasureTheory PVMPilotSchedule BoundedResponseQuarterRate
noncomputable section
variable [PVMPilotSchedule.Schedule]
variable (d : ℕ) [PVMGeneralGeometry.ExplorationLibrary d]

theorem rawEstimator_quarterRate (batchSize : ℕ → ℕ) (theta : PhysicalParameter (d+1))
    (hbudget : PVMPilotSchedule.OneStepBudget) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol d batchSize) theta)
      (fun n path => quarterScale n • (rawEstimator d batchSize path (n+1)-theta.1))
      atTop (fun _ => (0 : HermitianSpace (d+1))) := by
  have h := PVMPilotSchedule.scheduled_estimate_scaled_zero PVMPilotBorn.bornKernel
    PVMPilotBorn.bornKernel_isMarkov theta PVMPilotRegression.frame (fun _ => PVMPilotRegression.response)
    theta.1 (physicalController d) (SequentialRidgeController.batchRefresh batchSize)
    (PVMPilotBorn.coercivityConstant d) (PVMPilotBorn.coercivityConstant_pos d)
    PVMPilotRegression.frame_nonnegative PVMPilotRegression.frame_coercive
    (fun n a => PVMPilotRegression.response_mean theta (n,a)) (2*PVMGeometry.basisBound d)
    (fun n a y => PVMPilotRegression.noise_bound theta (n,a) y)
    ((PVMGeometry.basisBound d)^2) (sq_nonneg _)
    (fun u n a => by simpa only [PVMPilotRegression.noise, mul_pow, mul_assoc] using
      PVMPilotRegression.noise_secondMoment theta (n,a) u)
    (fun n => Real.sqrt (Real.sqrt (n:ℝ))) (fun _ => Real.sqrt_nonneg _)
    (quarter_condition hbudget)
  exact h.comp (tendsto_add_atTop_nat 1)

end
end QubitOracle.AdaptiveDesign.PVMPilotAdaptive

-/
