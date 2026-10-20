-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMPilotRegression
import QubitOracle.AdaptiveDesign.AdaptiveBudgetVectorRate
import QubitOracle.AdaptiveDesign.ScheduledRidgeController

/-! Strong consistency of the exploration-only ridge fit under E_n → ∞. -/
namespace QubitOracle.AdaptiveDesign.PVMPilotSchedule
open Filter MeasureTheory ProbabilityTheory QubitOracle.Paper
open CoerciveLeastSquares AdaptiveRidgeConsistency AdaptiveBudgetMoments
open scoped BigOperators Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
variable [Schedule]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma gram_coercive (frame : ℕ → E →ₗ[ℝ] E) (κ : ℝ) (hκ : 0 < κ)
    (hf : ∀ n, Coercive (frame n) (κ * epsilon n)) (n : ℕ) :
    Coercive (ridgeGram frame 1 n) (min 1 κ * mass n) := by
  intro x
  have hsum : κ * (∑ t ∈ Finset.range n, epsilon t) * ‖x‖^2 ≤
      ∑ t ∈ Finset.range n, ⟪x,frame t x⟫_ℝ := by
    calc
      _ = ∑ t ∈ Finset.range n, κ*epsilon t*‖x‖^2 := by rw [Finset.mul_sum, Finset.sum_mul]
      _ ≤ _ := Finset.sum_le_sum (fun t _ => hf t x)
  have hc1 : min (1:ℝ) κ ≤ 1 := min_le_left _ _
  have hck : min (1:ℝ) κ ≤ κ := min_le_right _ _
  have hE := Finset.sum_nonneg (s:=Finset.range n) (fun t _ => epsilon_nonnegative t)
  have hb : min (1:ℝ) κ*mass n ≤ 1+κ*(∑ t ∈ Finset.range n, epsilon t) := by
    dsimp [mass, ExplorationBudgetStrongLaw.mass]
    nlinarith [mul_le_mul_of_nonneg_right hck hE]
  rw [ridgeGram_apply, inner_add_right, inner_smul_right, inner_sum,
    real_inner_self_eq_norm_sq, one_mul]
  nlinarith [mul_le_mul_of_nonneg_right hb (sq_nonneg ‖x‖)]

lemma ridgeEstimate_tendsto (frame : ℕ → E →ₗ[ℝ] E) (response : ℕ → E)
    (truth : E) (κ : ℝ) (hκ : 0 < κ)
    (hf0 : ∀ n, Coercive (frame n) 0)
    (hf : ∀ n, Coercive (frame n) (κ*epsilon n))
    (hnoise : Tendsto (fun n => (mass n)⁻¹ •
      ∑ t ∈ Finset.range n, innovation frame response truth t) atTop (𝓝 0)) :
    Tendsto (ridgeEstimate frame response 1 0 zero_lt_one le_rfl hf0) atTop (𝓝 truth) := by
  let c : ℝ := min 1 κ
  have hc : 0 < c := lt_min zero_lt_one hκ
  have hi := (tendsto_inv_atTop_zero.comp mass_tendsto).smul_const truth
  have hres := hnoise.sub hi
  simp only [Function.comp_def, ← smul_sub, zero_smul, sub_zero] at hres
  have hlim := hres.norm.div_const c
  simp only [norm_zero, zero_div] at hlim
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hlim
  intro n
  have hb := norm_le_residual_div _ _ (mul_pos hc (mass_pos n))
    (gram_coercive frame κ hκ hf n) _ _
    (ridgeEstimate_errorEquation frame response truth 1 0 zero_lt_one le_rfl hf0 n)
  simp only [one_smul] at hb
  apply hb.trans_eq
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (mass_pos n).le)]
  field_simp

variable {Theta Action Outcome : Type}
  [MeasurableSpace Action] [MeasurableSpace Outcome]
  [Fintype Outcome] [MeasurableSingletonClass Outcome]
  [StandardBorelSpace Outcome] [Nonempty Outcome]

/-- Every probabilistic input is a finite-action mean/variance calculation. -/
theorem scheduled_estimate_consistent
    (kernel : Theta → Kernel (ℕ × Action) Outcome)
    (hk : ∀ theta, IsMarkovKernel (kernel theta))
    (theta : Theta) (frame : ℕ → Action → E →ₗ[ℝ] E)
    (response : ℕ → Action → Outcome → E)
    (truth : E) (controller : E → Action) (refresh : ℕ → Bool)
    (κ : ℝ) (hκ : 0 < κ) (hf0 : ∀ n a, Coercive (frame n a) 0)
    (hf : ∀ n a, Coercive (frame n a) (κ*epsilon n))
    (hm : ∀ n a, ∫ y, response n a y ∂kernel theta (n,a)=frame n a truth)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n a y, ‖response n a y-frame n a truth‖ ≤ C)
    (V : ℝ) (hV : 0 ≤ V)
    (hv : ∀ u n a, ∫ y, ⟪u,response n a y-frame n a truth⟫_ℝ^2 ∂kernel theta (n,a)
      ≤ ‖u‖^2*V*epsilon n) :
    let p := ScheduledRidgeController.protocol kernel hk frame response controller refresh
      1 0 zero_lt_one le_rfl hf0
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure p theta,
      Tendsto (fun n => (ScheduledRidgeController.pathState frame response controller refresh
        1 0 zero_lt_one le_rfl hf0 path n).estimate zero_lt_one) atTop (𝓝 truth) := by
  intro p
  letI : IsMarkovKernel (kernel theta) := hk theta
  let g : (ℕ × Action) → Outcome → E := fun a y => response a.1 a.2 y-frame a.1 a.2 truth
  have hmean a : ∫ y, g a y ∂p.response theta a=0 := by
    change (∫ y, response a.1 a.2 y-frame a.1 a.2 truth ∂kernel theta a)=0
    rw [integral_sub Integrable.of_finite (integrable_const _), hm]
    simp
  have hh := vector_noise_ae p theta (fun _ _ => rfl) g hmean C hC
    (fun a y => hb a.1 a.2 y) epsilon epsilon_nonnegative mass_tendsto V hV
    (fun u a => hv u a.1 a.2)
  filter_upwards [hh] with path hpath
  simp_rw [ScheduledRidgeController.pathState_estimate_eq_ridgeEstimate]
  apply ridgeEstimate_tendsto _ _ truth κ hκ _ (fun n => hf n _) hpath

end
end QubitOracle.AdaptiveDesign.PVMPilotSchedule

-/
