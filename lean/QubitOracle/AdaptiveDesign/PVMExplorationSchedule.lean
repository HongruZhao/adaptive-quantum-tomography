import QubitOracle.AdaptiveDesign.ExplorationRidgeConsistency
import QubitOracle.AdaptiveDesign.FiniteDimensionalResponseRates

/-! General deterministic exploration schedules.  The accumulated budget,
not a prescribed power or a prescribed library cardinality, controls the
preliminary rate. -/
namespace QubitOracle.AdaptiveDesign.PVMExplorationSchedule
open Filter MeasureTheory ProbabilityTheory QubitOracle.Paper
open CoerciveLeastSquares AdaptiveRidgeConsistency ExplorationRate
open scoped BigOperators Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 1500000

/-- Static conditions on the known exploration probabilities.  The last
condition is the sufficient cumulative budget for the one-step argument;
it contains no estimator or unknown-state quantity. -/
class Schedule where
  probability : ℕ → ℝ
  nonnegative : ∀ n, 0 ≤ probability n
  le_one : ∀ n, probability n ≤ 1
  vanishes : Tendsto probability atTop (𝓝 0)
  budget_rate : Tendsto (fun n : ℕ => ((n : ℝ)+1)^(3/4 : ℝ) /
    (1 + ∑ t ∈ Finset.range n, probability t)) atTop (𝓝 0)

variable [S : Schedule]

def epsilon (n : ℕ) : ℝ := S.probability n
lemma epsilon_nonnegative (n : ℕ) : 0 ≤ epsilon n := S.nonnegative n
lemma epsilon_le_one (n : ℕ) : epsilon n ≤ 1 := S.le_one n
lemma epsilon_tendsto_zero : Tendsto epsilon atTop (𝓝 0) := S.vanishes
def budget (n : ℕ) : ℝ := ∑ t ∈ Finset.range n, epsilon t
lemma budget_nonnegative (n : ℕ) : 0 ≤ budget n :=
  Finset.sum_nonneg (fun t _ => epsilon_nonnegative t)
lemma budget_add_one_pos (n : ℕ) : 0 < 1 + budget n := by
  have h := budget_nonnegative n
  linarith
lemma budget_rate : Tendsto (fun n : ℕ => ((n : ℝ)+1)^(3/4 : ℝ) /
    (1 + budget n)) atTop (𝓝 0) := S.budget_rate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma gram_coercive (frame : ℕ → E →ₗ[ℝ] E) (κ : ℝ) (hκ : 0 < κ)
    (hf : ∀ n, Coercive (frame n) (κ * epsilon n)) (n : ℕ) :
    Coercive (ridgeGram frame 1 n) (min 1 κ * (1 + budget n)) := by
  intro x
  have hsum : κ * budget n * ‖x‖^2 ≤
      ∑ t ∈ Finset.range n, ⟪x, frame t x⟫_ℝ := by
    calc
      _ = ∑ t ∈ Finset.range n, κ * epsilon t * ‖x‖^2 := by
        simp only [budget, Finset.mul_sum, Finset.sum_mul]
      _ ≤ _ := Finset.sum_le_sum (fun t _ => hf t x)
  have hc1 : min (1 : ℝ) κ ≤ 1 := min_le_left _ _
  have hcκ : min (1 : ℝ) κ ≤ κ := min_le_right _ _
  have hmass := budget_nonnegative n
  have hb : min (1 : ℝ) κ * (1 + budget n) ≤ 1 + κ * budget n := by
    nlinarith [mul_le_mul_of_nonneg_right hcκ hmass]
  rw [ridgeGram_apply, inner_add_right, inner_smul_right, inner_sum,
    real_inner_self_eq_norm_sq, one_mul]
  nlinarith [mul_le_mul_of_nonneg_right hb (sq_nonneg ‖x‖)]

lemma ridgeEstimate_tendsto (frame : ℕ → E →ₗ[ℝ] E) (response : ℕ → E)
    (truth : E) (κ : ℝ) (hκ : 0 < κ)
    (hf0 : ∀ n, Coercive (frame n) 0)
    (hf : ∀ n, Coercive (frame n) (κ * epsilon n))
    (hnoise : Tendsto (fun n : ℕ => ((n : ℝ)+1)^(-3/4 : ℝ) •
      ∑ t ∈ Finset.range n, innovation frame response truth t) atTop (𝓝 0)) :
    Tendsto (ridgeEstimate frame response 1 0 zero_lt_one le_rfl hf0)
      atTop (𝓝 truth) := by
  let c : ℝ := min 1 κ
  have hc : 0 < c := lt_min (by norm_num) hκ
  have hridge : Tendsto (fun n : ℕ => ((n : ℝ)+1)^(-3/4 : ℝ) • truth)
      atTop (𝓝 (0 : E)) := by
    simpa using weight_tendsto_zero.smul_const truth
  have hres := hnoise.sub hridge
  simp only [smul_sub, sub_zero] at hres
  have hlim : Tendsto (fun n : ℕ =>
      (((n : ℝ)+1)^(3/4 : ℝ) / (1 + budget n) / c) *
      ‖((n : ℝ)+1)^(-3/4 : ℝ) •
        ((∑ t ∈ Finset.range n, innovation frame response truth t) - truth)‖)
      atTop (𝓝 0) := by
    simpa [smul_sub] using (budget_rate.div_const c).mul hres.norm
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply squeeze_zero (fun _ => norm_nonneg _) _ hlim
  intro n
  have hp : 0 < c * (1 + budget n) := mul_pos hc (budget_add_one_pos n)
  have hb := norm_le_residual_div _ _ hp (gram_coercive frame κ hκ hf n) _ _
    (ridgeEstimate_errorEquation frame response truth 1 0 zero_lt_one le_rfl hf0 n)
  simp only [one_smul] at hb
  apply hb.trans_eq
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  rw [show (-3/4 : ℝ) = -(3/4 : ℝ) by norm_num,
    Real.rpow_neg (by positivity)]
  have hpow : ((n : ℝ)+1)^(3/4 : ℝ) ≠ 0 := by positivity
  have hmass := (budget_add_one_pos n).ne'
  field_simp

variable {Theta Action Outcome : Type*}
  [MeasurableSpace Action] [MeasurableSpace Outcome]
  [Fintype Outcome] [MeasurableSingletonClass Outcome]
  [StandardBorelSpace Outcome] [Nonempty Outcome]

theorem scheduled_estimate_consistent
    (kernel : Theta → Kernel (ℕ × Action) Outcome)
    (hk : ∀ theta, IsMarkovKernel (kernel theta))
    (theta : Theta) (frame : ℕ → Action → E →ₗ[ℝ] E)
    (response : ℕ → Action → Outcome → E)
    (truth : E) (controller : E → Action) (refresh : ℕ → Bool)
    (κ : ℝ) (hκ : 0 < κ) (hf0 : ∀ n a, Coercive (frame n a) 0)
    (hf : ∀ n a, Coercive (frame n a) (κ * epsilon n))
    (hmean : ∀ n a, ∫ y, response n a y ∂kernel theta (n,a) = frame n a truth)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n a y, ‖response n a y - frame n a truth‖ ≤ C) :
    let p := ScheduledRidgeController.protocol kernel hk frame response controller refresh
      1 0 zero_lt_one le_rfl hf0
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure p theta,
      Tendsto (fun n => (ScheduledRidgeController.pathState frame response controller refresh
        1 0 zero_lt_one le_rfl hf0 path n).estimate zero_lt_one) atTop (𝓝 truth) := by
  intro p
  letI : IsMarkovKernel (kernel theta) := hk theta
  let centered : (ℕ × Action) → Outcome → E :=
    fun a y => response a.1 a.2 y - frame a.1 a.2 truth
  have hc : ∀ a, ∫ y, centered a y ∂p.response theta a = 0 := by
    intro a
    change (∫ y, response a.1 a.2 y - frame a.1 a.2 truth ∂kernel theta a) = 0
    rw [integral_sub Integrable.of_finite (integrable_const _), hmean]
    simp
  have hh := actualVectorResponse_threeQuarter_ae_tendsto_zero p theta centered hc C hC
    (fun a y => hbound a.1 a.2 y)
  filter_upwards [hh] with path hpath
  simp_rw [ScheduledRidgeController.pathState_estimate_eq_ridgeEstimate]
  apply ridgeEstimate_tendsto _ _ truth κ hκ _ (fun n => hf n _) hpath

end
end QubitOracle.AdaptiveDesign.PVMExplorationSchedule
