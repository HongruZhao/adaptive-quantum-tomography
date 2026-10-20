import QubitOracle.AdaptiveDesign.ScheduledRidgeController

/-! Vanishing exploration still gives consistency on the actual adaptive law.
The rate is proved from bounded innovations, not assumed of the estimator. -/
namespace QubitOracle.AdaptiveDesign.ExplorationRidge
open Filter MeasureTheory ProbabilityTheory QubitOracle.Paper
open CoerciveLeastSquares AdaptiveRidgeConsistency ExplorationRate
open scoped BigOperators Topology InnerProductSpace
noncomputable section

def epsilon (n : ℕ) : ℝ := ((n:ℝ)+1)^(-1/4:ℝ)
lemma epsilon_pos (n : ℕ) : 0 < epsilon n := Real.rpow_pos_of_pos (by positivity) _
lemma epsilon_le_one (n : ℕ) : epsilon n ≤ 1 := by
  exact Real.rpow_le_one_of_one_le_of_nonpos (by have h := Nat.cast_nonneg (α := ℝ) n; linarith) (by norm_num)
lemma epsilon_antitone : Antitone epsilon := by
  intro m n h
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast Nat.add_le_add_right h 1)
    (by norm_num)
lemma epsilon_tendsto_zero : Tendsto epsilon atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => ((n:ℝ)+1)^(-1/4:ℝ)) atTop (𝓝 0)
  have ht : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  convert (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/4)).comp ht using 1 <;> norm_num [epsilon, Function.comp_def]
lemma epsilon_growth (n : ℕ) : ((n:ℝ)+1) * epsilon n = ((n:ℝ)+1)^(3/4:ℝ) := by
  change ((n:ℝ)+1) * ((n:ℝ)+1)^(-1/4:ℝ) = _
  calc
    _ = ((n:ℝ)+1)^(1:ℝ) * ((n:ℝ)+1)^(-1/4:ℝ) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_add (by positivity)]; norm_num

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
lemma gram_coercive (frame : ℕ → E →ₗ[ℝ] E) (κ : ℝ) (hκ : 0 < κ)
    (hf : ∀ n, Coercive (frame n) (κ * epsilon n)) (n : ℕ) (hn : 0 < n) :
    Coercive (ridgeGram frame 1 n) ((κ/2) * ((n:ℝ)+1)^(3/4:ℝ)) := by
  intro x
  have hsum : (n:ℝ) * (κ * epsilon n * ‖x‖^2) ≤
      ∑ t ∈ Finset.range n, ⟪x, frame t x⟫_ℝ := by
    calc
      _ = ∑ t ∈ Finset.range n, κ * epsilon n * ‖x‖^2 := by simp
      _ ≤ _ := Finset.sum_le_sum fun t ht =>
        le_trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (epsilon_antitone (Nat.le_of_lt (Finset.mem_range.mp ht))) hκ.le)
          (sq_nonneg _)) (hf t x)
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have heg := epsilon_growth n
  have he := epsilon_pos n
  rw [ridgeGram_apply, inner_add_right, inner_smul_right, inner_sum,
    real_inner_self_eq_norm_sq, one_mul]
  have hh : ((κ/2)*((n:ℝ)+1)^(3/4:ℝ)) ≤ (n:ℝ)*κ*epsilon n := by
    rw [← heg]
    nlinarith [mul_nonneg (show 0 ≤ (n:ℝ)-1 by linarith) (mul_pos hκ he).le]
  nlinarith [mul_le_mul_of_nonneg_right hh (sq_nonneg ‖x‖), sq_nonneg ‖x‖]

theorem ridgeEstimate_tendsto (frame : ℕ → E →ₗ[ℝ] E) (response : ℕ → E)
    (truth : E) (κ : ℝ) (hκ : 0 < κ)
    (hf0 : ∀ n, Coercive (frame n) 0)
    (hf : ∀ n, Coercive (frame n) (κ * epsilon n))
    (hnoise : Tendsto (fun n : ℕ => ((n:ℝ)+1)^(-3/4:ℝ) •
      ∑ t ∈ Finset.range n, innovation frame response truth t) atTop (𝓝 0)) :
    Tendsto (ridgeEstimate frame response 1 0 zero_lt_one le_rfl hf0) atTop (𝓝 truth) := by
  have hridge : Tendsto (fun n : ℕ => ((n:ℝ)+1)^(-3/4:ℝ) • truth) atTop (𝓝 (0:E)) := by
    simpa using weight_tendsto_zero.smul_const truth
  have hres : Tendsto (fun n : ℕ => ((n:ℝ)+1)^(-3/4:ℝ) •
      ((∑ t ∈ Finset.range n, innovation frame response truth t) - truth)) atTop (𝓝 (0:E)) := by
    simpa only [smul_sub, sub_zero] using hnoise.sub hridge
  have hlim : Tendsto (fun n : ℕ => ‖((n:ℝ)+1)^(-3/4:ℝ) •
      ((∑ t ∈ Finset.range n, innovation frame response truth t) - truth)‖ / (κ/2))
      atTop (𝓝 0) := by simpa using hres.norm.div_const (κ/2)
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _)) _ hlim
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hbound := norm_le_residual_div _ _ (by positivity : 0 < (κ/2)*((n:ℝ)+1)^(3/4:ℝ))
    (gram_coercive frame κ hκ hf n hn) _ _
    (ridgeEstimate_errorEquation frame response truth 1 0 zero_lt_one le_rfl hf0 n)
  simp only [one_smul] at hbound
  calc
    _ ≤ ‖(∑ t ∈ Finset.range n, innovation frame response truth t)-truth‖ /
      ((κ/2)*((n:ℝ)+1)^(3/4:ℝ)) := hbound
    _ = _ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      rw [show (-3/4:ℝ)= -(3/4:ℝ) by norm_num, Real.rpow_neg (by positivity)]
      field_simp

variable {Theta Action Outcome : Type*}
variable [MeasurableSpace Action] [MeasurableSpace Outcome]
variable [Fintype Outcome] [MeasurableSingletonClass Outcome]
variable [StandardBorelSpace Outcome] [Nonempty Outcome]
/-- A complete probabilistic consistency theorem for the scheduled history fold. -/
theorem scheduled_estimate_consistent
    (kernel : Theta → Kernel (ℕ × Action) Outcome) (hk : ∀ theta, IsMarkovKernel (kernel theta))
    (theta : Theta) (frame : ℕ → Action → E →ₗ[ℝ] E) (response : ℕ → Action → Outcome → E)
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
  let centered : (ℕ × Action) → Outcome → E := fun a y => response a.1 a.2 y - frame a.1 a.2 truth
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
end QubitOracle.AdaptiveDesign.ExplorationRidge
