import QubitOracle.AdaptiveDesign.PolynomialSqrtExponential
import QubitOracle.AdaptiveDesign.ExplorationRidgeConsistency
import QubitOracle.AdaptiveDesign.P1ControllerBounds
import QubitOracle.AdaptiveDesign.P1FiniteSampleBounds
import QubitOracle.AdaptiveDesign.P1Localization
import QubitOracle.AdaptiveDesign.P1WeightedBorn
import QubitOracle.AdaptiveDesign.P1WeightedController
import QubitOracle.AdaptiveDesign.P1WeightedPolicy
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.AdaptiveTrajectoryExperiment
import QubitOracle.Paper.MixedProbabilityFloor
import QubitOracle.Paper.MixedRotationalTarget
import QubitOracle.Paper.OneQubitCyclicBornPath
import QubitOracle.Paper.OneQubitLabeledThreeAxisBornKernel
namespace QubitOracle.AdaptiveDesign.P1Weighted
open QubitOracle QubitOracle.Paper Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
local instance P1ControllerLocalization_measurable : MeasurableSpace LabeledBinaryOutcome := ⊤
local instance P1ControllerLocalization_nonempty : Nonempty LabeledBinaryOutcome := ⟨(0,.plus)⟩

def reportedError (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool) (θ : Fin 3 → ℝ)
    (n : ℕ) (path : Path) : Vector :=
  WithLp.toLp 2 (controller loss n (estimate loss ridge refresh n path)-θ)

theorem truth_eventually_in_clip_ball (θ : Fin 3 → ℝ) (hθ : blochNormSq θ < 1) :
    ∀ᶠ n in atTop, blochNormSq θ ≤ 1-ExplorationRidge.epsilon (n+1)^2 := by
  have hh : Tendsto (fun n => 1-ExplorationRidge.epsilon (n+1)^2) atTop (𝓝 (1:ℝ)) := by
    simpa using tendsto_const_nhds.sub ((ExplorationRidge.epsilon_tendsto_zero.comp
      (tendsto_add_atTop_nat 1)).pow 2)
  exact hh.eventually (eventually_ge_nhds hθ)

theorem frobenius_controller_localization (ridge : ℝ) (hr : 0 < ridge) (refresh : ℕ → Bool)
    (θ : OneQubitPhysicalParameter) (hθ : blochNormSq θ.1 < 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ B c : ℝ, 0 < B ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      (adaptiveInfiniteTrajectoryMeasure (protocol (policy .frobenius ridge refresh)) θ).real
        {path | δ ≤ ‖reportedError .frobenius ridge refresh θ.1 (n+1) path‖} ≤
      B*Real.exp (-c*Real.sqrt ((n+1:ℕ):ℝ)) := by
  obtain ⟨B,c,hB,hc,ht⟩ := raw_localization .frobenius ridge hr refresh θ δ hδ
  refine ⟨B,c,hB,hc,?_⟩
  filter_upwards [ht,truth_eventually_in_clip_ball θ.1 hθ] with n hn hball
  apply (measureReal_mono ?_).trans hn
  intro path hp
  exact hp.trans (clip_error_bound (n+1) (estimate .frobenius ridge refresh (n+1) path) θ.1 hball)

theorem frobenius_weight_local_lower (θ : Fin 3 → ℝ) (hθ : blochNormSq θ < 1) :
    ∃ δ κ : ℝ, 0 < δ ∧ 0 < κ ∧ ∀ x : Fin 3 → ℝ,
      ‖WithLp.toLp 2 (x-θ)‖ < δ → ∀ i, κ ≤ weight .frobenius x i := by
  let g := mixedRadialGap θ
  have hg : 0 < g := mixedRadialGap_pos θ hθ
  have hg1 : g ≤ 1 := gap_le_one θ
  have hcont : Continuous (fun x : Vector => mixedRadialGap x.ofLp) :=
    continuous_mixedRadialGap.comp (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ))
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp (hcont.continuousAt (x:=WithLp.toLp 2 θ))
    (g/2) (by positivity)
  refine ⟨δ,g/6,hδ,by positivity,fun x hx i => ?_⟩
  have hd : dist (WithLp.toLp 2 x) (WithLp.toLp 2 θ) < δ := by
    rw [dist_eq_norm]
    have he : WithLp.toLp 2 x-WithLp.toLp 2 θ = WithLp.toLp 2 (x-θ) := by ext i; rfl
    rw [he]
    exact hx
  have hh := hclose hd
  change |mixedRadialGap x-g| < g/2 at hh
  have hxg : g/2 ≤ mixedRadialGap x := by linarith only [neg_lt_of_abs_lt hh]
  have hx1 := gap_le_one x
  have hxn : 0 ≤ mixedRadialGap x := Real.sqrt_nonneg _
  have ha : g/6 ≤ mixedCoherenceAllocation x := by
    unfold mixedCoherenceAllocation
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [mul_nonneg hg.le (sub_nonneg.mpr hx1)]
  have hb : g/6 ≤ mixedRadialAllocation x := by
    unfold mixedRadialAllocation
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [mul_nonneg hg.le (sub_nonneg.mpr hx1)]
  fin_cases i <;> simp only [weight,radialTangentMass,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one] <;> assumption

theorem inverse_weight_bound (loss : Loss) (k : ℕ) (x : Fin 3 → ℝ) (i : Fin 3) :
    (weight loss (controller loss k x) i)⁻¹ ≤ 3*((k:ℝ)+1) := by
  have hN : (1:ℝ) ≤ (k:ℝ)+1 := by linarith [Nat.cast_nonneg (α:=ℝ) k]
  have he : ((k:ℝ)+1)⁻¹ ≤ ExplorationRidge.epsilon k := by
    unfold ExplorationRidge.epsilon
    simpa only [Real.rpow_neg_one] using Real.rpow_le_rpow_of_exponent_le hN
      (show (-1:ℝ) ≤ -1/4 by norm_num)
  have hw := weight_floor loss k x i
  have hp : 0 < weight loss (controller loss k x) i :=
    (div_pos (ExplorationRidge.epsilon_pos k) (by norm_num)).trans_le hw
  have hlow : (3*((k:ℝ)+1))⁻¹ ≤ weight loss (controller loss k x) i := by
    have hh := div_le_div_of_nonneg_right he (by norm_num : (0:ℝ)≤3)
    calc
      _ = ((k:ℝ)+1)⁻¹/3 := by rw [mul_inv]; ring
      _ ≤ ExplorationRidge.epsilon k/3 := hh
      _ ≤ _ := hw
  have hh := one_div_le_one_div_of_le (show (0:ℝ)<(3*((k:ℝ)+1))⁻¹ by positivity) hlow
  simpa only [one_div,inv_inv] using hh

end
end QubitOracle.AdaptiveDesign.P1Weighted
