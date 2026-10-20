import QubitOracle.AdaptiveDesign.P1ControllerBounds
import QubitOracle.AdaptiveDesign.ExplorationRidgeConsistency
import QubitOracle.AdaptiveDesign.P1FiniteSampleBounds
import QubitOracle.AdaptiveDesign.P1ObservedRidge
import QubitOracle.AdaptiveDesign.P1WeightedBorn
import QubitOracle.AdaptiveDesign.P1WeightedConsistency
import QubitOracle.AdaptiveDesign.P1WeightedController
import QubitOracle.AdaptiveDesign.P1WeightedPolicy
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.AdaptiveTrajectoryExperiment
import QubitOracle.Paper.MixedProbabilityFloor
import QubitOracle.Paper.OneQubitCyclicBornPath
import QubitOracle.Paper.OneQubitLabeledThreeAxisBornKernel
/-! Localization of the actual observed-axis ridge estimator. The
expanding-ball safeguard supplies excitation before consistency is used. -/
namespace QubitOracle.AdaptiveDesign.P1Weighted
open QubitOracle QubitOracle.Paper Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
local instance P1Localization_measurable : MeasurableSpace LabeledBinaryOutcome := ⊤
local instance P1Localization_nonempty : Nonempty LabeledBinaryOutcome := ⟨(0,.plus)⟩

theorem safeguard_variance_scale (n : ℕ) (hn : 0 < n) :
    Real.sqrt (n:ℝ)/2 ≤ (n:ℝ)*(ExplorationRidge.epsilon n)^2 := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hs : Real.sqrt ((n:ℝ)+1)^2=(n:ℝ)+1 := Real.sq_sqrt (by positivity)
  have hp : (ExplorationRidge.epsilon n)^2*Real.sqrt ((n:ℝ)+1)=1 := by
    unfold ExplorationRidge.epsilon
    rw [Real.sqrt_eq_rpow,← Real.rpow_natCast,← Real.rpow_mul (by positivity),← Real.rpow_add (by positivity)]
    norm_num
  have he : Real.sqrt ((n:ℝ)+1)/2 ≤ (n:ℝ)*(ExplorationRidge.epsilon n)^2 := by
    apply (mul_le_mul_iff_right₀ (Real.sqrt_pos.mpr (show (0:ℝ)<(n:ℝ)+1 by positivity))).mp
    calc
      _ = ((n:ℝ)+1)/2 := by nlinarith only [hs]
      _ ≤ (n:ℝ) := by linarith only [hn']
      _ = _ := by nlinarith only [congrArg (fun x : ℝ => (n:ℝ)*x) hp]
  exact (div_le_div_of_nonneg_right (Real.sqrt_le_sqrt (by linarith : (n:ℝ)≤(n:ℝ)+1)) (by norm_num)).trans he

theorem safeguard_budget_tendsto :
    Tendsto (fun n : ℕ => (n:ℝ)*ExplorationRidge.epsilon n) atTop atTop := by
  have hh := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<3/4)).comp
    (show Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop from
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)).const_mul_atTop (by norm_num : (0:ℝ)<1/2)
  apply tendsto_atTop_mono' atTop _ hh
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  dsimp only [Function.comp_def]
  rw [← ExplorationRidge.epsilon_growth]
  nlinarith [ExplorationRidge.epsilon_pos n]

theorem raw_localization (loss : Loss) (ridge : ℝ) (hr : 0 < ridge) (refresh : ℕ → Bool)
    (θ : OneQubitPhysicalParameter) (δ : ℝ) (hδ : 0 < δ) :
    ∃ B c : ℝ, 0 < B ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      (adaptiveInfiniteTrajectoryMeasure (protocol (policy loss ridge refresh)) θ).real
        {path | δ ≤ ‖rawError loss ridge refresh θ.1 (n+1) path‖} ≤
      B*Real.exp (-c*Real.sqrt ((n+1:ℕ):ℝ)) := by
  let p := policy loss ridge refresh
  let μ := adaptiveInfiniteTrajectoryMeasure (protocol p) θ
  obtain ⟨B1,c1,hB1,hc1,hg⟩ := gramDeviation_tail p θ
  obtain ⟨B2,c2,hB2,hc2,hm⟩ := residualSum_tail p θ
  let c := min (c1/72) (c2*δ^2/288)
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  have hbias : ∀ᶠ n : ℕ in atTop,
      ridge*‖WithLp.toLp 2 θ.1‖ ≤ δ*((n+1:ℕ):ℝ)*ExplorationRidge.epsilon (n+1)/12 := by
    have ht := (safeguard_budget_tendsto.comp (tendsto_add_atTop_nat 1)).const_mul_atTop
      (show (0:ℝ)<δ/12 by positivity)
    have he := ht.eventually (eventually_ge_atTop (ridge*‖WithLp.toLp 2 θ.1‖))
    filter_upwards [he] with n hn
    dsimp only [Function.comp_def] at hn
    convert hn using 1 <;> first | rfl | ring
  refine ⟨B1+B2,c,by positivity,hc,?_⟩
  filter_upwards [hbias] with n hbias
  let N : ℝ := ((n+1:ℕ):ℝ)
  let ε := ExplorationRidge.epsilon (n+1)
  have hN : 0 < N := by dsimp [N]; positivity
  have hε : 0 < ε := ExplorationRidge.epsilon_pos _
  have hsub : {path | δ ≤ ‖rawError loss ridge refresh θ.1 (n+1) path‖} ⊆
      {path | N*ε/6 ≤ entrySize (gramDeviation p (n+1) path)} ∪
        {path | δ*N*ε/12 ≤ ‖residualSum p θ.1 (n+1) path‖} := by
    intro path hp
    by_contra hx
    have hnot := not_or.mp hx
    have hgd : entrySize (gramDeviation p (n+1) path) < N*ε/6 := not_le.mp hnot.1
    have hres : ‖residualSum p θ.1 (n+1) path‖ < δ*N*ε/12 := not_le.mp hnot.2
    have hG := gram_lower_from_predicted loss ridge hr.le refresh (n+1) path _
      (predictedGram_lower loss ridge refresh (n+1) path)
    have hG' : Lower (pathState loss ridge refresh (n+1) path).gram (N*ε/6) :=
      lower_mono _ _ _ (by dsimp [p,N,ε] at hgd ⊢; linarith only [hgd]) hG
    have he := rawError_of_lower loss ridge hr refresh θ.1 (n+1) path _ (by positivity) hG'
    have hh := (div_lt_iff₀ (show 0<N*ε/6 by positivity)).mpr
      (show ‖residualSum p θ.1 (n+1) path‖+ridge*‖WithLp.toLp 2 θ.1‖ < δ*(N*ε/6) by
        change ridge*‖WithLp.toLp 2 θ.1‖ ≤ δ*N*ε/12 at hbias
        linarith only [hres,hbias])
    exact (not_le_of_gt (he.trans_lt hh)) hp
  have he1 : -c1*(N*ε/6)^2/N ≤ -c*Real.sqrt N := by
    have hv := safeguard_variance_scale (n+1) (by omega)
    change Real.sqrt N/2 ≤ N*ε^2 at hv
    have hh := mul_le_mul_of_nonneg_left hv (div_pos hc1 (by norm_num : (0:ℝ)<36)).le
    have hm := mul_le_mul_of_nonneg_right (min_le_left (c1/72) (c2*δ^2/288)) (Real.sqrt_nonneg N)
    have hid : -c1*(N*ε/6)^2/N = -(c1/36)*(N*ε^2) := by field_simp; ring
    rw [hid]
    dsimp only [c] at *
    nlinarith only [hh,hm]
  have he2 : -c2*(δ*N*ε/12)^2/N ≤ -c*Real.sqrt N := by
    have hv := safeguard_variance_scale (n+1) (by omega)
    change Real.sqrt N/2 ≤ N*ε^2 at hv
    have hh := mul_le_mul_of_nonneg_left hv (show 0≤c2*δ^2/144 by positivity)
    have hm := mul_le_mul_of_nonneg_right (min_le_right (c1/72) (c2*δ^2/288)) (Real.sqrt_nonneg N)
    have hid : -c2*(δ*N*ε/12)^2/N = -(c2*δ^2/144)*(N*ε^2) := by field_simp; ring
    rw [hid]
    dsimp only [c] at *
    nlinarith only [hh,hm]
  calc
    _ ≤ μ.real ({path | N*ε/6 ≤ entrySize (gramDeviation p (n+1) path)} ∪
        {path | δ*N*ε/12 ≤ ‖residualSum p θ.1 (n+1) path‖}) := measureReal_mono hsub
    _ ≤ μ.real {path | N*ε/6 ≤ entrySize (gramDeviation p (n+1) path)}+
        μ.real {path | δ*N*ε/12 ≤ ‖residualSum p θ.1 (n+1) path‖} := measureReal_union_le _ _
    _ ≤ B1*Real.exp (-c1*(N*ε/6)^2/N)+B2*Real.exp (-c2*(δ*N*ε/12)^2/N) :=
      add_le_add (hg n (N*ε/6) (by positivity)) (hm n (δ*N*ε/12) (by positivity))
    _ ≤ (B1+B2)*Real.exp (-c*Real.sqrt N) := by
      nlinarith only [mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he1) hB1.le,
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he2) hB2.le]

end
end QubitOracle.AdaptiveDesign.P1Weighted
