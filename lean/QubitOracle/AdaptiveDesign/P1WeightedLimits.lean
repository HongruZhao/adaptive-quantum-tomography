import QubitOracle.AdaptiveDesign.P1WeightedGeometry

/-! Limits of the actual regression Gram and conditional residual covariance.
No convergence of the chosen eigenvectors is needed, even at the center. -/
namespace QubitOracle.AdaptiveDesign.P1Weighted
open QubitOracle QubitOracle.Paper Filter MeasureTheory
open AdaptiveResponseStrongLaw
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
local instance : MeasurableSpace LabeledBinaryOutcome := ⊤
local instance : Nonempty LabeledBinaryOutcome := ⟨(0, .plus)⟩

def heldController (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool) (n : ℕ) (path : Path) : Fin 3 → ℝ :=
  controller loss (P1.lastRefresh refresh n) (estimate loss ridge refresh (P1.lastRefresh refresh n) path)

theorem action_eq_reference (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool) (n : ℕ) (path : Path) :
    actualAction (policy loss ridge refresh) n path =
      referenceAction loss (heldController loss ridge refresh n path) (controller_interior loss _ _) :=
  action_eq_lastRefresh loss ridge refresh n path

theorem heldController_consistent (loss : Loss) (ridge : ℝ) (hr : 0 < ridge)
    (refresh : ℕ → Bool) (hrefresh : ∀ K, ∃ n, K ≤ n ∧ refresh n = true)
    (θ : OneQubitPhysicalParameter) (hθ : blochNormSq θ.1 < 1) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (protocol (policy loss ridge refresh)) θ,
      Tendsto (fun n => heldController loss ridge refresh n path) atTop (𝓝 θ.1) := by
  filter_upwards [controller_consistent loss ridge hr refresh θ hθ] with path hp
  exact hp.comp (P1.lastRefresh_tendsto refresh hrefresh)

theorem gram_current_tendsto (loss : Loss) (ridge : ℝ) (hr : 0 < ridge)
    (refresh : ℕ → Bool) (hrefresh : ∀ K, ∃ n, K ≤ n ∧ refresh n = true)
    (θ : OneQubitPhysicalParameter) (hθ : blochNormSq θ.1 < 1) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (protocol (policy loss ridge refresh)) θ,
      Tendsto (fun n => gram (actualAction (policy loss ridge refresh) n path))
        atTop (𝓝 (meanGramTarget loss θ.1)) := by
  filter_upwards [heldController_consistent loss ridge hr refresh hrefresh θ hθ] with path hp
  simpa only [action_eq_reference,gram_reference,Function.comp_def] using
    (continuous_meanGramTarget loss).continuousAt.tendsto.comp hp

theorem dot_abs_le_one (θ : Fin 3 → ℝ) (hθ : blochNormSq θ ≤ 1) (a : Action) (k : Fin 3) :
    |blochDot θ (axis a k)| ≤ 1 := by
  have hh := bloch_cauchy_schwarz θ (axis a k)
  have ha : blochNormSq (axis a k) = 1 := a.frame.unit_axes k
  rw [ha,mul_one] at hh
  nlinarith [sq_abs (blochDot θ (axis a k)),abs_nonneg (blochDot θ (axis a k))]

theorem noise_stability (θ r : Fin 3 → ℝ) (hθ : blochNormSq θ ≤ 1)
    (hr : blochNormSq r ≤ 1) (a : Action) (i j : Fin 3) :
    |noiseCovariance θ a i j - noiseCovariance r a i j| ≤ 6*‖θ-r‖ := by
  have hterm (k : Fin 3) :
      |((1-blochDot θ (axis a k)^2) - (1-blochDot r (axis a k)^2)) *
        (axis a k i * axis a k j)| ≤ 6*‖θ-r‖ := by
    have hx := dot_abs_le_one θ hθ a k
    have hy := dot_abs_le_one r hr a k
    have hd := blochDot_sub_abs_le_three_norm θ r (axis a k) (a.frame.unit_axes k)
    have hp : |axis a k i * axis a k j| ≤ 1 := by
      rw [abs_mul]
      exact (mul_le_mul (axis_abs_le_one a k i) (axis_abs_le_one a k j)
        (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
    have hs : |blochDot θ (axis a k)+blochDot r (axis a k)| ≤ 2 :=
      (abs_add_le _ _).trans (by linarith)
    have he : (1-blochDot θ (axis a k)^2) - (1-blochDot r (axis a k)^2) =
        -(blochDot θ (axis a k)-blochDot r (axis a k)) *
          (blochDot θ (axis a k)+blochDot r (axis a k)) := by ring
    rw [he,abs_mul,abs_mul,abs_neg]
    calc
      _ ≤ (3*‖θ-r‖)*2*1 := mul_le_mul (mul_le_mul hd hs (abs_nonneg _) (by positivity)) hp
        (abs_nonneg _) (by positivity)
      _ = _ := by ring
  simp only [noiseCovariance,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,blochOuter]
  rw [← Finset.sum_sub_distrib]
  calc
    _ = |∑ k, a.weight k * (((1-blochDot θ (axis a k)^2) - (1-blochDot r (axis a k)^2)) *
        (axis a k i * axis a k j))| := by congr 1; apply Finset.sum_congr rfl; intros; ring
    _ ≤ ∑ k, |a.weight k * (((1-blochDot θ (axis a k)^2) - (1-blochDot r (axis a k)^2)) *
        (axis a k i * axis a k j))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, a.weight k * (6*‖θ-r‖) := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul,abs_of_nonneg (a.nonneg k)]
      exact mul_le_mul_of_nonneg_left (hterm k) (a.nonneg k)
    _ = _ := by rw [← Finset.sum_mul,a.total,one_mul]

theorem noise_current_tendsto (loss : Loss) (ridge : ℝ) (hr : 0 < ridge)
    (refresh : ℕ → Bool) (hrefresh : ∀ K, ∃ n, K ≤ n ∧ refresh n = true)
    (θ : OneQubitPhysicalParameter) (hθ : blochNormSq θ.1 < 1) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (protocol (policy loss ridge refresh)) θ,
      Tendsto (fun n => noiseCovariance θ.1 (actualAction (policy loss ridge refresh) n path))
        atTop (𝓝 (noiseTarget loss θ.1)) := by
  filter_upwards [heldController_consistent loss ridge hr refresh hrefresh θ hθ] with path hp
  have href := (continuous_noiseTarget loss).continuousAt.tendsto.comp hp
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have hdiff : Tendsto (fun n => noiseCovariance θ.1 (actualAction (policy loss ridge refresh) n path) i j -
      noiseTarget loss (heldController loss ridge refresh n path) i j) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hzero : Tendsto (fun n => 6*‖θ.1-heldController loss ridge refresh n path‖) atTop (𝓝 0) := by
      simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => θ.1) atTop (𝓝 θ.1)).sub hp).norm.const_mul (6:ℝ)
    apply squeeze_zero (fun _ => norm_nonneg _) _ hzero
    intro n
    have hheld : blochNormSq (heldController loss ridge refresh n path) < 1 := controller_interior loss _ _
    rw [Real.norm_eq_abs,action_eq_reference,← noise_reference loss _ hheld]
    exact noise_stability _ _ hθ.le (controller_interior loss _ _).le _ i j
  have hh := (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp href i) j).add hdiff
  convert hh using 1
  · ext n
    simp only [Function.comp_apply]
    ring
  · simp

theorem gram_innovation_average (p : Policy) (θ : OneQubitPhysicalParameter) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (protocol p) θ, ∀ i j : Fin 3,
      Tendsto (fun n : ℕ => (n:ℝ)⁻¹ * ∑ t ∈ Finset.range n,
        (actualAxis p t path i * actualAxis p t path j - gram (actualAction p t path) i j))
        atTop (𝓝 0) := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  exact actualResponse_average_ae_tendsto_zero (protocol p) θ
    (fun a z => axis a z.1 i * axis a z.1 j - gram a i j)
    (fun a => gram_centered_mean θ a i j) 2 (by norm_num)
    (fun a z => gram_innovation_bound a z i j)

theorem observedGram_tendsto (loss : Loss) (ridge : ℝ) (hr : 0 < ridge)
    (refresh : ℕ → Bool) (hrefresh : ∀ K, ∃ n, K ≤ n ∧ refresh n = true)
    (θ : OneQubitPhysicalParameter) (hθ : blochNormSq θ.1 < 1) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (protocol (policy loss ridge refresh)) θ,
      Tendsto (fun n : ℕ => (n:ℝ)⁻¹ • (pathState loss ridge refresh n path).gram)
        atTop (𝓝 (meanGramTarget loss θ.1)) := by
  filter_upwards [gram_current_tendsto loss ridge hr refresh hrefresh θ hθ,
    gram_innovation_average (policy loss ridge refresh) θ] with path hg hn
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have ha := (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hg i) j).cesaro_smul
  have hb := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).mul_const
    ((ridge • (1:Mat)) i j)
  have hh := hb.add (ha.add (hn i j))
  convert hh using 1
  · ext n
    simp [pathState_gram,Matrix.smul_apply,Matrix.add_apply,Matrix.sum_apply,
      blochOuter,Finset.sum_sub_distrib,smul_eq_mul]
    ring
  · simp

end
end QubitOracle.AdaptiveDesign.P1Weighted
