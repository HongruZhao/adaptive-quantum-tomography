import QubitOracle.AdaptiveDesign.P1ObservedRidge

/-! Strong consistency of both literal P1 estimators, including Frobenius.
All excitation and noise hypotheses below are proved for the adaptive protocol. -/
namespace QubitOracle.AdaptiveDesign.P1Weighted
open QubitOracle QubitOracle.Paper Filter MeasureTheory
open scoped BigOperators Topology InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

local instance : MeasurableSpace LabeledBinaryOutcome := ⊤
local instance : Nonempty LabeledBinaryOutcome := ⟨(0, .plus)⟩

def scale (n : ℕ) : ℝ := ((n:ℝ)+1)^(-3/4:ℝ)
def predictedGram (p : Policy) (n : ℕ) (path : Path) : Mat :=
  ∑ t ∈ Finset.range n, gram (actualAction p t path)
def gramDeviation (p : Policy) (n : ℕ) (path : Path) : Mat :=
  (∑ t ∈ Finset.range n, blochOuter (actualAxis p t path)) - predictedGram p n path

theorem lower_smul (A : Mat) (c s : ℝ) (hs : 0 ≤ s) (h : Lower A c) : Lower (s • A) (s*c) := by
  intro x
  rw [quadratic_smul,mul_assoc]
  exact mul_le_mul_of_nonneg_left (h x) hs

theorem lower_mono (A : Mat) (c b : ℝ) (hcb : c ≤ b) (h : Lower A b) : Lower A c := by
  intro x
  exact (mul_le_mul_of_nonneg_right hcb (normSq_nonneg x)).trans (h x)

theorem predictedGram_lower (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool) (n : ℕ) (path : Path) :
    Lower (predictedGram (policy loss ridge refresh) n path) ((n:ℝ)*ExplorationRidge.epsilon n/3) := by
  intro x
  rw [predictedGram,quadratic_sum]
  calc
    _ = ∑ t ∈ Finset.range n, (ExplorationRidge.epsilon n/3) * blochNormSq x := by simp; ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro t ht
      apply gram_lower _ _ _ x
      intro k
      exact (div_le_div_of_nonneg_right (ExplorationRidge.epsilon_antitone
        (Nat.le_of_lt (Finset.mem_range.mp ht))) (by norm_num)).trans
        (actual_weight_floor loss ridge refresh t path k)

theorem scale_epsilon (n : ℕ) : scale n * ExplorationRidge.epsilon n = ((n:ℝ)+1)⁻¹ := by
  unfold scale ExplorationRidge.epsilon
  rw [← Real.rpow_add (by positivity)]
  norm_num [Real.rpow_neg_one]

theorem gramDeviation_rate (p : Policy) (θ : OneQubitPhysicalParameter) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (protocol p) θ,
      Tendsto (fun n => entrySize (scale n • gramDeviation p n path)) atTop (𝓝 0) := by
  filter_upwards [gram_innovation_rate p θ] with path hp
  have hh := tendsto_finset_sum Finset.univ (fun i _ =>
    tendsto_finset_sum Finset.univ (fun j _ => (hp i j).abs))
  simpa [entrySize,gramDeviation,predictedGram,scale,Matrix.smul_apply,
    Matrix.sub_apply,Matrix.sum_apply,blochOuter,Finset.sum_sub_distrib] using hh

theorem scaledGram_lower (loss : Loss) (ridge : ℝ) (hr : 0 < ridge)
    (refresh : ℕ → Bool) (n : ℕ) (path : Path) :
    Lower (scale n • (pathState loss ridge refresh n path).gram)
      ((n:ℝ)/((n:ℝ)+1)/3 - entrySize (scale n • gramDeviation (policy loss ridge refresh) n path)) := by
  have hs : 0 ≤ scale n := Real.rpow_nonneg (by positivity) _
  have hp := lower_smul _ _ (scale n) hs (predictedGram_lower loss ridge refresh n path)
  have hbase : Lower (scale n • (ridge • (1:Mat) + predictedGram (policy loss ridge refresh) n path))
      ((n:ℝ)/((n:ℝ)+1)/3) := by
    intro x
    rw [quadratic_smul,quadratic_add,quadratic_smul,quadratic_one]
    have hh := hp x
    rw [quadratic_smul] at hh
    have hid : scale n * ((n:ℝ)*ExplorationRidge.epsilon n/3) = (n:ℝ)/((n:ℝ)+1)/3 := by
      calc
        _ = (n:ℝ)*(scale n*ExplorationRidge.epsilon n)/3 := by ring
        _ = _ := by rw [scale_epsilon]; ring
    rw [hid] at hh
    nlinarith [mul_nonneg hs (mul_nonneg hr.le (normSq_nonneg x))]
  have hh := lower_perturb _ (scale n • gramDeviation (policy loss ridge refresh) n path) _ hbase
  convert hh using 1
  rw [pathState_gram,← smul_add]
  congr 1
  simp only [gramDeviation,predictedGram]
  abel

theorem eventual_scaledGram_lower (loss : Loss) (ridge : ℝ) (hr : 0 < ridge)
    (refresh : ℕ → Bool) (θ : OneQubitPhysicalParameter) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (protocol (policy loss ridge refresh)) θ,
      ∀ᶠ n in atTop, Lower (scale n • (pathState loss ridge refresh n path).gram) (1/6) := by
  filter_upwards [gramDeviation_rate (policy loss ridge refresh) θ] with path hp
  have hc : Tendsto (fun n : ℕ => (n:ℝ)/((n:ℝ)+1)/3 -
      entrySize (scale n • gramDeviation (policy loss ridge refresh) n path)) atTop (𝓝 (1/3:ℝ)) := by
    simpa using (tendsto_natCast_div_add_atTop (1:ℝ)).div_const 3 |>.sub hp
  filter_upwards [hc.eventually (Ioi_mem_nhds (by norm_num : (1/6:ℝ)<1/3))] with n hn
  exact lower_mono _ _ _ hn.le (scaledGram_lower loss ridge hr refresh n path)

theorem outer_mulVec (u x : Fin 3 → ℝ) : (blochOuter u).mulVec x = blochDot x u • u := by
  ext i
  simp [blochOuter,Matrix.mulVec,dotProduct,blochDot,Fin.sum_univ_succ]
  ring

theorem normal_error (loss : Loss) (ridge : ℝ) (hr : 0 < ridge) (refresh : ℕ → Bool)
    (θ : Fin 3 → ℝ) (n : ℕ) (path : Path) :
    (pathState loss ridge refresh n path).gram.toEuclideanLin
      (WithLp.toLp 2 (estimate loss ridge refresh n path - θ)) =
      (∑ t ∈ Finset.range n, residual θ (actualAction (policy loss ridge refresh) t path) (path t))
        - ridge • WithLp.toLp 2 θ := by
  apply PiLp.ext
  intro i
  simp only [Matrix.toEuclideanLin_apply,PiLp.toLp_apply]
  rw [Matrix.mulVec_sub,estimate_normalEquation loss ridge hr]
  rw [pathState_rhs,pathState_gram,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec]
  simp only [Matrix.sum_mulVec,outer_mulVec,Finset.sum_apply,Pi.sub_apply,Pi.add_apply,Pi.smul_apply,
    PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,residual,PiLp.toLp_apply]
  simp [actualAxis,mul_sub,Finset.sum_sub_distrib,mul_comm]
  ring

/-- No estimator-consistency assumption is supplied: the theorem concerns the
literal history fold and all its actual adaptive Born observations. -/
theorem estimate_consistent (loss : Loss) (ridge : ℝ) (hr : 0 < ridge) (refresh : ℕ → Bool)
    (θ : OneQubitPhysicalParameter) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (protocol (policy loss ridge refresh)) θ,
      Tendsto (fun n => estimate loss ridge refresh n path) atTop (𝓝 θ.1) := by
  filter_upwards [eventual_scaledGram_lower loss ridge hr refresh θ,
    residual_rate (policy loss ridge refresh) θ] with path hG hnoise
  have hridge : Tendsto (fun n => scale n • (ridge • WithLp.toLp 2 θ.1 : Vector)) atTop (𝓝 0) := by
    simpa [scale] using ExplorationRate.weight_tendsto_zero.smul_const (ridge • WithLp.toLp 2 θ.1 : Vector)
  have hres := hnoise.sub hridge
  simp only [sub_zero] at hres
  have hnorm : Tendsto (fun n => ‖WithLp.toLp 2 (estimate loss ridge refresh n path - θ.1)‖) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _
      (by simpa using hres.norm.div_const (1/6:ℝ))
    filter_upwards [hG] with n hn
    have heq := congrArg (fun x : Vector => scale n • x)
      (normal_error loss ridge hr refresh θ.1 n path)
    have hh := CoerciveLeastSquares.norm_le_residual_div _ _ (by norm_num : (0:ℝ)<1/6)
      (lower_to_coercive _ _ hn) _ _
      (by simpa only [Matrix.toEuclideanLin.map_smul,LinearMap.smul_apply,smul_sub] using heq)
    simpa [scale,div_eq_mul_inv] using hh
  have hvec : Tendsto (fun n => WithLp.toLp 2 (estimate loss ridge refresh n path - θ.1)) atTop (𝓝 (0:Vector)) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hplain : Tendsto (fun n => estimate loss ridge refresh n path - θ.1) atTop (𝓝 0) :=
    (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)).continuousAt.tendsto.comp hvec
  convert hplain.add_const θ.1 using 1 <;> simp

end
end QubitOracle.AdaptiveDesign.P1Weighted
