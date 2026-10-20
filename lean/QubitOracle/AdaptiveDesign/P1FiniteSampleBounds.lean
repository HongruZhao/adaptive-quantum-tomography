import QubitOracle.AdaptiveDesign.P1WeightedEndpoints
import QubitOracle.AdaptiveDesign.FiniteGaussianTails

/-! Actual mixed-qubit residual and Gram tails, and pathwise ridge
error inequalities, uniform over deterministic refresh schedules. -/
namespace QubitOracle.AdaptiveDesign.P1Weighted
open QubitOracle QubitOracle.Paper Filter MeasureTheory ProbabilityTheory
open AdaptiveResponseMoments AdaptiveRidgeConsistency
open scoped BigOperators Topology InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
local instance P1FiniteSampleBounds_measurable : MeasurableSpace LabeledBinaryOutcome := ⊤
local instance P1FiniteSampleBounds_nonempty : Nonempty LabeledBinaryOutcome := ⟨(0,.plus)⟩

def residualSum (p : Policy) (θ : Fin 3 → ℝ) (n : ℕ) (path : Path) : Vector :=
  ∑ t ∈ Finset.range n, residual θ (actualAction p t path) (path t)

theorem residualSum_bound (p : Policy) (θ : OneQubitPhysicalParameter) (n : ℕ) (path : Path) :
    ‖residualSum p θ.1 n path‖ ≤ (n:ℝ)*6 := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _k ∈ Finset.range n, (6:ℝ) := Finset.sum_le_sum (fun _ _ => residual_bound θ _ _)
    _ = _ := by simp

theorem residualSum_moments (p : Policy) (θ : OneQubitPhysicalParameter) (r : ℕ) :
    UniformMoment (adaptiveInfiniteTrajectoryMeasure (protocol p) θ)
      (fun n path => (Real.sqrt ((n+1:ℕ):ℝ))⁻¹ • residualSum p θ.1 (n+1) path) r :=
  actualVectorResponse_uniformMoment (protocol p) θ (residual θ.1) (residual_mean θ)
    6 (by norm_num) (residual_bound θ) r

theorem residualSum_tail (p : Policy) (θ : OneQubitPhysicalParameter) :
    ∃ B c : ℝ, 0 < B ∧ 0 < c ∧ ∀ (n : ℕ) (x : ℝ), 0 ≤ x →
      (adaptiveInfiniteTrajectoryMeasure (protocol p) θ).real
        {path | x ≤ ‖residualSum p θ.1 (n+1) path‖} ≤ B*Real.exp (-c*x^2/((n+1:ℕ):ℝ)) :=
  AdaptiveGaussianTails.vector (protocol p) θ (residual θ.1) (residual_mean θ)
    6 (by norm_num) (residual_bound θ)

theorem gramDeviation_tail (p : Policy) (θ : OneQubitPhysicalParameter) :
    ∃ B c : ℝ, 0 < B ∧ 0 < c ∧ ∀ (n : ℕ) (x : ℝ), 0 ≤ x →
      (adaptiveInfiniteTrajectoryMeasure (protocol p) θ).real
        {path | x ≤ entrySize (gramDeviation p (n+1) path)} ≤ B*Real.exp (-c*x^2/((n+1:ℕ):ℝ)) := by
  have hh (ij : Fin 3 × Fin 3) := AdaptiveGaussianTails.scalar (protocol p) θ
    (fun a z => axis a z.1 ij.1*axis a z.1 ij.2-gram a ij.1 ij.2)
    (fun a => gram_centered_mean θ a ij.1 ij.2) 2 (by norm_num) (fun a z => gram_innovation_bound a z ij.1 ij.2)
  obtain ⟨B,c,hB,hc,ht⟩ := AdaptiveGaussianTails.finiteSum
    (fun (ij : Fin 3 × Fin 3) n path => ∑ k ∈ Finset.range (n+1),
      (actualAxis p k path ij.1*actualAxis p k path ij.2-gram (actualAction p k path) ij.1 ij.2)) hh
  refine ⟨B,c,hB,hc,fun n x hx => ?_⟩
  simpa only [entrySize,gramDeviation,predictedGram,Matrix.sub_apply,Matrix.sum_apply,blochOuter,
    ← Finset.sum_sub_distrib,Fintype.sum_prod_type] using ht n x hx

def rawError (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool) (θ : Fin 3 → ℝ)
    (n : ℕ) (path : Path) : Vector := WithLp.toLp 2 (estimate loss ridge refresh n path-θ)

theorem ridge_lower (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool) (n : ℕ) (path : Path) :
    Lower (pathState loss ridge refresh n path).gram ridge := by
  intro x
  rw [pathState_gram,quadratic_add,quadratic_smul,quadratic_one,quadratic_sum]
  simp only [quadratic_outer]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem rawError_of_lower (loss : Loss) (ridge : ℝ) (hr : 0 < ridge) (refresh : ℕ → Bool)
    (θ : Fin 3 → ℝ) (n : ℕ) (path : Path) (c : ℝ) (hc : 0 < c)
    (hG : Lower (pathState loss ridge refresh n path).gram c) :
    ‖rawError loss ridge refresh θ n path‖ ≤
      (‖residualSum (policy loss ridge refresh) θ n path‖+ridge*‖WithLp.toLp 2 θ‖)/c := by
  have hh := CoerciveLeastSquares.norm_le_residual_div _ c hc (lower_to_coercive _ _ hG)
    _ _ (normal_error loss ridge hr refresh θ n path)
  apply hh.trans
  apply div_le_div_of_nonneg_right _ hc.le
  apply (norm_sub_le _ _).trans
  simp only [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
  rfl

theorem rawError_global_bound (loss : Loss) (ridge : ℝ) (hr : 0 < ridge) (refresh : ℕ → Bool)
    (θ : OneQubitPhysicalParameter) (n : ℕ) (path : Path) :
    ‖rawError loss ridge refresh θ.1 n path‖ ≤ (n:ℝ)*6/ridge+‖WithLp.toLp 2 θ.1‖ := by
  apply (rawError_of_lower loss ridge hr refresh θ.1 n path ridge hr (ridge_lower _ _ _ _ _)).trans
  calc
    _ ≤ ((n:ℝ)*6+ridge*‖WithLp.toLp 2 θ.1‖)/ridge :=
      div_le_div_of_nonneg_right (add_le_add (residualSum_bound _ θ n path) (le_refl _)) hr.le
    _ = _ := by field_simp

theorem gram_lower_from_predicted (loss : Loss) (ridge : ℝ) (hr : 0 ≤ ridge) (refresh : ℕ → Bool)
    (n : ℕ) (path : Path) (c : ℝ)
    (hpred : Lower (predictedGram (policy loss ridge refresh) n path) c) :
    Lower (pathState loss ridge refresh n path).gram
      (c-entrySize (gramDeviation (policy loss ridge refresh) n path)) := by
  have hh := lower_perturb _ (gramDeviation (policy loss ridge refresh) n path) c hpred
  intro x
  rw [pathState_gram,quadratic_add,quadratic_smul,quadratic_one]
  have he : predictedGram (policy loss ridge refresh) n path+gramDeviation (policy loss ridge refresh) n path =
      ∑ k ∈ Finset.range n, blochOuter (actualAxis (policy loss ridge refresh) k path) := by
    unfold gramDeviation
    abel
  rw [he] at hh
  exact (hh x).trans (le_add_of_nonneg_left (mul_nonneg hr (normSq_nonneg x)))

theorem bures_lower_of_noise (ridge : ℝ) (hr : 0 ≤ ridge) (refresh : ℕ → Bool)
    (n : ℕ) (path : Path)
    (hb : entrySize (gramDeviation (policy .bures ridge refresh) n path) ≤ (n:ℝ)/6) :
    Lower (pathState .bures ridge refresh n path).gram ((n:ℝ)/6) := by
  have hp : Lower (predictedGram (policy .bures ridge refresh) n path) ((n:ℝ)/3) := by
    intro x
    rw [predictedGram,quadratic_sum]
    have he (k : ℕ) : gram (actualAction (policy .bures ridge refresh) k path) = (1/3:ℝ) • (1:Mat) := by
      rw [action_eq_reference,gram_reference]
      rfl
    simp only [he,quadratic_smul,quadratic_one,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    ring_nf
    exact le_refl _
  exact lower_mono _ _ _ (by linarith only [hb]) (gram_lower_from_predicted .bures ridge hr refresh n path _ hp)

end
end QubitOracle.AdaptiveDesign.P1Weighted
