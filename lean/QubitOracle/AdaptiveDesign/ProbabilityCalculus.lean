import Mathlib.Analysis.Normed.Operator.Bilinear
import QubitOracle.AdaptiveDesign.ProbabilityZeroAlgebra
/-! Elementary probability calculus for the estimator remainder argument.
Every result follows from the definition of convergence in measure. -/

namespace QubitOracle.AdaptiveDesign.ProbabilityCalculus

open Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

variable {Ω J E F G : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {l : Filter J}

theorem continuousAt_const [PseudoMetricSpace E] [PseudoMetricSpace F]
    {f : J → Ω → E} {x : E} (hf : TendstoInMeasure μ f l (fun _ => x))
    {φ : E → F} (hφ : ContinuousAt φ x) :
    TendstoInMeasure μ (fun n ω => φ (f n ω)) l (fun _ => φ x) := by
  rw [tendstoInMeasure_iff_dist] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hφδ⟩ := Metric.continuousAt_iff.mp hφ ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hf δ hδ) (fun _ => bot_le)
  intro n
  apply measure_mono
  intro ω hω
  by_contra hclose
  exact (not_lt_of_ge hω) (hφδ (lt_of_not_ge hclose))

theorem norm_zero [SeminormedAddCommGroup E] {f : J → Ω → E}
    (hf : TendstoInMeasure μ f l (fun _ => 0)) :
    TendstoInMeasure μ (fun n ω => ‖f n ω‖) l (fun _ => 0) := by
  apply ProbabilityZeroAlgebra.dominated hf 1 (by norm_num)
  intro n ω
  simp

/-- Eventual deterministic tail bounds, also called boundedness in probability. -/
def TightNorm [SeminormedAddCommGroup E] (μ : Measure Ω) (f : J → Ω → E)
    (l : Filter J) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n in l, μ {ω | C ≤ ‖f n ω‖} ≤ ε

theorem tight_of_zero [SeminormedAddCommGroup E] {f : J → Ω → E}
    (hf : TendstoInMeasure μ f l (fun _ => 0)) : TightNorm μ f l := by
  rw [tendstoInMeasure_iff_norm] at hf
  intro ε hε
  refine ⟨1, by norm_num, ?_⟩
  simpa only [sub_zero] using (hf 1 (by norm_num)).eventually (Iio_mem_nhds hε) |>.mono
    (fun _ h => h.le)

theorem tight_uniform_bound [SeminormedAddCommGroup E] {f : J → Ω → E}
    (C : ℝ) (hb : ∀ n ω, ‖f n ω‖ ≤ C) : TightNorm μ f l := by
  intro ε hε
  refine ⟨|C|+1, by positivity, Eventually.of_forall fun n => ?_⟩
  have heq : {ω | |C|+1 ≤ ‖f n ω‖} = ∅ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hω
    linarith [hb n ω, le_abs_self C]
  rw [heq, measure_empty]
  exact bot_le

theorem tight_dominated [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    {f : J → Ω → E} {g : J → Ω → F} (hf : TightNorm μ f l)
    (C : ℝ) (hC : 0 < C) (hb : ∀ n ω, ‖g n ω‖ ≤ C * ‖f n ω‖) :
    TightNorm μ g l := by
  intro ε hε
  obtain ⟨B,hB,ht⟩ := hf ε hε
  refine ⟨C*B, mul_pos hC hB, ?_⟩
  filter_upwards [ht] with n hn
  apply le_trans (measure_mono ?_) hn
  intro ω hω
  exact (mul_le_mul_iff_right₀ hC).mp (hω.trans (hb n ω))

theorem tight_add [SeminormedAddCommGroup E] {f g : J → Ω → E}
    (hf : TightNorm μ f l) (hg : TightNorm μ g l) :
    TightNorm μ (fun n ω => f n ω + g n ω) l := by
  intro ε hε
  have hhalf : (0 : ℝ≥0∞) < ε/2 := ENNReal.div_pos hε.ne' (by simp)
  obtain ⟨B,hB,hfB⟩ := hf (ε/2) hhalf
  obtain ⟨C,hC,hgC⟩ := hg (ε/2) hhalf
  refine ⟨B+C, add_pos hB hC, ?_⟩
  filter_upwards [hfB,hgC] with n hn hn'
  calc
    _ ≤ μ ({ω | B ≤ ‖f n ω‖} ∪ {ω | C ≤ ‖g n ω‖}) := by
      apply measure_mono
      intro ω hω
      change B+C ≤ ‖f n ω + g n ω‖ at hω
      by_cases h : B ≤ ‖f n ω‖
      · exact Or.inl h
      · right
        by_contra h'
        change ¬ C ≤ ‖g n ω‖ at h'
        have hb := norm_add_le (f n ω) (g n ω)
        have h1 := lt_of_not_ge h
        have h2 := lt_of_not_ge h'
        linarith
    _ ≤ μ {ω | B ≤ ‖f n ω‖} + μ {ω | C ≤ ‖g n ω‖} := measure_union_le _ _
    _ ≤ ε/2 + ε/2 := add_le_add hn hn'
    _ = ε := ENNReal.add_halves ε

theorem tight_finite_sum [SeminormedAddCommGroup E] {R : Type*} (s : Finset R)
    (f : R → J → Ω → E) (hf : ∀ r ∈ s, TightNorm μ (f r) l) :
    TightNorm μ (fun n ω => ∑ r ∈ s, f r n ω) l := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (tight_uniform_bound (μ := μ) (l := l) 0
      (fun _ _ => (show ‖(0 : E)‖ ≤ 0 by simp)))
  | @insert r s hr ih =>
    simpa only [Finset.sum_insert hr] using tight_add
      (hf r (Finset.mem_insert_self _ _)) (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- A small factor times a tight factor is negligible. This also covers
random linear operators through their operator-norm inequality. -/
theorem product_bound_zero [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [SeminormedAddCommGroup G] {f : J → Ω → E} {g : J → Ω → F} {z : J → Ω → G}
    (hf : TendstoInMeasure μ f l (fun _ => 0)) (hg : TightNorm μ g l)
    (hb : ∀ n ω, ‖z n ω‖ ≤ ‖f n ω‖ * ‖g n ω‖) :
    TendstoInMeasure μ z l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm] at hf ⊢
  simp only [sub_zero] at hf ⊢
  intro δ hδ
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have hhalf : (0 : ℝ≥0∞) < ε/2 := ENNReal.div_pos hε.ne' (by simp)
  obtain ⟨C, hC, ht⟩ := hg (ε/2) hhalf
  have hs := (hf (δ/C) (div_pos hδ hC)).eventually (Iio_mem_nhds
    hhalf)
  filter_upwards [ht, hs] with n hn hn'
  calc
    μ {ω | δ ≤ ‖z n ω‖} ≤
        μ ({ω | δ/C ≤ ‖f n ω‖} ∪ {ω | C ≤ ‖g n ω‖}) := by
      apply measure_mono
      intro ω hω
      by_cases h : δ/C ≤ ‖f n ω‖
      · exact Or.inl h
      · right
        by_contra h'
        have hf' : ‖f n ω‖ * C < δ := (lt_div_iff₀ hC).mp (lt_of_not_ge h)
        have hg' : ‖f n ω‖ * ‖g n ω‖ ≤ ‖f n ω‖ * C :=
          mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge h')) (norm_nonneg _)
        exact (not_lt_of_ge hω) ((hb n ω).trans hg' |>.trans_lt hf')
    _ ≤ μ {ω | δ/C ≤ ‖f n ω‖} + μ {ω | C ≤ ‖g n ω‖} := measure_union_le _ _
    _ ≤ ε/2 + ε/2 := add_le_add hn'.le hn
    _ = ε := ENNReal.add_halves ε

theorem mul_zero {f g : J → Ω → ℝ}
    (hf : TendstoInMeasure μ f l (fun _ => 0))
    (hg : TendstoInMeasure μ g l (fun _ => 0)) :
    TendstoInMeasure μ (fun n ω => f n ω * g n ω) l (fun _ => 0) :=
  product_bound_zero hf (tight_of_zero hg) (fun n ω => (norm_mul _ _).le)

theorem square_norm_zero [SeminormedAddCommGroup E] {f : J → Ω → E}
    (hf : TendstoInMeasure μ f l (fun _ => 0)) :
    TendstoInMeasure μ (fun n ω => ‖f n ω‖ ^ 2) l (fun _ => 0) := by
  simpa only [pow_two] using mul_zero (norm_zero hf) (norm_zero hf)

theorem clm_apply_zero [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A : J → Ω → E →L[ℝ] F} {x : J → Ω → E}
    (hA : TendstoInMeasure μ A l (fun _ => 0)) (hx : TightNorm μ x l) :
    TendstoInMeasure μ (fun n ω => A n ω (x n ω)) l (fun _ => 0) :=
  product_bound_zero hA hx (fun n ω => (A n ω).le_opNorm (x n ω))

/-- A path-dependent finite number of exceptional observations is harmless.
The bound need only hold eventually on almost every path, and its random
constant need not be selected as a measurable function. -/
theorem of_eventual_ae_bound [IsFiniteMeasure μ] [NormedAddCommGroup E]
    {f : ℕ → Ω → E} {g : ℕ → Ω → ℝ} {a : ℕ → ℝ} (C : ℝ)
    (hm : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg : TendstoInMeasure μ g atTop (fun _ => 0)) (ha : Tendsto a atTop (𝓝 0))
    (hb : ∀ᵐ ω ∂μ, ∃ B : ℝ, ∀ᶠ n in atTop, ‖f n ω‖ ≤ C * |g n ω| + |a n| * B) :
    TendstoInMeasure μ f atTop (fun _ => 0) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff hm).mpr
  intro ns hns
  obtain ⟨ms,hms,hgms⟩ := (hg.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms,hms,?_⟩
  filter_upwards [hb,hgms] with ω hω hlim
  obtain ⟨B,hB⟩ := hω
  have hsub := hns.tendsto_atTop.comp hms.tendsto_atTop
  have hupper : Tendsto (fun k => C * |g (ns (ms k)) ω| + |a (ns (ms k))| * B)
      atTop (𝓝 0) := by
    simpa using (hlim.abs.const_mul C).add ((ha.comp hsub).abs.mul_const B)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (hsub.eventually hB) hupper

end
end QubitOracle.AdaptiveDesign.ProbabilityCalculus
