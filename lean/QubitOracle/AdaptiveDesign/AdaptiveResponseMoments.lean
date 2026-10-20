import QubitOracle.AdaptiveDesign.SubGaussianPowerMoments
import Mathlib.MeasureTheory.Function.L2Space

/-! Uniform polynomial moments of actual finite-outcome adaptive response sums.
The source of the moments is conditional centering and a bounded response,
not an assumed moment bound on the estimator. -/
namespace QubitOracle.AdaptiveDesign.AdaptiveResponseMoments
open Filter MeasureTheory ProbabilityTheory QubitOracle.Paper
open BoundedResponseQuarterRate AdaptiveResponseStrongLaw AdaptiveRidgeConsistency
open SubGaussianPowerMoments
open scoped BigOperators Topology InnerProductSpace ENNReal NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

variable {Ω E F : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

def UniformMoment (μ : Measure Ω) (X : ℕ → Ω → E) (p : ℕ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ n, MemLp (X n) p μ ∧ ∫ ω, ‖X n ω‖^p ∂μ ≤ K

theorem norm_add_pow_le (x y : E) (p : ℕ) :
    ‖x+y‖^p ≤ (2:ℝ)^p*(‖x‖^p+‖y‖^p) := by
  have hm : ‖x‖+‖y‖ ≤ 2*max ‖x‖ ‖y‖ := by
    linarith [le_max_left ‖x‖ ‖y‖, le_max_right ‖x‖ ‖y‖]
  have hp : (max ‖x‖ ‖y‖)^p ≤ ‖x‖^p+‖y‖^p := by
    rcases le_total ‖x‖ ‖y‖ with h | h
    · rw [max_eq_right h]; exact le_add_of_nonneg_left (by positivity)
    · rw [max_eq_left h]; exact le_add_of_nonneg_right (by positivity)
  exact (pow_le_pow_left₀ (norm_nonneg _) ((norm_add_le x y).trans hm) p).trans
    (by rw [mul_pow]; exact mul_le_mul_of_nonneg_left hp (by positivity))

theorem UniformMoment.of_dominated {X : ℕ → Ω → E} (hX : UniformMoment μ X p)
    (Y : ℕ → Ω → F) (hm : ∀ n, AEStronglyMeasurable (Y n) μ)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n ω, ‖Y n ω‖ ≤ C*‖X n ω‖) :
    UniformMoment μ Y p := by
  obtain ⟨K,hK,hX⟩ := hX
  refine ⟨C^p*K, by positivity, fun n => ⟨(hX n).1.of_le_mul (hm n)
    (Eventually.of_forall (hb n)), ?_⟩⟩
  calc
    _ ≤ ∫ ω, C^p*‖X n ω‖^p ∂μ := by
      apply integral_mono_of_nonneg (Eventually.of_forall (fun _ => by positivity))
        ((hX n).1.integrable_norm_pow'.const_mul _) (Eventually.of_forall (fun ω => ?_))
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (hb n ω) p
    _ = C^p*(∫ ω, ‖X n ω‖^p ∂μ) := integral_const_mul _ _
    _ ≤ C^p*K := mul_le_mul_of_nonneg_left (hX n).2 (by positivity)

theorem UniformMoment.add {X Y : ℕ → Ω → E}
    (hX : UniformMoment μ X p) (hY : UniformMoment μ Y p) :
    UniformMoment μ (fun n ω => X n ω+Y n ω) p := by
  obtain ⟨K,hK,hX⟩ := hX
  obtain ⟨L,hL,hY⟩ := hY
  refine ⟨(2:ℝ)^p*(K+L), by positivity, fun n => ⟨(hX n).1.add (hY n).1, ?_⟩⟩
  calc
    _ ≤ ∫ ω, (2:ℝ)^p*(‖X n ω‖^p+‖Y n ω‖^p) ∂μ := by
      apply integral_mono ((hX n).1.add (hY n).1).integrable_norm_pow'
        (((hX n).1.integrable_norm_pow'.add (hY n).1.integrable_norm_pow').const_mul _)
      exact fun ω => norm_add_pow_le _ _ p
    _ = (2:ℝ)^p*((∫ ω, ‖X n ω‖^p ∂μ)+(∫ ω, ‖Y n ω‖^p ∂μ)) := by
      rw [integral_const_mul, integral_add (hX n).1.integrable_norm_pow' (hY n).1.integrable_norm_pow']
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add (hX n).2 (hY n).2) (by positivity)

theorem UniformMoment.norm {X : ℕ → Ω → E} (hX : UniformMoment μ X p) :
    UniformMoment μ (fun n ω => ‖X n ω‖) p := by
  obtain ⟨K,hK,hX⟩ := hX
  exact ⟨K,hK,fun n => ⟨(hX n).1.norm, by simpa only [norm_norm] using (hX n).2⟩⟩

theorem UniformMoment.const_mul {X : ℕ → Ω → ℝ} (hX : UniformMoment μ X p) (c : ℝ) :
    UniformMoment μ (fun n ω => c*X n ω) p := by
  apply hX.of_dominated _ (fun n =>
    ((Classical.choose_spec hX).2 n).1.1.const_mul c) |c| (abs_nonneg c)
  intro n ω
  simp only [norm_mul, Real.norm_eq_abs, le_refl]

theorem UniformMoment.norm_sq_of_four {X : ℕ → Ω → E} (hX : UniformMoment μ X 4) :
    UniformMoment μ (fun n ω => ‖X n ω‖^2) 2 := by
  obtain ⟨K,hK,hX⟩ := hX
  refine ⟨K,hK,fun n => ⟨?_, ?_⟩⟩
  · have ht := (hX n).1.norm_rpow_div 2
    norm_num at ht
    have hdiv : (4:ENNReal)/2 = 2 := by
      symm
      apply (ENNReal.eq_div_iff (by norm_num) (by simp)).mpr
      norm_num
    rw [hdiv] at ht
    exact ht
  · simpa only [norm_pow, norm_norm, ← pow_mul] using (hX n).2


theorem uniformMoment_of_bound (X : ℕ → Ω → E)
    (hm : ∀ n, AEStronglyMeasurable (X n) μ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n ω, ‖X n ω‖ ≤ C) (p : ℕ) : UniformMoment μ X p := by
  refine ⟨C^p, by positivity, fun n => ⟨MemLp.of_bound (hm n) C
    (Eventually.of_forall (hb n)), ?_⟩⟩
  calc
    _ ≤ ∫ _ : Ω, C^p ∂μ := integral_mono_of_nonneg
      (Eventually.of_forall (fun _ => by positivity)) (integrable_const _)
      (Eventually.of_forall (fun ω => pow_le_pow_left₀ (norm_nonneg _) (hb n ω) p))
    _ = _ := by simp

theorem UniformMoment.finite_sum {ι : Type*} (s : Finset ι)
    (X : ι → ℕ → Ω → E) (h : ∀ i ∈ s, UniformMoment μ (X i) p) :
    UniformMoment μ (fun n ω => ∑ i ∈ s, X i n ω) p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact uniformMoment_of_bound _ (fun _ => aestronglyMeasurable_const) 0 (by norm_num)
      (fun _ _ => by simp) p
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (h i (Finset.mem_insert_self _ _)).add
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem boundedMartingale_uniformMoment [StandardBorelSpace Ω]
    (F : Filtration ℕ ‹MeasurableSpace Ω›) (X : ℕ → Ω → ℝ)
    (ha : StronglyAdapted F X) (hz : X 0 = 0)
    (hc : ∀ n, μ[X (n+1) | F n] =ᵐ[μ] 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n ω, ‖X n ω‖ ≤ C) (p : ℕ) :
    UniformMoment μ (fun n ω => (Real.sqrt ((n+1:ℕ):ℝ))⁻¹ *
      ∑ k ∈ Finset.range (n+1), X k ω) p := by
  obtain ⟨c,hc',hsg⟩ := boundedMartingale_sum_subGaussian μ F X ha hz hc C hC hb
  refine ⟨2*(p:ℝ)^p*Real.exp ((c:ℝ)/2), by positivity, fun n => ?_⟩
  have hs : HasSubgaussianMGF
      (fun ω => (Real.sqrt ((n+1:ℕ):ℝ))⁻¹ * ∑ k ∈ Finset.range (n+1), X k ω) c μ := by
    have h := (hsg n).const_mul (Real.sqrt ((n+1:ℕ):ℝ))⁻¹
    convert h using 1
    apply NNReal.eq
    change (c:ℝ) = (Real.sqrt ((n+1:ℕ):ℝ))⁻¹ ^ 2 * (((n+1:ℕ):ℝ)*(c:ℝ))
    rw [inv_pow, Real.sq_sqrt (by positivity)]
    field_simp
  exact ⟨by simpa using hs.memLp (p:ℝ≥0), by simpa [Real.norm_eq_abs] using integral_abs_pow_le hs p⟩

variable {Theta Action Outcome : Type*}
  [MeasurableSpace Action] [MeasurableSpace Outcome]
  [Fintype Outcome] [MeasurableSingletonClass Outcome]
  [StandardBorelSpace Outcome] [Nonempty Outcome]

theorem actualResponse_uniformMoment
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta)
    (g : Action → Outcome → ℝ)
    (hmean : ∀ a, ∫ y, g a y ∂protocol.response theta a = 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ a y, ‖g a y‖ ≤ C) (p : ℕ) :
    UniformMoment (adaptiveInfiniteTrajectoryMeasure protocol theta)
      (fun n path => (Real.sqrt ((n+1:ℕ):ℝ))⁻¹ *
        ∑ k ∈ Finset.range (n+1), actualResponse protocol g k path) p := by
  let μ := adaptiveInfiniteTrajectoryMeasure protocol theta
  let X : ℕ → AdaptiveInfinitePath Outcome → ℝ
    | 0, _ => 0
    | k+1, path => actualResponse protocol g (k+1) path
  have ha : StronglyAdapted MeasureTheory.Filtration.piLE X := by
    intro n
    cases n with
    | zero => exact stronglyMeasurable_const
    | succ n => exact actualResponse_stronglyMeasurable_piLE protocol g (n+1)
  have hc (n : ℕ) : μ[X (n+1) | MeasureTheory.Filtration.piLE n] =ᵐ[μ] 0 :=
    actualResponse_condExp_zero protocol theta g hmean C hb n
  have hbs (n : ℕ) (path : AdaptiveInfinitePath Outcome) : ‖X n path‖ ≤ C := by
    cases n with
    | zero => simpa [X] using hC
    | succ n => exact hb _ _
  have hs := boundedMartingale_uniformMoment (μ:=μ) _ X ha rfl hc C hC hbs p
  have hi : UniformMoment μ
      (fun n path => (Real.sqrt ((n+1:ℕ):ℝ))⁻¹ * actualResponse protocol g 0 path) p := by
    apply uniformMoment_of_bound _ (fun n =>
      (((actualResponse_stronglyMeasurable_piLE protocol g 0).mono
        (MeasureTheory.Filtration.piLE.le 0)).const_mul _).aestronglyMeasurable) C hC
    intro n path
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hsqrt : 1 ≤ Real.sqrt ((n+1:ℕ):ℝ) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      norm_num
    exact (mul_le_mul_of_nonneg_left (hb _ _) (by positivity)).trans
      (mul_le_of_le_one_left hC ((inv_le_one₀ (by positivity)).mpr hsqrt))
  have heq (n : ℕ) (path : AdaptiveInfinitePath Outcome) :
      (∑ k ∈ Finset.range (n+1), X k path)+actualResponse protocol g 0 path =
        ∑ k ∈ Finset.range (n+1), actualResponse protocol g k path := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp [X]
  convert hs.add hi using 1
  funext n path
  rw [← mul_add, heq]

theorem actualVectorResponse_uniformMoment
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta)
    (g : Action → Outcome → E)
    (hmean : ∀ a, ∫ y, g a y ∂protocol.response theta a = 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ a y, ‖g a y‖ ≤ C) (p : ℕ) :
    UniformMoment (adaptiveInfiniteTrajectoryMeasure protocol theta)
      (fun n path => (Real.sqrt ((n+1:ℕ):ℝ))⁻¹ •
        ∑ k ∈ Finset.range (n+1), actualVectorResponse protocol g k path) p := by
  letI : IsMarkovKernel (protocol.response theta) := protocol.response_isMarkov theta
  let b := stdOrthonormalBasis ℝ E
  have hc (i : Fin (Module.finrank ℝ E)) :=
    actualResponse_uniformMoment protocol theta (fun a y => ⟪b i, g a y⟫_ℝ)
      (fun a => by rw [integral_inner Integrable.of_finite, hmean a, inner_zero_right]) C hC
      (fun a y => (norm_inner_le_norm _ _).trans (by simpa [b.norm_eq_one] using hb a y)) p
  have hvec (i : Fin (Module.finrank ℝ E)) : UniformMoment
      (adaptiveInfiniteTrajectoryMeasure protocol theta)
      (fun n path => ((Real.sqrt ((n+1:ℕ):ℝ))⁻¹ *
        ∑ k ∈ Finset.range (n+1), ⟪b i, actualVectorResponse protocol g k path⟫_ℝ) • b i) p := by
    have hm (n : ℕ) := (Classical.choose_spec (hc i)).2 n
    apply (hc i).of_dominated _ (fun n => hm n |>.1.1.smul_const (b i)) 1 (by norm_num)
    intro n path
    simp only [norm_smul, b.norm_eq_one, mul_one, one_mul]
    rfl
  have hs := UniformMoment.finite_sum Finset.univ _ (fun i _ => hvec i)
  simpa only [← inner_sum, ← inner_smul_right, b.sum_repr'] using hs

end
end QubitOracle.AdaptiveDesign.AdaptiveResponseMoments
