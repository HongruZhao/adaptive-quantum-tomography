import QubitOracle.AdaptiveDesign.AdaptiveResponseMoments
/-! Integer moment bounds imply every smaller nonnegative real moment. -/
namespace QubitOracle.AdaptiveDesign.AdaptiveResponseMoments
open MeasureTheory Filter
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem rpow_le_one_add_pow (x : ℝ) (hx : 0 ≤ x) (r : ℝ) (hr : 0 ≤ r)
    (p : ℕ) (hp : r ≤ (p:ℝ)) : x^r ≤ 1+x^p := by
  by_cases h : x ≤ 1
  · exact (Real.rpow_le_one hx h hr).trans (le_add_of_nonneg_right (pow_nonneg hx p))
  · have hh := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge h) hp
    simpa only [Real.rpow_natCast] using hh.trans (le_add_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1))

theorem UniformMoment.real_moment {X : ℕ → Ω → E} {p : ℕ} (hX : UniformMoment μ X p)
    (r : ℝ) (hr : 0 ≤ r) (hp : r ≤ (p:ℝ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n,
      Integrable (fun ω => ‖X n ω‖^r) μ ∧ (∫ ω, ‖X n ω‖^r ∂μ) ≤ K := by
  obtain ⟨K,hK,hX⟩ := hX
  refine ⟨1+K,by positivity,fun n => ?_⟩
  have hm := (hX n).1.1.norm.aemeasurable.pow_const r
  have hb (ω : Ω) : ‖X n ω‖^r ≤ 1+‖X n ω‖^p :=
    rpow_le_one_add_pow _ (norm_nonneg _) r hr p hp
  have hi : Integrable (fun ω => ‖X n ω‖^r) μ :=
    (integrable_const (1:ℝ) |>.add (hX n).1.integrable_norm_pow').mono'
      hm.aestronglyMeasurable (Eventually.of_forall (fun ω => by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
        exact hb ω))
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ ω, 1+‖X n ω‖^p ∂μ := integral_mono hi
      ((integrable_const (1:ℝ)).add (hX n).1.integrable_norm_pow') hb
    _ = 1+(∫ ω, ‖X n ω‖^p ∂μ) := by
      rw [integral_add (integrable_const (1:ℝ)) (hX n).1.integrable_norm_pow']
      simp
    _ ≤ _ := by linarith [(hX n).2]

theorem real_moments_of_all_integer {X : ℕ → Ω → E}
    (hX : ∀ p : ℕ, 0 < p → UniformMoment μ X p) (r : ℝ) (hr : 0 ≤ r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n,
      Integrable (fun ω => ‖X n ω‖^r) μ ∧ (∫ ω, ‖X n ω‖^r ∂μ) ≤ K := by
  obtain ⟨p,hp⟩ := exists_nat_gt r
  exact (hX (p+1) (Nat.succ_pos _)).real_moment r hr (by exact_mod_cast hp.le.trans (by norm_num))

end
end QubitOracle.AdaptiveDesign.AdaptiveResponseMoments
