import QubitOracle.AdaptiveDesign.AdaptiveResponseMoments
import Mathlib.Topology.Order.LiminfLimsup

/-! Transfer of fourth moments from a good-history bound. Exceptional
sets may be replaced by measurable envelopes with the same outer measure. -/
namespace QubitOracle.AdaptiveDesign.AdaptiveResponseMoments
open Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
set_option backward.isDefEq.respectTransparency.types false

theorem UniformMoment.norm_sq_of_eight {X : ℕ → Ω → E} (hX : UniformMoment μ X 8) :
    UniformMoment μ (fun n ω => ‖X n ω‖^2) 4 := by
  obtain ⟨K,hK,hX⟩ := hX
  refine ⟨K,hK,fun n => ⟨?_,?_⟩⟩
  · have ht := (hX n).1.norm_rpow_div 2
    norm_num at ht
    have hdiv : (8:ENNReal)/2 = 4 := by
      symm
      apply (ENNReal.eq_div_iff (by norm_num) (by simp)).mpr
      norm_num
    rw [hdiv] at ht
    exact ht
  · simpa only [norm_pow,norm_norm,← pow_mul] using (hX n).2

theorem moment_of_good_event (p : ℕ) (hp : 0 < p) (Y : ℕ → Ω → E) (X : ℕ → Ω → ℝ)
    (hX : UniformMoment μ X p) (hXp : ∀ n ω, 0 ≤ X n ω)
    (hm : ∀ n, AEStronglyMeasurable (Y n) μ) (bad : ℕ → Set Ω)
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n) (hglobal : ∀ n ω, ‖Y n ω‖ ≤ B n)
    (hgood : ∀ n ω, ω ∉ bad n → ‖Y n ω‖ ≤ X n ω)
    (hprob : ∃ K : ℝ, 0 ≤ K ∧ ∀ n, (B n)^p*μ.real (bad n) ≤ K) :
    UniformMoment μ Y p := by
  classical
  let A := fun n => toMeasurable μ (bad n)
  let Z := fun n => (A n).indicator (fun _ : Ω => B n)
  have hZ : UniformMoment μ Z p := by
    obtain ⟨K,hK,hbound⟩ := hprob
    refine ⟨K,hK,fun n => ⟨(memLp_const (B n)).indicator (measurableSet_toMeasurable _ _),?_⟩⟩
    have he : (fun ω => ‖Z n ω‖^p) = (A n).indicator (fun _ : Ω => (B n)^p) := by
      funext ω
      by_cases hx : ω ∈ A n
      · simp [Z,hx,Real.norm_eq_abs,abs_of_nonneg (hB n)]
      · simp [Z,hx,Nat.ne_of_gt hp]
    rw [he,integral_indicator_const _ (measurableSet_toMeasurable _ _)]
    simpa only [A,smul_eq_mul,measureReal_def,measure_toMeasurable,mul_comm] using hbound n
  apply (hX.add hZ).of_dominated Y hm 1 (by norm_num)
  intro n ω
  have hZp : 0 ≤ Z n ω := Set.indicator_nonneg (fun _ _ => hB n) _
  rw [one_mul,Real.norm_eq_abs,abs_of_nonneg (add_nonneg (hXp n ω) hZp)]
  by_cases hx : ω ∈ A n
  · have he : Z n ω = B n := Set.indicator_of_mem hx _
    rw [he]
    exact (hglobal n ω).trans (le_add_of_nonneg_left (hXp n ω))
  · have he : Z n ω = 0 := Set.indicator_of_notMem hx _
    rw [he,add_zero]
    exact hgood n ω (fun hw => hx (subset_toMeasurable μ (bad n) hw))


theorem fourthMoment_of_good_event (Y : ℕ → Ω → E) (X : ℕ → Ω → ℝ)
    (hX : UniformMoment μ X 4) (hXp : ∀ n ω, 0 ≤ X n ω)
    (hm : ∀ n, AEStronglyMeasurable (Y n) μ) (bad : ℕ → Set Ω)
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n) (hglobal : ∀ n ω, ‖Y n ω‖ ≤ B n)
    (hgood : ∀ n ω, ω ∉ bad n → ‖Y n ω‖ ≤ X n ω)
    (hprob : ∃ K : ℝ, 0 ≤ K ∧ ∀ n, (B n)^4*μ.real (bad n) ≤ K) :
    UniformMoment μ Y 4 := by
  classical
  let A := fun n => toMeasurable μ (bad n)
  let Z := fun n => (A n).indicator (fun _ : Ω => B n)
  have hZ : UniformMoment μ Z 4 := by
    obtain ⟨K,hK,hbound⟩ := hprob
    refine ⟨K,hK,fun n => ⟨(memLp_const (B n)).indicator (measurableSet_toMeasurable _ _),?_⟩⟩
    have he : (fun ω => ‖Z n ω‖^4) = (A n).indicator (fun _ : Ω => (B n)^4) := by
      funext ω
      by_cases hx : ω ∈ A n
      · simp [Z,hx,Real.norm_eq_abs,abs_of_nonneg (hB n)]
      · simp [Z,hx]
    rw [he,integral_indicator_const _ (measurableSet_toMeasurable _ _)]
    simpa only [A,smul_eq_mul,measureReal_def,measure_toMeasurable,mul_comm] using hbound n
  apply (hX.add hZ).of_dominated Y hm 1 (by norm_num)
  intro n ω
  have hZp : 0 ≤ Z n ω := Set.indicator_nonneg (fun _ _ => hB n) _
  rw [one_mul,Real.norm_eq_abs,abs_of_nonneg (add_nonneg (hXp n ω) hZp)]
  by_cases hx : ω ∈ A n
  · have he : Z n ω = B n := Set.indicator_of_mem hx _
    rw [he]
    exact (hglobal n ω).trans (le_add_of_nonneg_left (hXp n ω))
  · have he : Z n ω = 0 := Set.indicator_of_notMem hx _
    rw [he,add_zero]
    exact hgood n ω (fun hw => hx (subset_toMeasurable μ (bad n) hw))

end
end QubitOracle.AdaptiveDesign.AdaptiveResponseMoments
