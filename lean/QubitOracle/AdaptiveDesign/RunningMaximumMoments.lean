import QubitOracle.AdaptiveDesign.AdaptiveResponseMoments

/-! Finite-prefix maximum moments from summable exceptional-event
weights. This avoids treating a future-dependent bound as predictable. -/
namespace QubitOracle.AdaptiveDesign.RunningMaximumMoments
open MeasureTheory Filter AdaptiveResponseMoments
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

def running (C : ℝ) (X : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0, _ => C
  | n+1, ω => max (running C X n ω) (X n ω)

theorem base_le (C : ℝ) (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : C ≤ running C X n ω := by
  induction n with
  | zero => exact le_refl _
  | succ n ih => exact ih.trans (le_max_left _ _)

theorem term_le (C : ℝ) (X : ℕ → Ω → ℝ) (n k : ℕ) (hk : k<n) (ω : Ω) :
    X k ω ≤ running C X n ω := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hkn : k=n
    · subst k; exact le_max_right _ _
    · exact (ih (by omega)).trans (le_max_left _ _)

theorem measurable (C : ℝ) (X : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (X n)) (n : ℕ) :
    Measurable (running C X n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact ih.max (hm n)

theorem moment (C : ℝ) (hC : 0 ≤ C) (X : ℕ → Ω → ℝ)
    (hm : ∀ n, Measurable (X n)) (hX : ∀ n ω, 0 ≤ X n ω)
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n) (hbound : ∀ n ω, X n ω ≤ B n)
    (bad : ℕ → Set Ω) (hgood : ∀ n ω, ω ∉ bad n → X n ω ≤ C)
    (p : ℕ) (hs : Summable (fun n => (B n)^p*μ.real (bad n))) :
    UniformMoment μ (running C X) p := by
  classical
  let A := fun n => toMeasurable μ (bad n)
  let F := fun n => (A n).indicator (fun _ : Ω => (B n)^p)
  have hF (n : ℕ) : Integrable (F n) μ :=
    (integrable_const _).indicator (measurableSet_toMeasurable _ _)
  have hFp (n : ℕ) (ω : Ω) : 0 ≤ F n ω :=
    Set.indicator_nonneg (fun _ _ => pow_nonneg (hB n) p) _
  have hstep (n : ℕ) (ω : Ω) : (running C X (n+1) ω)^p ≤ (running C X n ω)^p+F n ω := by
    have hr : 0 ≤ running C X n ω := hC.trans (base_le C X n ω)
    by_cases hx : X n ω ≤ running C X n ω
    · rw [running,max_eq_left hx]
      exact le_add_of_nonneg_right (hFp n ω)
    · rw [running,max_eq_right (not_le.mp hx).le]
      have hbad : ω ∈ bad n := by
        by_contra hh
        exact hx ((hgood n ω hh).trans (base_le C X n ω))
      have he : F n ω = (B n)^p := Set.indicator_of_mem (subset_toMeasurable μ (bad n) hbad) _
      rw [he]
      exact (pow_le_pow_left₀ (hX n ω) (hbound n ω) p).trans (le_add_of_nonneg_left (by positivity))
  have hpw (n : ℕ) (ω : Ω) : (running C X n ω)^p ≤ C^p+∑ k ∈ Finset.range n, F k ω := by
    induction n with
    | zero => simp [running]
    | succ n ih =>
      rw [Finset.sum_range_succ]
      exact (hstep n ω).trans (by linarith only [ih])
  have hbounded (n : ℕ) (ω : Ω) : running C X n ω ≤ C+∑ k ∈ Finset.range n, B k := by
    induction n with
    | zero => simp [running]
    | succ n ih =>
      rw [running,Finset.sum_range_succ]
      apply max_le
      · linarith only [ih,hB n]
      · exact (hbound n ω).trans (by
          have hh := Finset.sum_nonneg (fun k (_ : k ∈ Finset.range n) => hB k)
          linarith only [hC,hh])
  refine ⟨C^p+∑' k, (B k)^p*μ.real (bad k),
    add_nonneg (pow_nonneg hC p)
      (tsum_nonneg (fun k => mul_nonneg (pow_nonneg (hB k) p) measureReal_nonneg)),
    fun n => ⟨?_,?_⟩⟩
  · exact MemLp.of_bound (measurable C X hm n).aestronglyMeasurable (C+∑ k ∈ Finset.range n, B k)
      (Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs,abs_of_nonneg (hC.trans (base_le C X n ω))]
        exact hbounded n ω))
  · calc
      _ ≤ ∫ ω, C^p+∑ k ∈ Finset.range n, F k ω ∂μ := by
        apply integral_mono_of_nonneg (Eventually.of_forall (fun _ => by positivity))
          ((integrable_const _).add (integrable_finset_sum _ (fun k _ => hF k)))
          (Eventually.of_forall (fun ω => ?_))
        rw [Real.norm_eq_abs,abs_of_nonneg (hC.trans (base_le C X n ω))]
        exact hpw n ω
      _ = C^p+∑ k ∈ Finset.range n, (B k)^p*μ.real (bad k) := by
        rw [integral_add (integrable_const _) (integrable_finset_sum _ (fun k _ => hF k)),integral_const,
          integral_finset_sum _ (fun k _ => hF k)]
        simp only [F,integral_indicator_const _ (measurableSet_toMeasurable _ _),
          A,smul_eq_mul,measureReal_def,measure_toMeasurable,measure_univ,ENNReal.toReal_one,
          one_mul,mul_comm,mul_one]
      _ ≤ _ := add_le_add (le_refl _) (hs.sum_le_tsum _
        (fun k _ => mul_nonneg (pow_nonneg (hB k) p) measureReal_nonneg))

end
end QubitOracle.AdaptiveDesign.RunningMaximumMoments
