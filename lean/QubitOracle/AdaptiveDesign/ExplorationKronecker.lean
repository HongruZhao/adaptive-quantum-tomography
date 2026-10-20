import Mathlib

/-! Deterministic summation by parts for an arbitrary accumulated budget. -/
namespace QubitOracle.AdaptiveDesign.ExplorationKronecker
open Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1800000

theorem weighted_average_zero (b z : ℕ → ℝ)
    (hb : ∀ n, 0 < b n) (hmono : Monotone b) (hinf : Tendsto b atTop atTop)
    (hz : Tendsto z atTop (𝓝 0)) :
    Tendsto (fun n => (∑ k ∈ Finset.range n, (b (k+1)-b k)*z k)/b n) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K,hK⟩ := (Metric.tendsto_atTop.mp hz) (ε/2) (half_pos hε)
  let C := ∑ k ∈ Finset.range K, (b (k+1)-b k)*|z k|
  have hdiff (k : ℕ) : 0 ≤ b (k+1)-b k := sub_nonneg.mpr (hmono (Nat.le_succ k))
  have hc : 0 ≤ C := Finset.sum_nonneg (fun k _ => mul_nonneg (hdiff k) (abs_nonneg _))
  have hlim : Tendsto (fun n => C / b n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using (tendsto_inv_atTop_zero.comp hinf).const_mul C
  obtain ⟨N,hN⟩ := (Metric.tendsto_atTop.mp hlim) (ε/2) (half_pos hε)
  refine ⟨max N K, ?_⟩
  intro n hn
  have hnK : K ≤ n := (le_max_right N K).trans hn
  have hprefix : ∑ k ∈ Finset.range n, (if k<K then (b (k+1)-b k)*|z k| else 0) = C := by
    rw [← Finset.sum_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hbound : |∑ k ∈ Finset.range n, (b (k+1)-b k)*z k| ≤ C+(ε/2)*b n := by
    calc
      _ ≤ ∑ k ∈ Finset.range n, |(b (k+1)-b k)*z k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range n,
          ((if k<K then (b (k+1)-b k)*|z k| else 0)+(b (k+1)-b k)*(ε/2)) := by
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul, abs_of_nonneg (hdiff k)]
        by_cases hk : k<K
        · simp only [if_pos hk]
          exact le_add_of_nonneg_right (mul_nonneg (hdiff k) (half_pos hε).le)
        · simp only [if_neg hk, zero_add]
          apply mul_le_mul_of_nonneg_left _ (hdiff k)
          have hh := hK k (Nat.le_of_not_gt hk)
          simpa only [Real.dist_eq, sub_zero] using hh.le
      _ = C+(b n-b 0)*(ε/2) := by
        rw [Finset.sum_add_distrib, hprefix, ← Finset.sum_mul, Finset.sum_range_sub]
      _ ≤ C+(ε/2)*b n := by nlinarith [hb 0]
  have hsmall : C/b n < ε/2 := by
    have h := hN n ((le_max_left N K).trans hn)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hc (hb n).le)] at h
    exact h
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (hb n)]
  apply (div_le_div_of_nonneg_right hbound (hb n).le).trans_lt
  rw [add_div, mul_div_cancel_right₀ _ (hb n).ne']
  linarith

lemma summation_by_parts (b s : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, b (k+1)*(s (k+1)-s k) =
      b n*s n-b 0*s 0-∑ k ∈ Finset.range n, (b (k+1)-b k)*s k := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]; ring

/-- Kronecker's lemma in the precise form needed for exploration budgets. -/
theorem normalized_sum_zero (b x : ℕ → ℝ)
    (hb : ∀ n, 0 < b n) (hmono : Monotone b) (hinf : Tendsto b atTop atTop)
    (c : ℝ) (hx : Tendsto (fun n => ∑ k ∈ Finset.range n, x k/b (k+1)) atTop (𝓝 c)) :
    Tendsto (fun n => (∑ k ∈ Finset.range n, x k)/b n) atTop (𝓝 0) := by
  let s := fun n => (∑ k ∈ Finset.range n, x k/b (k+1))-c
  have hs : Tendsto s atTop (𝓝 0) := by simpa [s] using hx.sub_const c
  have ha := weighted_average_zero b s hb hmono hinf hs
  have hzero : Tendsto (fun n => b 0*s 0/b n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hinf).const_mul (b 0*s 0)
  have heq (n : ℕ) : (∑ k ∈ Finset.range n, x k)/b n =
      s n-(b 0*s 0/b n)-(∑ k ∈ Finset.range n, (b (k+1)-b k)*s k)/b n := by
    have h := summation_by_parts b s n
    have hterm (k : ℕ) : b (k+1)*(s (k+1)-s k) = x k := by
      dsimp [s]
      rw [Finset.sum_range_succ]
      field_simp [(hb (k+1)).ne']
      ring
    simp only [hterm] at h
    rw [h]
    field_simp [(hb n).ne']
  simpa only [← heq, sub_zero] using (hs.sub hzero).sub ha

end
end QubitOracle.AdaptiveDesign.ExplorationKronecker
