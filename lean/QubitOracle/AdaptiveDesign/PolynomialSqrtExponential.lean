import Mathlib.Topology.Order.LiminfLimsup
import QubitOracle.AdaptiveDesign.ExplorationRate
namespace QubitOracle.AdaptiveDesign.PolynomialSqrtExponential
open Filter
open scoped Topology BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

theorem tendsto_zero (c : ℝ) (hc : 0 < c) (p : ℕ) :
    Tendsto (fun n : ℕ => ((n:ℝ)+1)^p*Real.exp (-c*Real.sqrt ((n:ℝ)+1))) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => Real.sqrt ((n:ℝ)+1)) atTop atTop := by
    simp only [Real.sqrt_eq_rpow]
    exact (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/2)).comp
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((2*p:ℕ):ℝ) c hc).comp ht
  have he (n : ℕ) : Real.sqrt ((n:ℝ)+1)^(2*p) = ((n:ℝ)+1)^p := by
    rw [pow_mul,Real.sq_sqrt (by positivity)]
  simpa only [Function.comp_def,Real.rpow_natCast,he] using hh

theorem summable (c : ℝ) (hc : 0 < c) (p : ℕ) :
    Summable (fun n : ℕ => ((n:ℝ)+1)^p*Real.exp (-c*Real.sqrt ((n:ℝ)+1))) := by
  obtain ⟨K,hK⟩ := (tendsto_zero (c/2) (by positivity) p).bddAbove_range
  have hs : Summable (fun n : ℕ => max K 0*Real.exp (-(c/2)*Real.sqrt ((n:ℝ)+1))) := by
    simpa only [Real.sqrt_eq_rpow] using
      (ExplorationRate.summable_exp_neg_sqrt (c/2) (by positivity)).mul_left (max K 0)
  apply hs.of_nonneg_of_le (fun _ => by positivity)
  intro n
  have hh := mul_le_mul_of_nonneg_right ((hK (Set.mem_range_self n)).trans (le_max_left K 0))
    (Real.exp_pos (-(c/2)*Real.sqrt ((n:ℝ)+1))).le
  calc
    _ = (((n:ℝ)+1)^p*Real.exp (-(c/2)*Real.sqrt ((n:ℝ)+1)))*
        Real.exp (-(c/2)*Real.sqrt ((n:ℝ)+1)) := by
      rw [mul_assoc,← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := hh

theorem summable_of_tail (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (B c : ℝ) (hB : 0 ≤ B) (hc : 0 < c)
    (ht : ∀ᶠ n in atTop, f n ≤ B*Real.exp (-c*Real.sqrt ((n:ℝ)+1))) (p : ℕ) :
    Summable (fun n : ℕ => ((n:ℝ)+1)^p*f n) := by
  apply summable_of_isBigO_nat ((summable c hc p).mul_left B)
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [ht] with n hn
  have hfn := hf n
  simp only [Real.norm_eq_abs,abs_of_nonneg (show 0≤((n:ℝ)+1)^p*f n by positivity),
    abs_of_nonneg (show 0≤B*(((n:ℝ)+1)^p*Real.exp (-c*Real.sqrt ((n:ℝ)+1))) by positivity),one_mul]
  nlinarith only [mul_le_mul_of_nonneg_left hn (show (0:ℝ)≤((n:ℝ)+1)^p by positivity)]

end
end QubitOracle.AdaptiveDesign.PolynomialSqrtExponential
