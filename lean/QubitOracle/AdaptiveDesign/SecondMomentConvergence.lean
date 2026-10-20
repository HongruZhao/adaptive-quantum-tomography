import QubitOracle.AdaptiveDesign.ProbabilityCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Mean-square bounds imply convergence in probability by Markov's
inequality. Used with the exploration budget rather than the copy count. -/
namespace QubitOracle.AdaptiveDesign.SecondMomentConvergence
open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
noncomputable section
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem real_tail_bound (f : Ω → ℝ) (hi : Integrable (fun ω => f ω ^ 2) μ)
    (a : ℝ) (ha : ∫ ω, f ω ^ 2 ∂μ ≤ a) (δ : ℝ) (hδ : 0 < δ) :
    μ.real {ω | δ ≤ ‖f ω‖} ≤ a/δ^2 := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ (fun ω => sq_nonneg (f ω))) hi (δ^2)
  have he : {ω | δ^2 ≤ f ω ^ 2} = {ω | δ ≤ ‖f ω‖} := by
    ext ω
    simp only [Set.mem_setOf_eq, Real.norm_eq_abs]
    constructor
    · intro h
      nlinarith [sq_abs (f ω), abs_nonneg (f ω)]
    · intro h
      nlinarith [sq_abs (f ω), abs_nonneg (f ω)]
  rw [he] at hm
  apply (le_div_iff₀ (sq_pos_of_pos hδ)).mpr
  nlinarith

theorem inMeasure_of_secondMoment (f : ℕ → Ω → ℝ) (a : ℕ → ℝ)
    (hi : ∀ n, Integrable (fun ω => f n ω ^ 2) μ)
    (hb : ∀ n, ∫ ω, f n ω ^ 2 ∂μ ≤ a n)
    (ha : Tendsto a atTop (𝓝 0)) :
    TendstoInMeasure μ f atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro δ hδ
  simp only [sub_zero]
  have hr : Tendsto (fun n => μ.real {ω | δ ≤ ‖f n ω‖}) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => measureReal_nonneg)
      (fun n => real_tail_bound μ (f n) (hi n) (a n) (hb n) δ hδ)
    simpa using ha.div_const (δ^2)
  have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr
  have he (n : ℕ) : ENNReal.ofReal (μ.real {ω | δ ≤ ‖f n ω‖}) = μ {ω | δ ≤ ‖f n ω‖} :=
    ofReal_measureReal (by finiteness)
  simpa only [Function.comp_def, ENNReal.ofReal_zero, he] using hh

end
end QubitOracle.AdaptiveDesign.SecondMomentConvergence
