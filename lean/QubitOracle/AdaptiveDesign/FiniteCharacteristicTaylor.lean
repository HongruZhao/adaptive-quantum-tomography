import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Analysis.Complex.Exponential

/-! Elementary uniform characteristic-function remainders for bounded finite
experiments. This is the analytic ingredient for a direct bounded-response CLT. -/
namespace QubitOracle.AdaptiveDesign.FiniteCharacteristicTaylor
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

def phase (x : ℝ) : ℂ := Complex.exp ((x:ℂ)*Complex.I)

theorem phase_norm (x : ℝ) : ‖phase x‖ = 1 := by
  simp [phase,Complex.norm_exp]

theorem phase_add (x y : ℝ) : phase (x+y) = phase x * phase y := by
  simp [phase,add_mul,Complex.exp_add]

theorem phase_zero : phase 0 = 1 := by simp [phase]

theorem phase_taylor (x : ℝ) :
    ‖phase x - (1+(x:ℂ)*Complex.I-(x:ℂ)^2/2)‖ ≤ |x|^3*Real.exp |x| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp ((x:ℂ)*Complex.I) 3
  have he : (∑ m ∈ Finset.range 3, (((x:ℂ)*Complex.I)^m)/(m.factorial:ℂ)) =
      1+(x:ℂ)*Complex.I-(x:ℂ)^2/2 := by
    norm_num [Finset.sum_range_succ,mul_pow,Complex.I_sq]
    ring
  rw [he] at h
  simpa [phase,norm_mul,Complex.norm_real,Real.norm_eq_abs] using h

variable {O : Type*} [Fintype O]

theorem finite_centered_taylor (p g : O → ℝ) (hp : ∀ y, 0 ≤ p y) (hs : ∑ y, p y = 1)
    (hm : ∑ y, p y*g y = 0) (C : ℝ) (hC : 0 ≤ C) (hg : ∀ y, |g y| ≤ C) (u : ℝ) :
    ‖(∑ y, (p y:ℂ)*phase (u*g y)) - (1-(u:ℂ)^2*(∑ y, (p y:ℂ)*(g y:ℂ)^2)/2)‖ ≤
      |u|^3*C^3*Real.exp (|u| * C) := by
  have hpoly : (∑ y, (p y:ℂ)*(1+(u*g y:ℝ)*Complex.I-(u*g y:ℝ)^2/2)) =
      1-(u:ℂ)^2*(∑ y, (p y:ℂ)*(g y:ℂ)^2)/2 := by
    have hs' : (∑ y, (p y:ℂ)) = 1 := by exact_mod_cast hs
    have hm' : (∑ y, (p y:ℂ)*(g y:ℂ)) = 0 := by exact_mod_cast hm
    simp_rw [Complex.ofReal_mul,mul_sub,mul_add,mul_one]
    rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,hs']
    have hlin : (∑ y, (p y:ℂ)*((u:ℂ)*(g y:ℂ)*Complex.I)) = 0 := by
      calc
        _ = (u:ℂ)*Complex.I * (∑ y, (p y:ℂ)*(g y:ℂ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intros
          ring
        _ = 0 := by rw [hm']; ring
    rw [hlin,add_zero]
    congr 1
    rw [Finset.mul_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intros
    ring
  rw [← hpoly,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ y, ‖(p y:ℂ)*phase (u*g y)-(p y:ℂ)*(1+(u*g y:ℝ)*Complex.I-(u*g y:ℝ)^2/2)‖ := norm_sum_le _ _
    _ ≤ ∑ y, p y*(|u|^3*C^3*Real.exp (|u| * C)) := by
      apply Finset.sum_le_sum
      intro y _
      rw [← mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hp y)]
      apply mul_le_mul_of_nonneg_left _ (hp y)
      refine (phase_taylor (u*g y)).trans ?_
      have hh : |u*g y| ≤ |u| * C := by rw [abs_mul]; gcongr; exact hg y
      calc
        _ ≤ (|u| * C)^3 * Real.exp (|u| * C) := by gcongr
        _ = _ := by ring
    _ = _ := by rw [← Finset.sum_mul,hs,one_mul]

end
end QubitOracle.AdaptiveDesign.FiniteCharacteristicTaylor
