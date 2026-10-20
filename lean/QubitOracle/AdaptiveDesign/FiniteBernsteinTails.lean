import Mathlib

namespace QubitOracle.AdaptiveDesign.BoundedVarianceMGF
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem finite_abs_sum_bernstein {I : Type*} [Fintype I]
    (f : I → Ω → ℝ) (V C : ℝ) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (htail : ∀ i x, 0 ≤ x → μ.real {ω | x ≤ |f i ω|} ≤
      2*Real.exp (-(x^2)/(4*(1+C)*(1+V+x)))) (x : ℝ) (hx : 0 ≤ x) :
    μ.real {ω | x ≤ ∑ i, |f i ω|} ≤
      2*((Fintype.card I:ℝ)+1)*Real.exp
        (-(x^2)/(4*(1+C)*((Fintype.card I:ℝ)+1)^2*(1+V+x))) := by
  classical
  let K : ℝ := (Fintype.card I:ℝ)+1
  have hK : 0 < K := by dsimp [K]; positivity
  have hK1 : 1 ≤ K := by dsimp [K]; linarith [Nat.cast_nonneg (Fintype.card I) (α:=ℝ)]
  by_cases hx0 : x=0
  · subst x
    simp only [zero_pow (by norm_num : 2≠0),neg_zero,zero_div,Real.exp_zero,mul_one]
    exact (measureReal_le_one (μ:=μ)).trans (by linarith [Nat.cast_nonneg (Fintype.card I) (α:=ℝ)])
  have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hun : {ω | x ≤ ∑ i, |f i ω|} ⊆ ⋃ i, {ω | x/K ≤ |f i ω|} := by
    intro ω hω
    simp only [Set.mem_iUnion,Set.mem_setOf_eq]
    by_contra hh
    push_neg at hh
    have hs : (∑ i, |f i ω|) ≤ (Fintype.card I:ℝ)*(x/K) := by
      calc
        _ ≤ ∑ _i : I, x/K := Finset.sum_le_sum (fun i _ => (hh i).le)
        _ = _ := by simp
    have hlt : (Fintype.card I:ℝ)*(x/K) < x := by
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ hK).mpr
      dsimp only [K]
      nlinarith only [hxp]
    exact (not_le_of_gt (hs.trans_lt hlt)) hω
  have hexp : -(x/K)^2/(4*(1+C)*(1+V+x/K)) ≤
      -(x^2)/(4*(1+C)*K^2*(1+V+x)) := by
    have hxK : x/K ≤ x := (div_le_self hx hK1)
    have hd : 0 < 4*(1+C)*(1+V+x/K) := by positivity
    have hd' : 4*(1+C)*(1+V+x/K) ≤ 4*(1+C)*(1+V+x) := by nlinarith
    have hh := neg_le_neg (div_le_div_of_nonneg_left (sq_nonneg (x/K)) hd hd')
    calc
      _ ≤ -((x/K)^2/(4*(1+C)*(1+V+x))) := by simpa only [neg_div] using hh
      _ = _ := by field_simp <;> ring
  calc
    _ ≤ μ.real (⋃ i, {ω | x/K ≤ |f i ω|}) := measureReal_mono hun
    _ ≤ ∑ i, μ.real {ω | x/K ≤ |f i ω|} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : I, 2*Real.exp (-(x/K)^2/(4*(1+C)*(1+V+x/K))) :=
      Finset.sum_le_sum (fun i _ => htail i (x/K) (by positivity))
    _ ≤ ∑ _i : I, 2*Real.exp (-(x^2)/(4*(1+C)*K^2*(1+V+x))) :=
      Finset.sum_le_sum (fun _ _ => mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by norm_num))
    _ ≤ _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      change (Fintype.card I:ℝ)*(2*Real.exp _) ≤ 2*K*Real.exp _
      dsimp only [K]
      nlinarith [Real.exp_pos (-(x^2)/(4*(1+C)*((Fintype.card I:ℝ)+1)^2*(1+V+x)))]

theorem euclidean_norm_le_sum_abs {I : Type*} [Fintype I] (x : EuclideanSpace ℝ I) :
    ‖x‖ ≤ ∑ i, |x i| := by
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg (s:=Finset.univ) (fun i _ => abs_nonneg (x i))
  have he := EuclideanSpace.real_norm_sq_eq x
  simp only [sq_abs] at hs
  nlinarith [norm_nonneg x,Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset I)) => abs_nonneg (x i))]


end
end QubitOracle.AdaptiveDesign.BoundedVarianceMGF
