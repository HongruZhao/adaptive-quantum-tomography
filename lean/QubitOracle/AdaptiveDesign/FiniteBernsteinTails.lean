import QubitOracle.AdaptiveDesign.MartingaleBernstein

namespace QubitOracle.AdaptiveDesign.BoundedVarianceMGF
open MeasureTheory ProbabilityTheory Filter BoundedMartingaleSecondMoment
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

theorem vector_bernstein {I : Type*} [Fintype I]
    (F : Filtration ℕ mΩ) (X : ℕ → Ω → EuclideanSpace ℝ I)
    (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hc : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n ω, ‖X n ω‖ ≤ C)
    (v : ℕ → ℝ) (hv : ∀ n, ∀ᵐ ω ∂μ, μ[fun ω => ‖X n ω‖^2 | F n] ω ≤ v n)
    (n : ℕ) (V : ℝ) (hV : 0 ≤ V) (hbudget : ∑ k ∈ Finset.range n, v k ≤ V)
    (x : ℝ) (hx : 0 ≤ x) :
    μ.real {ω | x ≤ ‖∑ k ∈ Finset.range n, X k ω‖} ≤
      2*((Fintype.card I:ℝ)+1)*Real.exp
        (-(x^2)/(4*(1+C)*((Fintype.card I:ℝ)+1)^2*(1+V+x))) := by
  have hai (i : I) (k : ℕ) : StronglyMeasurable[F (k+1)] (fun ω => X k ω i) :=
    (EuclideanSpace.proj i).continuous.comp_stronglyMeasurable (ha k)
  have hib (i : I) (k : ℕ) (ω : Ω) : ‖X k ω i‖ ≤ C :=
    (PiLp.norm_apply_le (X k ω) i).trans (hb k ω)
  have hi (k : ℕ) : Integrable (X k) μ := Integrable.of_bound
    ((ha k).mono (F.le (k+1))).aestronglyMeasurable C (Eventually.of_forall (hb k))
  have hci (i : I) (k : ℕ) : μ[(fun ω => X k ω i) | F k] =ᵐ[μ] 0 := by
    have he := (EuclideanSpace.proj i).comp_condExp_comm (m:=F k) (hi k)
    filter_upwards [he,hc k] with ω heω hcω
    simpa [Function.comp_def,hcω] using heω.symm
  have hvi (i : I) (k : ℕ) :
      ∀ᵐ ω ∂μ, μ[fun ω => (X k ω i)^2 | F k] ω ≤ v k := by
    have hleft : Integrable (fun ω => (X k ω i)^2) μ := Integrable.of_bound
      (((hai i k).mono (F.le (k+1))).pow 2).aestronglyMeasurable (C^2)
      (Eventually.of_forall (fun ω => by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hib i k ω) 2))
    have hright : Integrable (fun ω => ‖X k ω‖^2) μ := Integrable.of_bound
      (((ha k).mono (F.le (k+1))).norm.pow 2).aestronglyMeasurable (C^2)
      (Eventually.of_forall (fun ω => by rw [norm_pow,norm_norm]; exact pow_le_pow_left₀ (norm_nonneg _) (hb k ω) 2))
    have hm := condExp_mono (m:=F k) hleft hright (Eventually.of_forall (fun ω => by
      have hh := pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le (X k ω) i) 2
      simpa only [Real.norm_eq_abs,sq_abs] using hh))
    filter_upwards [hm,hv k] with ω hmω hvω
    exact hmω.trans hvω
  have ht := finite_abs_sum_bernstein (μ:=μ)
    (fun i ω => partialSum (fun k ω => X k ω i) n ω) V C hV hC
    (fun i t ht => bernstein_abs F _ (hai i) (hci i) C hC (hib i) v (hvi i) n V hV hbudget t ht) x hx
  apply (measureReal_mono ?_).trans ht
  intro ω hω
  change x ≤ ‖∑ k ∈ Finset.range n, X k ω‖ at hω
  change x ≤ ∑ i, |partialSum (fun k ω => X k ω i) n ω|
  apply hω.trans
  simpa only [partialSum,WithLp.ofLp_sum,Finset.sum_apply] using
    euclidean_norm_le_sum_abs (∑ k ∈ Finset.range n, X k ω)

end
end QubitOracle.AdaptiveDesign.BoundedVarianceMGF
