import QubitOracle.AdaptiveDesign.AdaptiveResponseMoments
import QubitOracle.AdaptiveDesign.AdaptiveResponseStrongLaw
import QubitOracle.AdaptiveDesign.BoundedResponseQuarterRate
import QubitOracle.AdaptiveDesign.BoundedVarianceMGF
import QubitOracle.Paper.AdaptiveTrajectoryExperiment
/-! Gaussian tails for bounded centered adaptive scalar responses,
including the initial observation. No independence of selected actions. -/
namespace QubitOracle.AdaptiveDesign.AdaptiveGaussianTails
open QubitOracle.Paper Filter MeasureTheory ProbabilityTheory
open AdaptiveResponseStrongLaw AdaptiveRidgeConsistency BoundedResponseQuarterRate
open scoped BigOperators Topology NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

theorem twoSided_of_mgf {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hm : AEStronglyMeasurable X μ) (R : ℝ) (hb : ∀ ω, ‖X ω‖ ≤ R)
    (A V : ℝ) (hV : 0 < V)
    (hmgf : ∀ t : ℝ, (∫ ω, Real.exp (t*X ω) ∂μ) ≤ Real.exp (A+V*t^2/2))
    (x : ℝ) (hx : 0 ≤ x) :
    μ.real {ω | x ≤ |X ω|} ≤ 2*Real.exp A*Real.exp (-x^2/(2*V)) := by
  let t := x/V
  have ht : 0 ≤ t := div_nonneg hx hV.le
  have htail (s : ℝ) (hs : s=1 ∨ s= -1) :
      μ.real {ω | x ≤ s*X ω} ≤ Real.exp (A-x^2/(2*V)) := by
    have hi : Integrable (fun ω => Real.exp (t*(s*X ω))) μ := by
      have hh := (BoundedVarianceMGF.exp_memLp X hm R hb (t*s) 1).integrable le_rfl
      simpa only [mul_assoc] using hh
    have hh := measure_ge_le_exp_mul_mgf (μ:=μ) (X:=fun ω => s*X ω) x ht hi
    have hmg := hmgf (t*s)
    have hs2 : s^2=1 := by rcases hs with rfl|rfl <;> norm_num
    calc
      _ ≤ Real.exp (-t*x)*(∫ ω, Real.exp ((t*s)*X ω) ∂μ) := by simpa only [mgf,mul_assoc] using hh
      _ ≤ Real.exp (-t*x)*Real.exp (A+V*(t*s)^2/2) :=
        mul_le_mul_of_nonneg_left hmg (Real.exp_pos _).le
      _ = _ := by
        rw [← Real.exp_add,mul_pow,hs2,mul_one]
        congr 1
        dsimp only [t]
        field_simp
        ring
  have hp := htail 1 (Or.inl rfl)
  have hn := htail (-1) (Or.inr rfl)
  have hun : {ω | x ≤ |X ω|} ⊆ {ω | x ≤ 1*X ω} ∪ {ω | x ≤ (-1)*X ω} := by
    intro ω hω
    simpa only [Set.mem_union,Set.mem_setOf_eq,one_mul,neg_one_mul,le_abs] using hω
  calc
    _ ≤ μ.real ({ω | x ≤ 1*X ω} ∪ {ω | x ≤ (-1)*X ω}) := measureReal_mono hun
    _ ≤ μ.real {ω | x ≤ 1*X ω}+μ.real {ω | x ≤ (-1)*X ω} := measureReal_union_le _ _
    _ ≤ 2*Real.exp (A-x^2/(2*V)) := by linarith only [hp,hn]
    _ = _ := by rw [Real.exp_sub,div_eq_mul_inv,← Real.exp_neg]; ring

theorem scalar
    {Theta Action Outcome : Type*}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [Fintype Outcome] [MeasurableSingletonClass Outcome]
    [StandardBorelSpace Outcome] [Nonempty Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta)
    (g : Action → Outcome → ℝ)
    (hmean : ∀ a, ∫ y, g a y ∂protocol.response theta a = 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ a y, ‖g a y‖ ≤ C) :
    ∃ B c : ℝ, 0 < B ∧ 0 < c ∧ ∀ (n : ℕ) (x : ℝ), 0 ≤ x →
      (adaptiveInfiniteTrajectoryMeasure protocol theta).real
        {path | x ≤ |∑ k ∈ Finset.range (n+1), actualResponse protocol g k path|} ≤
      B*Real.exp (-c*x^2/((n+1:ℕ):ℝ)) := by
  let μ := adaptiveInfiniteTrajectoryMeasure protocol theta
  let X : ℕ → AdaptiveInfinitePath Outcome → ℝ
    | 0, _ => 0
    | k+1, path => actualResponse protocol g (k+1) path
  have ha : StronglyAdapted Filtration.piLE X := by
    intro n
    cases n with
    | zero => exact stronglyMeasurable_const
    | succ n => exact actualResponse_stronglyMeasurable_piLE protocol g (n+1)
  have hc (n : ℕ) : μ[X (n+1) | Filtration.piLE n] =ᵐ[μ] 0 :=
    actualResponse_condExp_zero protocol theta g hmean C hb n
  have hbound (n : ℕ) (path : AdaptiveInfinitePath Outcome) : ‖X n path‖ ≤ C := by
    cases n with
    | zero => simpa [X] using hC
    | succ n => exact hb _ _
  obtain ⟨c,hcpos,hsg⟩ := boundedMartingale_sum_subGaussian μ Filtration.piLE X ha rfl hc C hC hbound
  let V := (c:ℝ)+1
  have hV : 0 < V := by dsimp [V]; positivity
  refine ⟨2*Real.exp (C^2/2),(2*V)⁻¹,by positivity,by positivity,fun n x hx => ?_⟩
  let S := fun path => ∑ k ∈ Finset.range (n+1), actualResponse protocol g k path
  have hm : AEStronglyMeasurable S μ := by
    have hh : AEStronglyMeasurable (∑ k ∈ Finset.range (n+1), actualResponse protocol g k) μ :=
      Finset.aestronglyMeasurable_sum _ (fun k _ =>
        ((actualResponse_stronglyMeasurable_piLE protocol g k).mono (Filtration.piLE.le k)).aestronglyMeasurable)
    convert hh using 1
    funext path
    simp [S]
  have hbS (path : AdaptiveInfinitePath Outcome) : ‖S path‖ ≤ ((n+1:ℕ):ℝ)*C := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _k ∈ Finset.range (n+1), C := Finset.sum_le_sum (fun k _ => hb _ _)
      _ = _ := by simp
  have he (path : AdaptiveInfinitePath Outcome) :
      S path = (∑ k ∈ Finset.range (n+1), X k path)+actualResponse protocol g 0 path := by
    dsimp only [S]
    rw [Finset.sum_range_succ',Finset.sum_range_succ']
    simp [X]
  have hmgf (t : ℝ) : (∫ path, Real.exp (t*S path) ∂μ) ≤
      Real.exp (C^2/2+(((n+1:ℕ):ℝ)*V)*t^2/2) := by
    have hi := (hsg n).integrable_exp_mul t
    have hh := (hsg n).mgf_le t
    calc
      _ ≤ ∫ path, Real.exp (|t| * C)*Real.exp (t*∑ k ∈ Finset.range (n+1), X k path) ∂μ := by
        apply integral_mono_of_nonneg (Eventually.of_forall (fun _ => (Real.exp_pos _).le))
          (hi.const_mul _) (Eventually.of_forall (fun path => ?_))
        dsimp only
        rw [he,mul_add,Real.exp_add]
        have hi0 : Real.exp (t*actualResponse protocol g 0 path) ≤ Real.exp (|t| * C) := by
          have hz := BoundedVarianceMGF.exp_bound (actualResponse protocol g 0) C (fun _ => hb _ _) t path
          simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hz
        nlinarith [mul_le_mul_of_nonneg_left hi0
          (Real.exp_pos (t*∑ k ∈ Finset.range (n+1), X k path)).le]
      _ = Real.exp (|t| * C)*(∫ path, Real.exp (t*∑ k ∈ Finset.range (n+1), X k path) ∂μ) := integral_const_mul _ _
      _ ≤ Real.exp (|t| * C)*Real.exp ((((n+1:ℕ):ℝ)*(c:ℝ))*t^2/2) :=
        mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
      _ ≤ _ := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hN : (1:ℝ) ≤ ((n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        have hsq := sq_nonneg (|t|-C)
        rw [sub_sq,sq_abs] at hsq
        dsimp only [V]
        nlinarith [mul_le_mul_of_nonneg_right hN (sq_nonneg t)]
  have ht := twoSided_of_mgf S hm _ hbS (C^2/2) (((n+1:ℕ):ℝ)*V) (by positivity) hmgf x hx
  convert ht using 1
  congr 2
  field_simp

end
end QubitOracle.AdaptiveDesign.AdaptiveGaussianTails
