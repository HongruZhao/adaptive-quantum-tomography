import QubitOracle.AdaptiveDesign.AdaptiveGaussianTails
import QubitOracle.AdaptiveDesign.AdaptiveResponseStrongLaw
import QubitOracle.AdaptiveDesign.AdaptiveRidgeConsistency
import QubitOracle.Paper.AdaptiveTrajectoryExperiment
namespace QubitOracle.AdaptiveDesign.AdaptiveGaussianTails
open QubitOracle.Paper Filter MeasureTheory ProbabilityTheory
open AdaptiveRidgeConsistency AdaptiveResponseStrongLaw
open scoped BigOperators Topology InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

theorem finiteSum {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (f : ι → ℕ → Ω → ℝ)
    (hf : ∀ i, ∃ B c : ℝ, 0 < B ∧ 0 < c ∧ ∀ n x, 0 ≤ x →
      μ.real {ω | x ≤ |f i n ω|} ≤ B*Real.exp (-c*x^2/((n+1:ℕ):ℝ))) :
    ∃ B c : ℝ, 0 < B ∧ 0 < c ∧ ∀ n x, 0 ≤ x →
      μ.real {ω | x ≤ ∑ i, |f i n ω|} ≤ B*Real.exp (-c*x^2/((n+1:ℕ):ℝ)) := by
  classical
  choose B c hB hc ht using hf
  let c0 := (1+∑ i, (c i)⁻¹)⁻¹
  let K := (Fintype.card ι:ℝ)+1
  have hK : 0 < K := by dsimp [K]; positivity
  have hc0 : 0 < c0 := by
    apply inv_pos.mpr
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun i _ => (inv_pos.mpr (hc i)).le))
  have hsumB : 0 ≤ ∑ i, B i := Finset.sum_nonneg (fun i _ => (hB i).le)
  have hci (i : ι) : c0 ≤ c i := by
    have hi : (c i)⁻¹ ≤ 1+∑ j, (c j)⁻¹ := by
      have hh := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => (inv_pos.mpr (hc j)).le)
        (Finset.mem_univ i)
      linarith
    simpa only [one_div,inv_inv] using one_div_le_one_div_of_le (inv_pos.mpr (hc i)) hi
  refine ⟨1+∑ i, B i,c0/K^2,by positivity,by positivity,fun n x hx => ?_⟩
  by_cases hx0 : x=0
  · subst x
    simp only [zero_pow (by omega : 2≠0),mul_zero,zero_div,Real.exp_zero,mul_one]
    exact (measureReal_le_one (μ:=μ)).trans (by linarith only [hsumB])
  have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hun : {ω | x ≤ ∑ i, |f i n ω|} ⊆ ⋃ i, {ω | x/K ≤ |f i n ω|} := by
    intro ω hω
    simp only [Set.mem_iUnion,Set.mem_setOf_eq]
    by_contra hh
    push_neg at hh
    have hs : (∑ i, |f i n ω|) ≤ (Fintype.card ι:ℝ)*(x/K) := by
      calc
        _ ≤ ∑ _i : ι, x/K := Finset.sum_le_sum (fun i _ => (hh i).le)
        _ = _ := by simp
    have hlt : (Fintype.card ι:ℝ)*(x/K) < x := by
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ hK).mpr
      dsimp only [K]
      nlinarith only [hxp]
    exact (not_le_of_gt (hs.trans_lt hlt)) hω
  calc
    _ ≤ μ.real (⋃ i, {ω | x/K ≤ |f i n ω|}) := measureReal_mono hun
    _ ≤ ∑ i, μ.real {ω | x/K ≤ |f i n ω|} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ i, B i*Real.exp (-(c i)*(x/K)^2/((n+1:ℕ):ℝ)) :=
      Finset.sum_le_sum (fun i _ => ht i n (x/K) (div_nonneg hx hK.le))
    _ ≤ ∑ i, B i*Real.exp (-(c0/K^2)*x^2/((n+1:ℕ):ℝ)) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hB i).le
      apply Real.exp_le_exp.mpr
      have hh := div_le_div_of_nonneg_right
        (neg_le_neg (mul_le_mul_of_nonneg_right (hci i) (sq_nonneg (x/K))))
        (show (0:ℝ)≤((n+1:ℕ):ℝ) by positivity)
      rw [neg_mul]
      calc
        _ ≤ -(c0*(x/K)^2)/((n+1:ℕ):ℝ) := hh
        _ = -(c0/K^2)*x^2/((n+1:ℕ):ℝ) := by ring
    _ = (∑ i, B i)*Real.exp (-(c0/K^2)*x^2/((n+1:ℕ):ℝ)) := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

theorem vector
    {Theta Action Outcome E : Type*}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [Fintype Outcome] [MeasurableSingletonClass Outcome]
    [StandardBorelSpace Outcome] [Nonempty Outcome]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta)
    (g : Action → Outcome → E)
    (hmean : ∀ a, ∫ y, g a y ∂protocol.response theta a = 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ a y, ‖g a y‖ ≤ C) :
    ∃ B c : ℝ, 0 < B ∧ 0 < c ∧ ∀ (n : ℕ) (x : ℝ), 0 ≤ x →
      (adaptiveInfiniteTrajectoryMeasure protocol theta).real
        {path | x ≤ ‖∑ k ∈ Finset.range (n+1), actualVectorResponse protocol g k path‖} ≤
      B*Real.exp (-c*x^2/((n+1:ℕ):ℝ)) := by
  letI : IsMarkovKernel (protocol.response theta) := protocol.response_isMarkov theta
  let b := stdOrthonormalBasis ℝ E
  have hc (i : Fin (Module.finrank ℝ E)) := scalar protocol theta (fun a y => ⟪b i,g a y⟫_ℝ)
    (fun a => by rw [integral_inner Integrable.of_finite,hmean a,inner_zero_right]) C hC
    (fun a y => (norm_inner_le_norm _ _).trans (by simpa [b.norm_eq_one] using hb a y))
  obtain ⟨B,c,hB,hc',ht⟩ := finiteSum
    (fun i n path => ∑ k ∈ Finset.range (n+1), actualResponse protocol (fun a y => ⟪b i,g a y⟫_ℝ) k path) hc
  refine ⟨B,c,hB,hc',fun n x hx => (measureReal_mono ?_).trans (ht n x hx)⟩
  intro path hp
  let S := ∑ k ∈ Finset.range (n+1), actualVectorResponse protocol g k path
  have hn : ‖S‖ ≤ ∑ i, |⟪b i,S⟫_ℝ| := by
    calc
      _ = ‖∑ i, ⟪b i,S⟫_ℝ • b i‖ := congrArg norm (b.sum_repr' S).symm
      _ ≤ ∑ i, ‖⟪b i,S⟫_ℝ • b i‖ := norm_sum_le _ _
      _ = _ := by simp [norm_smul,b.norm_eq_one]
  change x ≤ _
  apply (show x ≤ ‖S‖ from hp).trans
  simpa only [S,inner_sum,actualVectorResponse,actualResponse] using hn

end
end QubitOracle.AdaptiveDesign.AdaptiveGaussianTails
