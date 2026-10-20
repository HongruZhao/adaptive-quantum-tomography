import QubitOracle.AdaptiveDesign.AdaptiveBudgetConcentration

namespace QubitOracle.AdaptiveDesign.AdaptiveBudgetConcentration
open QubitOracle.Paper Filter MeasureTheory ProbabilityTheory
open AdaptiveResponseStrongLaw AdaptiveConditionalMoments AdaptiveRidgeConsistency
open ExplorationBudgetStrongLaw
open scoped BigOperators Topology InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

theorem vector
    {Theta Action Outcome E : Type}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [Fintype Outcome] [MeasurableSingletonClass Outcome]
    [StandardBorelSpace Outcome] [Nonempty Outcome]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (protocol : PredictableAdaptiveProtocol Theta (ℕ × Action) Outcome) (theta : Theta)
    (htime : ∀ n h, (protocol.design n h).1 = n)
    (g : (ℕ × Action) → Outcome → E)
    (hmean : ∀ a, ∫ y, g a y ∂protocol.response theta a = 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ a y, ‖g a y‖ ≤ C)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (V : ℝ) (hV : 0 ≤ V)
    (hvar : ∀ u a, ∫ y, ⟪u,g a y⟫_ℝ^2 ∂protocol.response theta a ≤ ‖u‖^2*V*ε a.1)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ B c : ℝ, 0 < B ∧ 0 < c ∧ ∀ n,
      (adaptiveInfiniteTrajectoryMeasure protocol theta).real
        {path | δ*mass ε (n+1) ≤ ‖∑ k ∈ Finset.range (n+1), actualVectorResponse protocol g k path‖} ≤
      B*Real.exp (-c*mass ε (n+1)) := by
  classical
  letI : IsMarkovKernel (protocol.response theta) := protocol.response_isMarkov theta
  let μ := adaptiveInfiniteTrajectoryMeasure protocol theta
  let b := stdOrthonormalBasis ℝ E
  let N := Module.finrank ℝ E
  let a := δ/((N:ℝ)+1)
  have ha : 0 < a := div_pos hδ (by positivity)
  have hc (i : Fin N) := scalar protocol theta htime (fun a y => ⟪b i,g a y⟫_ℝ)
    (fun a => by rw [integral_inner Integrable.of_finite,hmean a,inner_zero_right]) C hC
    (fun a y => (norm_inner_le_norm _ _).trans (by simpa [b.norm_eq_one] using hb a y))
    ε hε V hV (fun a => by simpa [b.norm_eq_one] using hvar (b i) a) a ha
  choose B c hB hcpos htail using hc
  let c0 := (1+∑ i : Fin N, (c i)⁻¹)⁻¹
  have hinv (i : Fin N) : 0 ≤ (c i)⁻¹ := (inv_pos.mpr (hcpos i)).le
  have hden : 0 < 1+∑ i : Fin N, (c i)⁻¹ :=
    add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun i _ => hinv i))
  have hc0 : 0 < c0 := inv_pos.mpr hden
  have hci (i : Fin N) : c0 ≤ c i := by
    have hi : (c i)⁻¹ ≤ 1+∑ j : Fin N, (c j)⁻¹ := by
      have hs := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin N))) => hinv j)
        (Finset.mem_univ i)
      linarith
    have hh := one_div_le_one_div_of_le (inv_pos.mpr (hcpos i)) hi
    simpa only [one_div, inv_inv] using hh
  refine ⟨1+∑ i : Fin N, B i,c0,
    add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun i _ => (hB i).le)),hc0,fun n => ?_⟩
  let M := mass ε (n+1)
  let S := fun path => ∑ k ∈ Finset.range (n+1), actualVectorResponse protocol g k path
  have hM : 0 < M := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun k _ => hε k))
  have hrepr (path : AdaptiveInfinitePath Outcome) :
      ‖S path‖ ≤ ∑ i : Fin N, |⟪b i,S path⟫_ℝ| := by
    calc
      _ = ‖∑ i : Fin N, ⟪b i,S path⟫_ℝ • b i‖ := congrArg norm (b.sum_repr' (S path)).symm
      _ ≤ ∑ i : Fin N, ‖⟪b i,S path⟫_ℝ • b i‖ := norm_sum_le _ _
      _ = _ := by simp [norm_smul,b.norm_eq_one]
  have hsub : {path | δ*M ≤ ‖S path‖} ⊆ ⋃ i : Fin N, {path | a*M ≤ |⟪b i,S path⟫_ℝ|} := by
    intro path hp
    simp only [Set.mem_iUnion,Set.mem_ofPred_eq]
    by_contra hh
    push_neg at hh
    have hs : (∑ i : Fin N, |⟪b i,S path⟫_ℝ|) ≤ (N:ℝ)*(a*M) := by
      calc
        _ ≤ ∑ _i : Fin N, a*M := Finset.sum_le_sum (fun i _ => (hh i).le)
        _ = _ := by simp
    have hd : (N:ℝ)*(a*M) < δ*M := by
      have hN : (N:ℝ)/((N:ℝ)+1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
      have hx := mul_lt_mul_of_pos_right hN (mul_pos hδ hM)
      calc
        _ = ((N:ℝ)/((N:ℝ)+1))*(δ*M) := by dsimp only [a]; ring
        _ < 1*(δ*M) := hx
        _ = _ := one_mul _
    exact (not_le_of_gt (lt_of_le_of_lt ((hrepr path).trans hs) hd)) hp
  calc
    _ ≤ μ.real (⋃ i : Fin N, {path | a*M ≤ |⟪b i,S path⟫_ℝ|}) := measureReal_mono hsub
    _ ≤ ∑ i : Fin N, μ.real {path | a*M ≤ |⟪b i,S path⟫_ℝ|} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ i : Fin N, B i*Real.exp (-(c i)*M) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [S,inner_sum,actualVectorResponse,actualResponse] using htail i n
    _ ≤ ∑ i : Fin N, B i*Real.exp (-c0*M) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hB i).le
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right (hci i) hM.le]
    _ = (∑ i : Fin N, B i)*Real.exp (-c0*M) := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

end
end QubitOracle.AdaptiveDesign.AdaptiveBudgetConcentration
