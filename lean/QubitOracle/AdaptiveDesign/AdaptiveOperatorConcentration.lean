import QubitOracle.AdaptiveDesign.AdaptiveBudgetVectorConcentration

/-! Exponential concentration of bounded adaptive sums in any fixed
finite-dimensional normed space, including operator norm. -/
namespace QubitOracle.AdaptiveDesign.AdaptiveOperatorConcentration
open QubitOracle.Paper Filter MeasureTheory ProbabilityTheory
open AdaptiveRidgeConsistency
open scoped BigOperators Topology InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

theorem normed
    {Theta Action Outcome E : Type}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [Fintype Outcome] [MeasurableSingletonClass Outcome]
    [StandardBorelSpace Outcome] [Nonempty Outcome]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (protocol : PredictableAdaptiveProtocol Theta (ℕ × Action) Outcome) (theta : Theta)
    (htime : ∀ n h, (protocol.design n h).1 = n)
    (g : (ℕ × Action) → Outcome → E)
    (hmean : ∀ a, ∫ y, g a y ∂protocol.response theta a = 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ a y, ‖g a y‖ ≤ C)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ B c : ℝ, 0 < B ∧ 0 < c ∧ ∀ n,
      (adaptiveInfiniteTrajectoryMeasure protocol theta).real
        {path | δ*((n+1:ℕ):ℝ) ≤ ‖∑ k ∈ Finset.range (n+1), actualVectorResponse protocol g k path‖} ≤
      B*Real.exp (-c*((n+1:ℕ):ℝ)) := by
  letI : IsMarkovKernel (protocol.response theta) := protocol.response_isMarkov theta
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    ((Module.finBasis ℝ E).equivFun.trans (WithLp.linearEquiv 2 ℝ _).symm).toContinuousLinearEquiv
  let C' := ‖e.toContinuousLinearMap‖*C
  let K := ‖e.symm.toContinuousLinearMap‖+1
  have hK : 0 < K := by dsimp [K]; positivity
  have hg (a : ℕ × Action) (y : Outcome) : ‖e (g a y)‖ ≤ C' :=
    (e.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hb a y) (norm_nonneg _))
  have hm (a : ℕ × Action) : ∫ y, e (g a y) ∂protocol.response theta a = 0 := by
    change (∫ y, e.toContinuousLinearMap (g a y) ∂protocol.response theta a) = 0
    rw [e.toContinuousLinearMap.integral_comp_comm Integrable.of_finite, hmean a, map_zero]
  have hv (u : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) (a : ℕ × Action) :
      (∫ y, ⟪u,e (g a y)⟫_ℝ^2 ∂protocol.response theta a) ≤ ‖u‖^2*C'^2*1 := by
    calc
      _ ≤ ∫ _y, ‖u‖^2*C'^2 ∂protocol.response theta a := by
        apply integral_mono Integrable.of_finite (integrable_const _)
        intro y
        dsimp only
        have hi := (norm_inner_le_norm (𝕜:=ℝ) u (e (g a y))).trans
          (mul_le_mul_of_nonneg_left (hg a y) (norm_nonneg _))
        simpa only [Real.norm_eq_abs, sq_abs, mul_pow] using
          pow_le_pow_left₀ (norm_nonneg _) hi 2
      _ = _ := by simp
  obtain ⟨B,c,hB,hc,htail⟩ := AdaptiveBudgetConcentration.vector protocol theta htime
    (fun a y => e (g a y)) hm C' (mul_nonneg (norm_nonneg _) hC) hg
    (fun _ => 1) (fun _ => zero_le_one) (C'^2) (sq_nonneg _) hv (δ/(2*K)) (by positivity)
  refine ⟨B,c,hB,hc,fun n => ?_⟩
  have hM : ExplorationBudgetStrongLaw.mass (fun _ => 1) (n+1) = ((n+1:ℕ):ℝ)+1 := by
    simp [ExplorationBudgetStrongLaw.mass]
    ring
  have hsub : {path | δ*((n+1:ℕ):ℝ) ≤ ‖∑ k ∈ Finset.range (n+1), actualVectorResponse protocol g k path‖} ⊆
      {path | (δ/(2*K))*ExplorationBudgetStrongLaw.mass (fun _ => 1) (n+1) ≤
        ‖∑ k ∈ Finset.range (n+1), actualVectorResponse protocol (fun a y => e (g a y)) k path‖} := by
    intro path hp
    let x := ∑ k ∈ Finset.range (n+1), actualVectorResponse protocol g k path
    have hn : ‖x‖ ≤ K*‖e x‖ := by
      have hh := e.symm.toContinuousLinearMap.le_opNorm (e x)
      change ‖e.symm (e x)‖ ≤ _ at hh
      rw [e.symm_apply_apply] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) (norm_nonneg _))
    have hn' : δ*((n+1:ℕ):ℝ) ≤ K*‖e x‖ := hp.trans hn
    have he : (∑ k ∈ Finset.range (n+1), actualVectorResponse protocol (fun a y => e (g a y)) k path) = e x := by
      simp only [x,map_sum,actualVectorResponse]
    change (δ/(2*K))*ExplorationBudgetStrongLaw.mass (fun _ => 1) (n+1) ≤ _
    rw [he,hM]
    have hN : (1:ℝ) ≤ ((n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have heq : (δ/(2*K))*(((n+1:ℕ):ℝ)+1) = (δ*(((n+1:ℕ):ℝ)+1))/(2*K) := by ring
    rw [heq]
    apply (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hK)).mpr
    nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hN)]
  calc
    _ ≤ (adaptiveInfiniteTrajectoryMeasure protocol theta).real
      {path | (δ/(2*K))*ExplorationBudgetStrongLaw.mass (fun _ => 1) (n+1) ≤
        ‖∑ k ∈ Finset.range (n+1), actualVectorResponse protocol (fun a y => e (g a y)) k path‖} := measureReal_mono hsub
    _ ≤ B*Real.exp (-c*ExplorationBudgetStrongLaw.mass (fun _ => 1) (n+1)) := htail n
    _ ≤ _ := by
      rw [hM]
      apply mul_le_mul_of_nonneg_left _ hB.le
      apply Real.exp_le_exp.mpr
      nlinarith

end
end QubitOracle.AdaptiveDesign.AdaptiveOperatorConcentration
