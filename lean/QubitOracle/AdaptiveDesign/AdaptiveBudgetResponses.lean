import QubitOracle.AdaptiveDesign.ExplorationBudgetStrongLaw
import QubitOracle.AdaptiveDesign.SecondMomentConvergence

/-! The variance-budget strong law on the literal adaptive path measure. -/
namespace QubitOracle.AdaptiveDesign.AdaptiveBudgetResponses
open QubitOracle.Paper Filter MeasureTheory ProbabilityTheory
open AdaptiveResponseStrongLaw AdaptiveConditionalMoments
open ExplorationBudgetStrongLaw BoundedMartingaleSecondMoment
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false

variable {Theta Action Outcome : Type}
  [MeasurableSpace Action] [MeasurableSpace Outcome]
  [Fintype Outcome] [MeasurableSingletonClass Outcome]
  [StandardBorelSpace Outcome] [Nonempty Outcome]

lemma shifted_mass (ε : ℕ → ℝ) (n : ℕ) :
    mass (fun k => ε (k+1)) n = mass ε (n+1)-ε 0 := by
  simp only [mass, Finset.sum_range_succ']
  ring

theorem scalar_noise_ae
    (p : PredictableAdaptiveProtocol Theta (ℕ × Action) Outcome) (theta : Theta)
    (htime : ∀ n h, (p.design n h).1 = n)
    (g : (ℕ × Action) → Outcome → ℝ)
    (hmean : ∀ a, ∫ y, g a y ∂p.response theta a = 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ a y, ‖g a y‖ ≤ C)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hinf : Tendsto (mass ε) atTop atTop)
    (V : ℝ) (hV : 0 ≤ V)
    (hvar : ∀ a, ∫ y, g a y ^ 2 ∂p.response theta a ≤ V*ε a.1) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure p theta,
      Tendsto (fun n => (∑ k ∈ Finset.range n, actualResponse p g k path)/mass ε n)
        atTop (𝓝 0) := by
  let μ := adaptiveInfiniteTrajectoryMeasure p theta
  let X := fun n => actualResponse p g (n+1)
  have ha (n : ℕ) : StronglyMeasurable[Filtration.piLE (n+1)] (X n) :=
    actualResponse_stronglyMeasurable_piLE p g (n+1)
  have hc (n : ℕ) : μ[X n | Filtration.piLE n] =ᵐ[μ] 0 :=
    actualResponse_condExp_zero p theta g hmean C hb n
  have hbound (n : ℕ) (path : AdaptiveInfinitePath Outcome) : ‖X n path‖ ≤ C := hb _ _
  have hv (n : ℕ) : ∫ path, X n path ^ 2 ∂μ ≤ V*ε (n+1) := by
    have hbg (a : ℕ × Action) (y : Outcome) : ‖g a y ^ 2‖ ≤ C^2 := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb a y) 2
    have hcond := actualResponse_condExp p theta (fun a y => g a y ^ 2) (C^2) hbg n
    have hi : Integrable (fun path => ∫ y,
        g (p.design (n+1) (adaptiveInfinitePathPrefix (n+1) path)) y ^ 2
        ∂p.response theta (p.design (n+1) (adaptiveInfinitePathPrefix (n+1) path))) μ :=
      integrable_condExp.congr hcond
    calc
      _ = ∫ path, μ[(fun path => X n path ^ 2) | Filtration.piLE n] path ∂μ :=
        (integral_condExp (Filtration.piLE.le n)).symm
      _ = ∫ path, ∫ y, g (p.design (n+1) (adaptiveInfinitePathPrefix (n+1) path)) y ^ 2
          ∂p.response theta (p.design (n+1) (adaptiveInfinitePathPrefix (n+1) path)) ∂μ :=
        integral_congr_ae hcond
      _ ≤ ∫ _ : AdaptiveInfinitePath Outcome, V*ε (n+1) ∂μ := by
        apply integral_mono hi (integrable_const _)
        intro path
        simpa only [htime] using hvar (p.design (n+1) (adaptiveInfinitePathPrefix (n+1) path))
      _ = _ := by simp [μ]
  have hinf' : Tendsto (mass (fun k => ε (k+1))) atTop atTop := by
    change Tendsto (fun n => mass (fun k => ε (k+1)) n) atTop atTop
    simp_rw [shifted_mass]
    simpa only [Function.comp_def, sub_eq_add_neg, add_comm] using
      tendsto_atTop_add_const_right atTop (-ε 0) (hinf.comp (tendsto_add_atTop_nat 1))
  have hshift := normalized_sum_ae μ Filtration.piLE X ha hc (fun _ => C) hbound
    (fun k => ε (k+1)) (fun k => hε (k+1)) hinf' V hV hv
  filter_upwards [hshift] with path hpath
  have hrec (n : ℕ) : (∑ k ∈ Finset.range (n+1), actualResponse p g k path) =
      partialSum X n path + actualResponse p g 0 path := by
    rw [Finset.sum_range_succ']
    rfl
  have hinit : Tendsto (fun n => C/mass ε (n+1)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp (hinf.comp (tendsto_add_atTop_nat 1))).const_mul C
  have hlim : Tendsto (fun n => |partialSum X n path/mass (fun k => ε (k+1)) n|+
      C/mass ε (n+1)) atTop (𝓝 0) := by simpa using hpath.abs.add hinit
  have hnlim : Tendsto (fun n =>
      (∑ k ∈ Finset.range (n+1), actualResponse p g k path)/mass ε (n+1)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _ hlim
    intro n
    rw [hrec, Real.norm_eq_abs, abs_div, abs_of_pos (mass_pos ε hε (n+1))]
    have hd : mass (fun k => ε (k+1)) n ≤ mass ε (n+1) := by
      rw [shifted_mass]
      linarith [hε 0]
    calc
      _ ≤ (|partialSum X n path|+C)/mass ε (n+1) :=
        div_le_div_of_nonneg_right
          ((abs_add_le _ _).trans (add_le_add (le_refl _) (hb _ _))) (mass_pos ε hε (n+1)).le
      _ ≤ _ := by
        rw [add_div, abs_div, abs_of_pos (mass_pos _ (fun k => hε (k+1)) n)]
        exact add_le_add (div_le_div_of_nonneg_left (abs_nonneg _)
          (mass_pos _ (fun k => hε (k+1)) n) hd) (le_refl _)
  exact (tendsto_add_atTop_iff_nat 1).mp hnlim

end
end QubitOracle.AdaptiveDesign.AdaptiveBudgetResponses
