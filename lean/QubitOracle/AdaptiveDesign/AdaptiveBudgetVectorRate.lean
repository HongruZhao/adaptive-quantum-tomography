import QubitOracle.AdaptiveDesign.AdaptiveBudgetMoments

/-! Finite-dimensional exploration mean-square and preliminary rates. -/
namespace QubitOracle.AdaptiveDesign.AdaptiveBudgetMoments
open QubitOracle.Paper Filter MeasureTheory ProbabilityTheory
open AdaptiveResponseStrongLaw AdaptiveRidgeConsistency ExplorationBudgetStrongLaw
open scoped BigOperators Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
variable {Theta Action Outcome E : Type}
  [MeasurableSpace Action] [MeasurableSpace Outcome]
  [Fintype Outcome] [MeasurableSingletonClass Outcome]
  [StandardBorelSpace Outcome] [Nonempty Outcome]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma vectorSum_square_eq (p : PredictableAdaptiveProtocol Theta (ℕ × Action) Outcome)
    (g : (ℕ × Action) → Outcome → E) (n : ℕ) (path : AdaptiveInfinitePath Outcome) :
    ‖vectorSum p g n path‖^2 = ∑ i : Fin (Module.finrank ℝ E),
      scalarSum p (fun a y => ⟪stdOrthonormalBasis ℝ E i,g a y⟫_ℝ) n path ^ 2 := by
  rw [← (stdOrthonormalBasis ℝ E).sum_sq_inner_right]
  simp only [vectorSum, scalarSum, inner_sum, actualVectorResponse, actualResponse]

lemma vectorSum_square_integrable
    (p : PredictableAdaptiveProtocol Theta (ℕ × Action) Outcome) (theta : Theta)
    (g : (ℕ × Action) → Outcome → E) (C : ℝ) (hb : ∀ a y, ‖g a y‖ ≤ C) (n : ℕ) :
    Integrable (fun path => ‖vectorSum p g n path‖^2) (adaptiveInfiniteTrajectoryMeasure p theta) := by
  simp_rw [vectorSum_square_eq]
  apply integrable_finset_sum
  intro i _
  apply scalarSum_square_integrable p theta _ C
  intro a y
  exact (norm_inner_le_norm _ _).trans (by simpa using hb a y)

/-- This is an L2 bound for the actual adaptive experiment. -/
theorem vectorSum_secondMoment
    (p : PredictableAdaptiveProtocol Theta (ℕ × Action) Outcome) (theta : Theta)
    (htime : ∀ n h, (p.design n h).1=n) (g : (ℕ × Action) → Outcome → E)
    (hm : ∀ a, ∫ y, g a y ∂p.response theta a=0)
    (C : ℝ) (hb : ∀ a y, ‖g a y‖ ≤ C)
    (ε : ℕ → ℝ) (he : ∀ n, 0 ≤ ε n) (V : ℝ) (hV : 0 ≤ V)
    (hv : ∀ u a, ∫ y, ⟪u,g a y⟫_ℝ^2 ∂p.response theta a ≤ ‖u‖^2*V*ε a.1) (n : ℕ) :
    ∫ path, ‖vectorSum p g n path‖^2 ∂adaptiveInfiniteTrajectoryMeasure p theta ≤
      (Module.finrank ℝ E)*(2*V+2*C^2)*mass ε n := by
  letI : IsMarkovKernel (p.response theta) := p.response_isMarkov theta
  let b := stdOrthonormalBasis ℝ E
  have hb' i a y : ‖⟪b i,g a y⟫_ℝ‖ ≤ C :=
    (norm_inner_le_norm _ _).trans (by simpa [b.norm_eq_one] using hb a y)
  simp_rw [vectorSum_square_eq]
  rw [integral_finset_sum _ (fun i _ => scalarSum_square_integrable p theta _ C (hb' i) n)]
  have hh i := scalarSum_secondMoment p theta htime (fun a y => ⟪b i,g a y⟫_ℝ)
    (fun a => by rw [integral_inner Integrable.of_finite,hm a,inner_zero_right]) C (hb' i)
    ε he V hV (fun a => by simpa [b.norm_eq_one] using hv (b i) a) n
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
    using Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hh i)

/-- A deterministic scale is small whenever its square is negligible
relative to the exploration budget. -/
theorem scaled_vectorSum_zero
    (p : PredictableAdaptiveProtocol Theta (ℕ × Action) Outcome) (theta : Theta)
    (htime : ∀ n h, (p.design n h).1=n) (g : (ℕ × Action) → Outcome → E)
    (hm : ∀ a, ∫ y, g a y ∂p.response theta a=0)
    (C : ℝ) (hb : ∀ a y, ‖g a y‖ ≤ C)
    (ε : ℕ → ℝ) (he : ∀ n, 0 ≤ ε n) (V : ℝ) (hV : 0 ≤ V)
    (hv : ∀ u a, ∫ y, ⟪u,g a y⟫_ℝ^2 ∂p.response theta a ≤ ‖u‖^2*V*ε a.1)
    (q : ℕ → ℝ) (hq : Tendsto (fun n => q n^2/mass ε n) atTop (𝓝 0)) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure p theta)
      (fun n path => (q n/mass ε n) • vectorSum p g n path) atTop (fun _ => 0) := by
  let μ := adaptiveInfiniteTrajectoryMeasure p theta
  let A : ℝ := (Module.finrank ℝ E)*(2*V+2*C^2)
  have hs : TendstoInMeasure μ
      (fun n path => (q n/mass ε n)*‖vectorSum p g n path‖) atTop (fun _ => 0) := by
    apply SecondMomentConvergence.inMeasure_of_secondMoment μ _ (fun n => A*(q n^2/mass ε n))
    · intro n
      simp only [mul_pow]
      exact (vectorSum_square_integrable p theta g C hb n).const_mul _
    · intro n
      simp only [mul_pow, integral_const_mul]
      have hn := vectorSum_secondMoment p theta htime g hm C hb ε he V hV hv n
      calc
        _ ≤ (q n/mass ε n)^2 * (A*mass ε n) :=
          mul_le_mul_of_nonneg_left hn (sq_nonneg _)
        _ = _ := by field_simp [(mass_pos ε he n).ne']
    · simpa using hq.const_mul A
  apply ProbabilityZeroAlgebra.dominated hs 1 (by norm_num)
  intro n path
  simp only [norm_smul, norm_mul, norm_norm, one_mul]
  exact le_rfl

end
end QubitOracle.AdaptiveDesign.AdaptiveBudgetMoments
