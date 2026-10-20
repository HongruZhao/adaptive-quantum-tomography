import QubitOracle.AdaptiveDesign.AdaptiveBudgetResponses
import QubitOracle.AdaptiveDesign.AdaptiveRidgeConsistency
import QubitOracle.AdaptiveDesign.BoundedResponseQuarterRate

/-! Actual adaptive response moments retain the exploration budget.
No central limit theorem is needed for the preliminary rate. -/
namespace QubitOracle.AdaptiveDesign.AdaptiveBudgetMoments
open QubitOracle.Paper Filter MeasureTheory ProbabilityTheory
open AdaptiveResponseStrongLaw AdaptiveConditionalMoments AdaptiveRidgeConsistency
open ExplorationBudgetStrongLaw BoundedMartingaleSecondMoment
open scoped BigOperators Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
variable {Theta Action Outcome : Type}
  [MeasurableSpace Action] [MeasurableSpace Outcome]
  [Fintype Outcome] [MeasurableSingletonClass Outcome]
  [StandardBorelSpace Outcome] [Nonempty Outcome]

lemma actual_square_bound
    (p : PredictableAdaptiveProtocol Theta (ℕ × Action) Outcome) (theta : Theta)
    (htime : ∀ n h, (p.design n h).1=n)
    (g : (ℕ × Action) → Outcome → ℝ) (C : ℝ) (hb : ∀ a y, ‖g a y‖ ≤ C)
    (ε : ℕ → ℝ) (V : ℝ)
    (hv : ∀ a, ∫ y, g a y^2 ∂p.response theta a ≤ V*ε a.1) (n : ℕ) :
    ∫ path, actualResponse p g (n+1) path ^ 2 ∂adaptiveInfiniteTrajectoryMeasure p theta ≤
      V*ε (n+1) := by
  let μ := adaptiveInfiniteTrajectoryMeasure p theta
  have hbg (a : ℕ × Action) (y : Outcome) : ‖g a y ^ 2‖ ≤ C^2 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb a y) 2
  have hcond := actualResponse_condExp p theta (fun a y => g a y ^ 2) (C^2) hbg n
  have hi : Integrable (fun path => ∫ y,
      g (p.design (n+1) (adaptiveInfinitePathPrefix (n+1) path)) y ^ 2
      ∂p.response theta (p.design (n+1) (adaptiveInfinitePathPrefix (n+1) path))) μ :=
    integrable_condExp.congr hcond
  calc
    _ = ∫ path, μ[(fun path => actualResponse p g (n+1) path ^ 2) | Filtration.piLE n] path ∂μ :=
      (integral_condExp (Filtration.piLE.le n)).symm
    _ = ∫ path, ∫ y, g (p.design (n+1) (adaptiveInfinitePathPrefix (n+1) path)) y ^ 2
        ∂p.response theta (p.design (n+1) (adaptiveInfinitePathPrefix (n+1) path)) ∂μ :=
      integral_congr_ae hcond
    _ ≤ ∫ _ : AdaptiveInfinitePath Outcome, V*ε (n+1) ∂μ := by
      apply integral_mono hi (integrable_const _)
      intro path
      simpa only [htime] using hv (p.design (n+1) (adaptiveInfinitePathPrefix (n+1) path))
    _ = _ := by simp [μ]

def scalarSum (p : PredictableAdaptiveProtocol Theta (ℕ × Action) Outcome)
    (g : (ℕ × Action) → Outcome → ℝ) (n : ℕ) (path : AdaptiveInfinitePath Outcome) : ℝ :=
  ∑ k ∈ Finset.range n, actualResponse p g k path

lemma scalarSum_measurable (p : PredictableAdaptiveProtocol Theta (ℕ × Action) Outcome)
    (g : (ℕ × Action) → Outcome → ℝ) (n : ℕ) : StronglyMeasurable (scalarSum p g n) := by
  have h := Finset.stronglyMeasurable_sum (Finset.range n) (fun k _ =>
    (actualResponse_stronglyMeasurable_piLE p g k).mono (Filtration.piLE.le k))
  convert h using 1
  funext path
  simp [scalarSum]

lemma scalarSum_bound (p : PredictableAdaptiveProtocol Theta (ℕ × Action) Outcome)
    (g : (ℕ × Action) → Outcome → ℝ) (C : ℝ) (hb : ∀ a y, ‖g a y‖ ≤ C)
    (n : ℕ) (path : AdaptiveInfinitePath Outcome) : ‖scalarSum p g n path‖ ≤ n*C := by
  apply (norm_sum_le _ _).trans
  have h := Finset.sum_le_sum (s := Finset.range n) (fun k _ =>
    hb (p.design k (adaptiveInfinitePathPrefix k path)) (path k))
  simpa only [actualResponse, Finset.sum_const, Finset.card_range, nsmul_eq_mul] using h

lemma scalarSum_square_integrable (p : PredictableAdaptiveProtocol Theta (ℕ × Action) Outcome)
    (theta : Theta) (g : (ℕ × Action) → Outcome → ℝ) (C : ℝ) (hb : ∀ a y, ‖g a y‖ ≤ C)
    (n : ℕ) : Integrable (fun path => scalarSum p g n path ^ 2)
      (adaptiveInfiniteTrajectoryMeasure p theta) := by
  apply Integrable.of_bound ((scalarSum_measurable p g n).pow 2).aestronglyMeasurable ((n*C)^2)
  filter_upwards [] with path
  change ‖scalarSum p g n path ^ 2‖ ≤ (n*C)^2
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (scalarSum_bound p g C hb n path) 2

/-- The harmless initial observation is included explicitly. -/
theorem scalarSum_secondMoment
    (p : PredictableAdaptiveProtocol Theta (ℕ × Action) Outcome) (theta : Theta)
    (htime : ∀ n h, (p.design n h).1=n)
    (g : (ℕ × Action) → Outcome → ℝ)
    (hm : ∀ a, ∫ y, g a y ∂p.response theta a=0)
    (C : ℝ) (hb : ∀ a y, ‖g a y‖ ≤ C)
    (ε : ℕ → ℝ) (he : ∀ n, 0 ≤ ε n) (V : ℝ) (hV : 0 ≤ V)
    (hv : ∀ a, ∫ y, g a y^2 ∂p.response theta a ≤ V*ε a.1) (n : ℕ) :
    ∫ path, scalarSum p g n path ^ 2 ∂adaptiveInfiniteTrajectoryMeasure p theta ≤
      (2*V+2*C^2)*mass ε n := by
  cases n with
  | zero => simp [scalarSum, mass]; positivity
  | succ n =>
    let μ := adaptiveInfiniteTrajectoryMeasure p theta
    let X := fun k => actualResponse p g (k+1)
    have ha k : StronglyMeasurable[Filtration.piLE (k+1)] (X k) :=
      actualResponse_stronglyMeasurable_piLE p g (k+1)
    have hc k : μ[X k | Filtration.piLE k] =ᵐ[μ] 0 :=
      actualResponse_condExp_zero p theta g hm C hb k
    have hXb k path : ‖X k path‖ ≤ C := hb _ _
    have hXv k : ∫ path, X k path^2 ∂μ ≤ V*ε (k+1) :=
      actual_square_bound p theta htime g C hb ε V hv k
    have hs := integral_sum_square_le μ Filtration.piLE X ha hc (fun _ => C) hXb
      (fun k => ε (k+1)) V hXv n
    have hrec (path : AdaptiveInfinitePath Outcome) :
        scalarSum p g (n+1) path = partialSum X n path + actualResponse p g 0 path := by
      rw [scalarSum, Finset.sum_range_succ']
      rfl
    have hsum : ∑ k ∈ Finset.range n, ε (k+1) ≤ mass ε (n+1) := by
      rw [mass, Finset.sum_range_succ']
      linarith [he 0]
    calc
      _ ≤ ∫ path, 2*(partialSum X n path)^2+2*C^2 ∂μ := by
        apply integral_mono (scalarSum_square_integrable p theta g C hb (n+1))
          (((partialSum_square_integrable μ Filtration.piLE X ha (fun _ => C) hXb n).const_mul 2).add (integrable_const _))
        intro path
        change scalarSum p g (n+1) path ^ 2 ≤ 2*(partialSum X n path)^2+2*C^2
        rw [hrec]
        have h := hb (p.design 0 (adaptiveInfinitePathPrefix 0 path)) (path 0)
        change ‖actualResponse p g 0 path‖ ≤ C at h
        rw [Real.norm_eq_abs] at h
        nlinarith [sq_nonneg (partialSum X n path-actualResponse p g 0 path),
          sq_abs (actualResponse p g 0 path), abs_nonneg (actualResponse p g 0 path)]
      _ = 2*(∫ path, partialSum X n path^2 ∂μ)+2*C^2 := by
        rw [integral_add
          ((partialSum_square_integrable μ Filtration.piLE X ha (fun _ => C) hXb n).const_mul 2)
          (integrable_const _), integral_const_mul]
        simp [μ]
      _ ≤ _ := by
        have h1 := mul_le_mul_of_nonneg_left hsum hV
        have h2 := mul_le_mul_of_nonneg_left (mass_ge_one ε he (n+1)) (sq_nonneg C)
        nlinarith

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def vectorSum (p : PredictableAdaptiveProtocol Theta (ℕ × Action) Outcome)
    (g : (ℕ × Action) → Outcome → E) (n : ℕ) (path : AdaptiveInfinitePath Outcome) : E :=
  ∑ k ∈ Finset.range n, actualVectorResponse p g k path

/-- Strong consistency needs only a diverging exploration budget. -/
theorem vector_noise_ae
    (p : PredictableAdaptiveProtocol Theta (ℕ × Action) Outcome) (theta : Theta)
    (htime : ∀ n h, (p.design n h).1=n) (g : (ℕ × Action) → Outcome → E)
    (hm : ∀ a, ∫ y, g a y ∂p.response theta a=0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ a y, ‖g a y‖ ≤ C)
    (ε : ℕ → ℝ) (he : ∀ n, 0 ≤ ε n) (hinf : Tendsto (mass ε) atTop atTop)
    (V : ℝ) (hV : 0 ≤ V)
    (hv : ∀ u a, ∫ y, ⟪u,g a y⟫_ℝ^2 ∂p.response theta a ≤ ‖u‖^2*V*ε a.1) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure p theta,
      Tendsto (fun n => (mass ε n)⁻¹ • vectorSum p g n path) atTop (𝓝 0) := by
  letI : IsMarkovKernel (p.response theta) := p.response_isMarkov theta
  let b := stdOrthonormalBasis ℝ E
  have hcoord i := AdaptiveBudgetResponses.scalar_noise_ae p theta htime
    (fun a y => ⟪b i,g a y⟫_ℝ)
    (fun a => by rw [integral_inner Integrable.of_finite,hm a,inner_zero_right])
    C hC (fun a y => (norm_inner_le_norm _ _).trans (by simpa [b.norm_eq_one] using hb a y))
    ε he hinf V hV
    (fun a => by simpa [b.norm_eq_one] using hv (b i) a)
  have hall := ae_all_iff.2 hcoord
  filter_upwards [hall] with path hpath
  have hs := tendsto_finset_sum Finset.univ (fun i _ => (hpath i).smul_const (b i))
  simpa only [div_eq_mul_inv, ← inner_sum, ← inner_smul_right, mul_comm,
    b.sum_repr', vectorSum, zero_smul, Finset.sum_const_zero, actualResponse, actualVectorResponse] using hs

end
end QubitOracle.AdaptiveDesign.AdaptiveBudgetMoments
