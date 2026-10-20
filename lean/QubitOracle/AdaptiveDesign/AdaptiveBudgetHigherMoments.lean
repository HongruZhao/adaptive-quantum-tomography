import QubitOracle.AdaptiveDesign.BoundedVarianceMGF
import QubitOracle.AdaptiveDesign.AdaptiveBudgetResponses

/-! Higher moments on the actual adaptive path measure, normalized by the
deterministic exploration budget. Conditional variances are obtained from
the response kernel. No rate of divergence or batch-length assumption is
needed for these moment bounds. -/
namespace QubitOracle.AdaptiveDesign.AdaptiveBudgetHigherMoments
open QubitOracle.Paper Filter MeasureTheory ProbabilityTheory
open AdaptiveResponseStrongLaw AdaptiveConditionalMoments AdaptiveRidgeConsistency
open ExplorationBudgetStrongLaw BoundedMartingaleSecondMoment AdaptiveResponseMoments
open scoped BigOperators Topology InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

variable {Theta Action Outcome : Type}
  [MeasurableSpace Action] [MeasurableSpace Outcome]
  [Fintype Outcome] [MeasurableSingletonClass Outcome]
  [StandardBorelSpace Outcome] [Nonempty Outcome]

theorem scalar
    (protocol : PredictableAdaptiveProtocol Theta (ℕ × Action) Outcome) (theta : Theta)
    (htime : ∀ n h, (protocol.design n h).1 = n)
    (g : (ℕ × Action) → Outcome → ℝ)
    (hmean : ∀ a, ∫ y, g a y ∂protocol.response theta a = 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ a y, ‖g a y‖ ≤ C)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (V : ℝ) (hV : 0 ≤ V)
    (hvar : ∀ a, ∫ y, g a y^2 ∂protocol.response theta a ≤ V*ε a.1) (p : ℕ) :
    UniformMoment (adaptiveInfiniteTrajectoryMeasure protocol theta)
      (fun n path => (Real.sqrt (mass ε (n+1)))⁻¹ *
        ∑ k ∈ Finset.range (n+1), actualResponse protocol g k path) p := by
  let μ := adaptiveInfiniteTrajectoryMeasure protocol theta
  let X := fun n => actualResponse protocol g (n+1)
  have ha (n : ℕ) : StronglyMeasurable[Filtration.piLE (n+1)] (X n) :=
    actualResponse_stronglyMeasurable_piLE protocol g (n+1)
  have hc (n : ℕ) : μ[X n | Filtration.piLE n] =ᵐ[μ] 0 :=
    actualResponse_condExp_zero protocol theta g hmean C hb n
  have hbound (n : ℕ) (path : AdaptiveInfinitePath Outcome) : ‖X n path‖ ≤ C := hb _ _
  have hv (n : ℕ) : ∀ᵐ path ∂μ,
      μ[fun path => X n path^2 | Filtration.piLE n] path ≤ V*ε (n+1) := by
    have hbg (a : ℕ × Action) (y : Outcome) : ‖g a y^2‖ ≤ C^2 := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb a y) 2
    have hcond := actualResponse_condExp protocol theta (fun a y => g a y^2) (C^2) hbg n
    filter_upwards [hcond] with path hpath
    change μ[fun path => X n path^2 | Filtration.piLE n] path = _ at hpath
    rw [hpath]
    simpa only [htime] using hvar
      (protocol.design (n+1) (adaptiveInfinitePathPrefix (n+1) path))
  let K := C+1+V
  let M := fun n => mass ε (n+1)
  have hM (n : ℕ) : 1 ≤ M n := by
    dsimp [M,mass]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun k _ => hε k))
  have hMpos (n : ℕ) : 0 < M n := lt_of_lt_of_le zero_lt_one (hM n)
  have hsqrt (n : ℕ) : 1 ≤ Real.sqrt (M n) := by
    rw [Real.le_sqrt (by norm_num) (hMpos n).le]
    simpa using hM n
  have hK : 0 < K := by dsimp [K]; linarith
  have hCK : C ≤ K := by dsimp [K]; linarith
  have hVK : V ≤ K^2 := by dsimp [K]; nlinarith [sq_nonneg (C+V)]
  have htotal (n : ℕ) : (∑ k ∈ Finset.range n, V*ε (k+1)) ≤ V*M n := by
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ hV
    dsimp [M,mass]
    rw [Finset.sum_range_succ']
    linarith [hε 0]
  have hr (n : ℕ) : 0 < K*Real.sqrt (M n) := mul_pos hK (Real.sqrt_pos.mpr (hMpos n))
  have hcr (n : ℕ) : C ≤ K*Real.sqrt (M n) :=
    hCK.trans (le_mul_of_one_le_right hK.le (hsqrt n))
  have hvr (n : ℕ) : (∑ k ∈ Finset.range n, V*ε (k+1)) ≤ (K*Real.sqrt (M n))^2 := by
    rw [mul_pow, Real.sq_sqrt (hMpos n).le]
    exact (htotal n).trans (mul_le_mul_of_nonneg_right hVK (hMpos n).le)
  have hs := BoundedVarianceMGF.uniformMoment (μ:=μ) Filtration.piLE X ha hc C hC hbound
    (fun k => V*ε (k+1)) hv (fun n => K*Real.sqrt (M n)) hr hcr hvr p
  have hs' : UniformMoment μ
      (fun n path => (Real.sqrt (M n))⁻¹ * partialSum X n path) p := by
    convert hs.const_mul K using 1
    funext n path
    rw [mul_inv_rev]
    field_simp
  have hi : UniformMoment μ
      (fun n path => (Real.sqrt (M n))⁻¹ * actualResponse protocol g 0 path) p := by
    apply uniformMoment_of_bound _ (fun n =>
      (((actualResponse_stronglyMeasurable_piLE protocol g 0).mono
        (Filtration.piLE.le 0)).const_mul _).aestronglyMeasurable) C hC
    intro n path
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (mul_le_mul_of_nonneg_left (hb _ _) (by positivity)).trans
      (mul_le_of_le_one_left hC ((inv_le_one₀ (Real.sqrt_pos.mpr (hMpos n))).mpr (hsqrt n)))
  convert hs'.add hi using 1
  funext n path
  rw [← mul_add]
  congr 1
  rw [Finset.sum_range_succ']
  rfl

theorem vector
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (protocol : PredictableAdaptiveProtocol Theta (ℕ × Action) Outcome) (theta : Theta)
    (htime : ∀ n h, (protocol.design n h).1 = n)
    (g : (ℕ × Action) → Outcome → E)
    (hmean : ∀ a, ∫ y, g a y ∂protocol.response theta a = 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ a y, ‖g a y‖ ≤ C)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (V : ℝ) (hV : 0 ≤ V)
    (hvar : ∀ u a, ∫ y, ⟪u,g a y⟫_ℝ^2 ∂protocol.response theta a ≤ ‖u‖^2*V*ε a.1)
    (p : ℕ) :
    UniformMoment (adaptiveInfiniteTrajectoryMeasure protocol theta)
      (fun n path => (Real.sqrt (mass ε (n+1)))⁻¹ •
        ∑ k ∈ Finset.range (n+1), actualVectorResponse protocol g k path) p := by
  letI : IsMarkovKernel (protocol.response theta) := protocol.response_isMarkov theta
  let b := stdOrthonormalBasis ℝ E
  have hc (i : Fin (Module.finrank ℝ E)) := scalar protocol theta htime
    (fun a y => ⟪b i, g a y⟫_ℝ)
    (fun a => by rw [integral_inner Integrable.of_finite, hmean a, inner_zero_right]) C hC
    (fun a y => (norm_inner_le_norm _ _).trans (by simpa [b.norm_eq_one] using hb a y))
    ε hε V hV (fun a => by simpa [b.norm_eq_one] using hvar (b i) a) p
  have hvec (i : Fin (Module.finrank ℝ E)) : UniformMoment
      (adaptiveInfiniteTrajectoryMeasure protocol theta)
      (fun n path => ((Real.sqrt (mass ε (n+1)))⁻¹ *
        ∑ k ∈ Finset.range (n+1), ⟪b i, actualVectorResponse protocol g k path⟫_ℝ) • b i) p := by
    have hm (n : ℕ) := (Classical.choose_spec (hc i)).2 n
    apply (hc i).of_dominated _ (fun n => hm n |>.1.1.smul_const (b i)) 1 (by norm_num)
    intro n path
    simp only [norm_smul, b.norm_eq_one, mul_one, one_mul]
    rfl
  have hs := UniformMoment.finite_sum Finset.univ _ (fun i _ => hvec i)
  simpa only [← inner_sum, ← inner_smul_right, b.sum_repr'] using hs

end
end QubitOracle.AdaptiveDesign.AdaptiveBudgetHigherMoments
