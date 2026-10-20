import QubitOracle.AdaptiveDesign.L2MartingaleBudget
import QubitOracle.AdaptiveDesign.AdaptiveBudgetVectorRate

/-! Exact mean and variance accounting, including the first adaptive copy. -/
namespace QubitOracle.AdaptiveDesign.AdaptiveExactMoments
open QubitOracle.Paper Filter MeasureTheory ProbabilityTheory
open AdaptiveResponseStrongLaw AdaptiveConditionalMoments AdaptiveRidgeConsistency
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

variable {Theta Action Outcome : Type}
  [MeasurableSpace Action] [MeasurableSpace Outcome]
  [Fintype Outcome] [MeasurableSingletonClass Outcome]
  [StandardBorelSpace Outcome] [Nonempty Outcome]

theorem map_initial (p : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta) :
    (adaptiveInfiniteTrajectoryMeasure p theta).map (fun path => path 0)=
      adaptiveInitialOutcomeMeasure p theta := by
  letI : ∀ n, IsMarkovKernel (adaptiveIonescuStepKernel p theta n) :=
    fun n => adaptiveIonescuStepKernel_isMarkov p theta n
  let e := MeasurableEquiv.piUnique (fun i : Finset.Iic (0:ℕ) => AdaptiveOutcomeProcess Outcome i)
  have hp : (adaptiveInfiniteTrajectoryMeasure p theta).map (Preorder.frestrictLe 0)=
      (adaptiveInitialOutcomeMeasure p theta).map e.symm := by
    unfold adaptiveInfiniteTrajectoryMeasure Kernel.trajMeasure
    rw [Measure.map_comp _ _ (by fun_prop),Kernel.traj_map_frestrictLe_of_le (le_refl 0)]
    rw [Measure.deterministic_comp_eq_map]
    have hid : Preorder.frestrictLe₂ (π:=AdaptiveOutcomeProcess Outcome) (le_refl (0:ℕ)) = id := by
      funext x
      rfl
    rw [hid,Measure.map_id]
  have he : (fun path : AdaptiveInfinitePath Outcome => path 0)=e ∘ Preorder.frestrictLe 0 := by
    funext path
    rfl
  rw [he,← Measure.map_map e.measurable (Preorder.measurable_frestrictLe 0),hp]
  exact e.map_map_symm

theorem initial_integral (p : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta)
    (g : Action → Outcome → ℝ) :
    ∫ path, actualResponse p g 0 path ∂adaptiveInfiniteTrajectoryMeasure p theta =
      ∫ y, g (p.design 0 AdaptiveTrajectory.empty) y ∂adaptiveInitialOutcomeMeasure p theta := by
  rw [← map_initial p theta,integral_map (measurable_pi_apply 0).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable]
  rfl

/-- Information before copy n; unlike piLE, this starts with the trivial sigma algebra. -/
def past : Filtration ℕ (inferInstance : MeasurableSpace (AdaptiveInfinitePath Outcome)) where
  seq := fun n => match n with
    | 0 => ⊥
    | k+1 => Filtration.piLE k
  mono' := by
    intro i j hij
    cases i with
    | zero => exact bot_le
    | succ i =>
      cases j with
      | zero => omega
      | succ j => exact Filtration.piLE.mono (by omega)
  le' := by
    intro n
    cases n with
    | zero => exact bot_le
    | succ n => exact Filtration.piLE.le n

theorem centered_past (p : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta)
    (g : Action → Outcome → ℝ) (hm : ∀ a, ∫ y, g a y ∂p.response theta a=0)
    (C : ℝ) (hb : ∀ a y, ‖g a y‖≤C) (n : ℕ) :
    (adaptiveInfiniteTrajectoryMeasure p theta)[actualResponse p g n | past n]
      =ᵐ[adaptiveInfiniteTrajectoryMeasure p theta] 0 := by
  cases n with
  | zero =>
    change (adaptiveInfiniteTrajectoryMeasure p theta)[actualResponse p g 0 | ⊥] =ᵐ[_] 0
    rw [condExp_bot,initial_integral]
    exact ae_of_all _ (fun _ => hm _)
  | succ n => exact actualResponse_condExp_zero p theta g hm C hb n

theorem scalar_variance_identity
    (p : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta)
    (g : Action → Outcome → ℝ) (hm : ∀ a, ∫ y, g a y ∂p.response theta a=0)
    (C : ℝ) (hb : ∀ a y, ‖g a y‖≤C) (n : ℕ) :
    (∫ path, (∑ k ∈ Finset.range n,actualResponse p g k path)^2
      ∂adaptiveInfiniteTrajectoryMeasure p theta)=
      ∑ k ∈ Finset.range n, ∫ path, (actualResponse p g k path)^2
        ∂adaptiveInfiniteTrajectoryMeasure p theta := by
  apply L2MartingaleBudget.integral_partialSum_square
    (adaptiveInfiniteTrajectoryMeasure p theta) past (fun k => actualResponse p g k) _ _ _ n
  · intro k
    exact actualResponse_stronglyMeasurable_piLE p g k
  · exact centered_past p theta g hm C hb
  · intro k
    exact MemLp.of_bound ((actualResponse_stronglyMeasurable_piLE p g k).mono
      (Filtration.piLE.le k)).aestronglyMeasurable C (ae_of_all _ (fun path => hb _ _))

open scoped InnerProductSpace
open AdaptiveBudgetMoments

 theorem actual_mean_zero (p : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta)
    (g : Action → Outcome → ℝ) (hm : ∀ a, ∫ y, g a y ∂p.response theta a=0)
    (C : ℝ) (hb : ∀ a y, ‖g a y‖≤C) (n : ℕ) :
    ∫ path, actualResponse p g n path ∂adaptiveInfiniteTrajectoryMeasure p theta=0 := by
  rw [← integral_condExp (past.le n)]
  rw [integral_congr_ae (centered_past p theta g hm C hb n)]
  simp

 theorem integral_response_le (p : PredictableAdaptiveProtocol Theta (ℕ × Action) Outcome)
    (theta : Theta) (htime : ∀ n h, (p.design n h).1=n)
    (g : (ℕ × Action) → Outcome → ℝ) (C : ℝ) (hb : ∀ a y, ‖g a y‖≤C)
    (v : ℕ → ℝ) (hv : ∀ a, ∫ y, g a y ∂p.response theta a≤v a.1) (n : ℕ) :
    ∫ path, actualResponse p g n path ∂adaptiveInfiniteTrajectoryMeasure p theta≤v n := by
  cases n with
  | zero =>
    rw [initial_integral]
    simpa only [adaptiveInitialOutcomeMeasure,htime] using hv (p.design 0 AdaptiveTrajectory.empty)
  | succ n =>
    have h := actualResponse_condExp p theta g C hb n
    rw [← integral_condExp (Filtration.piLE.le n),integral_congr_ae h]
    have hi := integrable_condExp.congr h
    apply (integral_mono hi (integrable_const (v (n+1))) (fun path => ?_)).trans_eq
      (by simp)
    simpa only [htime] using hv (p.design (n+1) (adaptiveInfinitePathPrefix (n+1) path))

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

 theorem vectorSum_variance_identity
    (p : PredictableAdaptiveProtocol Theta (ℕ × Action) Outcome) (theta : Theta)
    (g : (ℕ × Action) → Outcome → E) (hm : ∀ a, ∫ y, g a y ∂p.response theta a=0)
    (C : ℝ) (hb : ∀ a y, ‖g a y‖≤C) (n : ℕ) :
    (∫ path, ‖vectorSum p g n path‖^2 ∂adaptiveInfiniteTrajectoryMeasure p theta)=
      ∑ k ∈ Finset.range n, ∫ path, ‖actualVectorResponse p g k path‖^2
        ∂adaptiveInfiniteTrajectoryMeasure p theta := by
  classical
  letI : IsMarkovKernel (p.response theta) := p.response_isMarkov theta
  let b := stdOrthonormalBasis ℝ E
  have hb' i a y : ‖⟪b i,g a y⟫_ℝ‖≤C :=
    (norm_inner_le_norm _ _).trans (by simpa [b.norm_eq_one] using hb a y)
  have hm' i a : (∫ y, ⟪b i,g a y⟫_ℝ ∂p.response theta a)=0 := by
    rw [integral_inner Integrable.of_finite,hm a,inner_zero_right]
  simp_rw [vectorSum_square_eq]
  rw [integral_finset_sum _ (fun i _ => scalarSum_square_integrable p theta _ C (hb' i) n)]
  simp_rw [scalarSum,scalar_variance_identity p theta _ (hm' _) C (hb' _)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← integral_finset_sum]
  · apply integral_congr_ae
    exact ae_of_all _ (fun path => by
      change (∑ i, ⟪b i,actualVectorResponse p g k path⟫_ℝ^2)=_
      exact b.sum_sq_inner_right _)
  · intro i _
    exact (MemLp.of_bound ((actualResponse_stronglyMeasurable_piLE p
      (fun a y => ⟪b i,g a y⟫_ℝ) k).mono (Filtration.piLE.le k)).aestronglyMeasurable
      C (ae_of_all _ (fun path => hb' i _ _)) :
      MemLp (actualResponse p (fun a y => ⟪b i,g a y⟫_ℝ) k) 2
        (adaptiveInfiniteTrajectoryMeasure p theta)).integrable_sq

 theorem vectorSum_secondMoment_sharp
    (p : PredictableAdaptiveProtocol Theta (ℕ × Action) Outcome) (theta : Theta)
    (htime : ∀ n h, (p.design n h).1=n)
    (g : (ℕ × Action) → Outcome → E) (hm : ∀ a, ∫ y, g a y ∂p.response theta a=0)
    (C : ℝ) (hb : ∀ a y, ‖g a y‖≤C)
    (v : ℕ → ℝ) (hv : ∀ a, ∫ y, ‖g a y‖^2 ∂p.response theta a≤v a.1) (n : ℕ) :
    (∫ path, ‖vectorSum p g n path‖^2 ∂adaptiveInfiniteTrajectoryMeasure p theta)≤
      ∑ k ∈ Finset.range n, v k := by
  rw [vectorSum_variance_identity p theta g hm C hb]
  apply Finset.sum_le_sum
  intro k hk
  exact integral_response_le p theta htime (fun a y => ‖g a y‖^2) (C^2)
    (fun a y => by
      rw [norm_pow,norm_norm]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb a y) 2) v hv k

 theorem vectorSum_mean_inner_zero
    (p : PredictableAdaptiveProtocol Theta (ℕ × Action) Outcome) (theta : Theta)
    (g : (ℕ × Action) → Outcome → E) (hm : ∀ a, ∫ y, g a y ∂p.response theta a=0)
    (C : ℝ) (hb : ∀ a y, ‖g a y‖≤C) (n : ℕ) (u : E) :
    ∫ path, ⟪u,vectorSum p g n path⟫_ℝ ∂adaptiveInfiniteTrajectoryMeasure p theta=0 := by
  letI : IsMarkovKernel (p.response theta) := p.response_isMarkov theta
  have hu a y : ‖⟪u,g a y⟫_ℝ‖≤‖u‖*C :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hb a y) (norm_nonneg u))
  simp only [vectorSum,inner_sum]
  change (∫ path, ∑ k ∈ Finset.range n, actualResponse p (fun a y => ⟪u,g a y⟫_ℝ) k path
    ∂adaptiveInfiniteTrajectoryMeasure p theta)=0
  rw [integral_finset_sum _ (fun k _ => actualResponse_integrable p theta _ (‖u‖*C) hu k)]
  change (∑ k ∈ Finset.range n, ∫ path,
    actualResponse p (fun a y => ⟪u,g a y⟫_ℝ) k path ∂adaptiveInfiniteTrajectoryMeasure p theta)=0
  simp_rw [actual_mean_zero p theta _ (fun a => by
    rw [integral_inner Integrable.of_finite,hm a,inner_zero_right]) (‖u‖*C) hu]
  simp

 theorem vectorSum_shift_secondMoment
    (p : PredictableAdaptiveProtocol Theta (ℕ × Action) Outcome) (theta : Theta)
    (g : (ℕ × Action) → Outcome → E) (hm : ∀ a, ∫ y, g a y ∂p.response theta a=0)
    (C : ℝ) (hb : ∀ a y, ‖g a y‖≤C) (n : ℕ) (u : E) :
    (∫ path, ‖vectorSum p g n path-u‖^2 ∂adaptiveInfiniteTrajectoryMeasure p theta)=
      (∫ path, ‖vectorSum p g n path‖^2 ∂adaptiveInfiniteTrajectoryMeasure p theta)+‖u‖^2 := by
  have hs := vectorSum_square_integrable p theta g C hb n
  have hi : Integrable (fun path => ⟪u,vectorSum p g n path⟫_ℝ)
      (adaptiveInfiniteTrajectoryMeasure p theta) := by
    simp only [vectorSum,inner_sum]
    apply integrable_finset_sum
    intro k hk
    exact actualResponse_integrable p theta _ (‖u‖*C) (fun a y =>
      (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hb a y) (norm_nonneg u))) k
  simp only [norm_sub_sq_real]
  simp_rw [show ∀ x : E, ⟪x,u⟫_ℝ=⟪u,x⟫_ℝ from fun x => (real_inner_comm x u).symm]
  rw [integral_add (f:=fun path => ‖vectorSum p g n path‖^2-2*⟪u,vectorSum p g n path⟫_ℝ)
    (g:=fun _ => ‖u‖^2) (hs.sub (hi.const_mul 2)) (integrable_const _)]
  rw [integral_sub hs (hi.const_mul 2),integral_const_mul,
    vectorSum_mean_inner_zero p theta g hm C hb]
  simp

end
end QubitOracle.AdaptiveDesign.AdaptiveExactMoments
