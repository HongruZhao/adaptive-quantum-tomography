import QubitOracle.AdaptiveDesign.AdaptiveBudgetHigherMoments

/-! Exponential localization from the exploration variance budget.
The estimates use the actual adaptive trajectory law and include the
initial observation, so there is no independence or deterministic-design
substitution. -/
namespace QubitOracle.AdaptiveDesign.AdaptiveBudgetConcentration
open QubitOracle.Paper Filter MeasureTheory ProbabilityTheory
open AdaptiveResponseStrongLaw AdaptiveConditionalMoments AdaptiveRidgeConsistency
open ExplorationBudgetStrongLaw BoundedMartingaleSecondMoment
open scoped BigOperators Topology InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {Theta Action Outcome : Type}
  [MeasurableSpace Action] [MeasurableSpace Outcome]
  [Fintype Outcome] [MeasurableSingletonClass Outcome]
  [StandardBorelSpace Outcome] [Nonempty Outcome]

theorem scalar_mgf
    (protocol : PredictableAdaptiveProtocol Theta (ℕ × Action) Outcome) (theta : Theta)
    (htime : ∀ n h, (protocol.design n h).1 = n)
    (g : (ℕ × Action) → Outcome → ℝ)
    (hmean : ∀ a, ∫ y, g a y ∂protocol.response theta a = 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ a y, ‖g a y‖ ≤ C)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (V : ℝ) (hV : 0 ≤ V)
    (hvar : ∀ a, ∫ y, g a y^2 ∂protocol.response theta a ≤ V*ε a.1)
    (t : ℝ) (ht : |t| * C ≤ 1) (n : ℕ) :
    (∫ path, Real.exp (t*∑ k ∈ Finset.range (n+1), actualResponse protocol g k path)
      ∂adaptiveInfiniteTrajectoryMeasure protocol theta) ≤
      Real.exp (|t| * C+t^2*V*mass ε (n+1)) := by
  let μ := adaptiveInfiniteTrajectoryMeasure protocol theta
  let X := fun k => actualResponse protocol g (k+1)
  have ha (k : ℕ) : StronglyMeasurable[Filtration.piLE (k+1)] (X k) :=
    actualResponse_stronglyMeasurable_piLE protocol g (k+1)
  have hc (k : ℕ) : μ[X k | Filtration.piLE k] =ᵐ[μ] 0 :=
    actualResponse_condExp_zero protocol theta g hmean C hb k
  have hv (k : ℕ) : ∀ᵐ path ∂μ,
      μ[fun path => X k path^2 | Filtration.piLE k] path ≤ V*ε (k+1) := by
    have hbg (a : ℕ × Action) (y : Outcome) : ‖g a y^2‖ ≤ C^2 := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb a y) 2
    have hh := actualResponse_condExp protocol theta (fun a y => g a y^2) (C^2) hbg k
    filter_upwards [hh] with path hp
    change μ[fun path => X k path^2 | Filtration.piLE k] path = _ at hp
    rw [hp]
    simpa only [htime] using hvar (protocol.design (k+1) (adaptiveInfinitePathPrefix (k+1) path))
  have hsum : (∑ k ∈ Finset.range n, V*ε (k+1)) ≤ V*mass ε (n+1) := by
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ hV
    dsimp [mass]
    rw [Finset.sum_range_succ']
    linarith [hε 0]
  have hi : Integrable (fun path => Real.exp (t*partialSum X n path)) μ := by
    apply (BoundedVarianceMGF.exp_memLp _
      (((partialSum_adapted Filtration.piLE X ha n).mono (Filtration.piLE.le n)).aestronglyMeasurable)
      ((n:ℝ)*C) (fun path => by
        simpa using partialSum_bound X (fun _ => C) (fun _ _ => hb _ _) n path) t 1).integrable le_rfl
  calc
    _ ≤ ∫ path, Real.exp (|t| * C)*Real.exp (t*partialSum X n path) ∂μ := by
      apply integral_mono_of_nonneg (Eventually.of_forall (fun _ => (Real.exp_pos _).le))
        (hi.const_mul _) (Eventually.of_forall ?_)
      intro path
      dsimp only
      rw [Finset.sum_range_succ', mul_add, Real.exp_add]
      change Real.exp (t*partialSum X n path)*Real.exp (t*actualResponse protocol g 0 path) ≤ _
      have h0 : Real.exp (t*actualResponse protocol g 0 path) ≤ Real.exp (|t| * C) := by
        simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
          BoundedVarianceMGF.exp_bound (actualResponse protocol g 0) C (fun _ => hb _ _) t path
      nlinarith [mul_le_mul_of_nonneg_left h0 (Real.exp_pos (t*partialSum X n path)).le]
    _ = Real.exp (|t| * C)*(∫ path, Real.exp (t*partialSum X n path) ∂μ) := integral_const_mul _ _
    _ ≤ Real.exp (|t| * C)*Real.exp (t^2*∑ k ∈ Finset.range n, V*ε (k+1)) :=
      mul_le_mul_of_nonneg_left
        (BoundedVarianceMGF.mgf_partialSum_le Filtration.piLE X ha hc C hC (fun _ _ => hb _ _)
          _ hv t ht n) (Real.exp_pos _).le
    _ ≤ Real.exp (|t| * C)*Real.exp (t^2*(V*mass ε (n+1))) := by
      gcongr
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- At every fixed positive distance the probability is exponentially
small in the expected exploration mass. -/
theorem scalar
    (protocol : PredictableAdaptiveProtocol Theta (ℕ × Action) Outcome) (theta : Theta)
    (htime : ∀ n h, (protocol.design n h).1 = n)
    (g : (ℕ × Action) → Outcome → ℝ)
    (hmean : ∀ a, ∫ y, g a y ∂protocol.response theta a = 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ a y, ‖g a y‖ ≤ C)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (V : ℝ) (hV : 0 ≤ V)
    (hvar : ∀ a, ∫ y, g a y^2 ∂protocol.response theta a ≤ V*ε a.1)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ B c : ℝ, 0 < B ∧ 0 < c ∧ ∀ n,
      (adaptiveInfiniteTrajectoryMeasure protocol theta).real
        {path | δ*mass ε (n+1) ≤ |∑ k ∈ Finset.range (n+1), actualResponse protocol g k path|} ≤
      B*Real.exp (-c*mass ε (n+1)) := by
  let μ := adaptiveInfiniteTrajectoryMeasure protocol theta
  let t := min ((C+1)⁻¹) (δ/(2*(V+1)))
  have ht : 0 < t := lt_min (inv_pos.mpr (by linarith)) (div_pos hδ (by positivity))
  have htC : t*C ≤ 1 := by
    calc
      _ ≤ (C+1)⁻¹*C := mul_le_mul_of_nonneg_right (min_le_left _ _) hC
      _ ≤ 1 := by rw [← div_eq_inv_mul]; apply (div_le_one (by linarith)).mpr; linarith
  have htV : t*V ≤ δ/2 := by
    calc
      _ ≤ t*(V+1) := mul_le_mul_of_nonneg_left (by linarith) ht.le
      _ ≤ δ/2 := by
        have hh := (le_div_iff₀ (by positivity : 0 < 2*(V+1))).mp
          (min_le_right ((C+1)⁻¹) (δ/(2*(V+1))))
        dsimp only [t]
        linarith
  refine ⟨2*Real.exp (t*C), t*δ/2, by positivity, by positivity, fun n => ?_⟩
  let S := fun path => ∑ k ∈ Finset.range (n+1), actualResponse protocol g k path
  let M := mass ε (n+1)
  have hM : 0 ≤ M := by
    dsimp [M,mass]
    exact add_nonneg zero_le_one (Finset.sum_nonneg (fun k _ => hε k))
  have hm : AEStronglyMeasurable S μ := by
    have hh : AEStronglyMeasurable (∑ k ∈ Finset.range (n+1), actualResponse protocol g k) μ :=
      (Finset.aestronglyMeasurable_sum (Finset.range (n+1)) (fun k _ =>
        ((actualResponse_stronglyMeasurable_piLE protocol g k).mono
          (Filtration.piLE.le k)).aestronglyMeasurable))
    convert hh using 1
    funext path
    simp [S]
  have hbS (path : AdaptiveInfinitePath Outcome) : ‖S path‖ ≤ ((n+1:ℕ):ℝ)*C := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _k ∈ Finset.range (n+1), C := Finset.sum_le_sum (fun k _ => hb _ _)
      _ = _ := by simp
  have htail (s : ℝ) (hs : |s| = t) :
      μ.real {path | δ*M ≤ (s/t)*S path} ≤ Real.exp (t*C-(t*δ/2)*M) := by
    have hh := measure_ge_le_exp_mul_mgf (μ:=μ) (X:=fun path => (s/t)*S path) (δ*M) ht.le
      (show Integrable (fun path => Real.exp (t*((s/t)*S path))) μ from by
        have he : (fun path => Real.exp (t*((s/t)*S path))) =
            (fun path => Real.exp (s*S path)) := by
          funext path; congr 1; field_simp
        rw [he]
        exact (BoundedVarianceMGF.exp_memLp S hm _ hbS s 1).integrable le_rfl)
    have he : (fun path => Real.exp (t*((s/t)*S path))) = (fun path => Real.exp (s*S path)) := by
      funext path; congr 1; field_simp
    have hmgf := scalar_mgf protocol theta htime g hmean C hC hb ε hε V hV hvar s
      (by rw [hs]; exact htC) n
    have hs2 : s^2 = t^2 := by rw [← sq_abs s, hs]
    change (∫ path, Real.exp (s*S path) ∂μ) ≤ _ at hmgf
    calc
      _ ≤ Real.exp (-t*(δ*M))*(∫ path, Real.exp (s*S path) ∂μ) := by simpa only [he, mgf] using hh
      _ ≤ Real.exp (-t*(δ*M))*Real.exp (|s| * C+s^2*V*M) :=
        mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
      _ = Real.exp (-t*(δ*M)+(t*C+t^2*V*M)) := by rw [← Real.exp_add,hs,hs2]
      _ ≤ _ := by apply Real.exp_le_exp.mpr; nlinarith [mul_le_mul_of_nonneg_left htV (mul_nonneg ht.le hM)]
  have hp := htail t (abs_of_pos ht)
  have hn := htail (-t) (by rw [abs_neg,abs_of_pos ht])
  have hun : {path | δ*M ≤ |S path|} ⊆
      {path | δ*M ≤ (t/t)*S path} ∪ {path | δ*M ≤ (-t/t)*S path} := by
    intro path hh
    simp only [Set.mem_ofPred_eq] at hh
    simpa [ht.ne',le_abs] using hh
  calc
    _ ≤ μ.real ({path | δ*M ≤ (t/t)*S path} ∪ {path | δ*M ≤ (-t/t)*S path}) := measureReal_mono hun
    _ ≤ μ.real {path | δ*M ≤ (t/t)*S path}+μ.real {path | δ*M ≤ (-t/t)*S path} := measureReal_union_le _ _
    _ ≤ 2*Real.exp (t*C-(t*δ/2)*M) := by linarith
    _ = _ := by rw [sub_eq_add_neg,Real.exp_add]; dsimp [M]; rw [neg_mul]; ring

end
end QubitOracle.AdaptiveDesign.AdaptiveBudgetConcentration
