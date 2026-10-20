import QubitOracle.AdaptiveDesign.BoundedMartingaleLogRate

/-! The almost-everywhere bounded and finite-coordinate versions of the
supplement's strong law. No finite sample space or regular conditional
distribution is assumed. -/
namespace QubitOracle.AdaptiveDesign.BoundedMartingaleLogRate
open MeasureTheory ProbabilityTheory Filter BoundedMartingaleSecondMoment
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem strong_law_of_ae_bounded (F : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hc : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n, ∀ᵐ ω ∂μ, ‖X n ω‖ ≤ C) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => partialSum X n ω/(n:ℝ)) atTop (𝓝 0) := by
  classical
  let Y := fun n ω => if ‖X n ω‖ ≤ C then X n ω else 0
  have hYa (n : ℕ) : StronglyMeasurable[F (n+1)] (Y n) :=
    StronglyMeasurable.ite (measurableSet_le (ha n).norm.measurable measurable_const)
      (ha n) stronglyMeasurable_const
  have he (n : ℕ) : Y n =ᵐ[μ] X n := by
    filter_upwards [hb n] with ω hω
    exact if_pos hω
  have hYb (n : ℕ) (ω : Ω) : ‖Y n ω‖ ≤ C := by
    dsimp only [Y]
    split_ifs with h
    · exact h
    · simpa using hC
  have hYc (n : ℕ) : μ[Y n | F n] =ᵐ[μ] 0 := (condExp_congr_ae (he n)).trans (hc n)
  filter_upwards [strong_law F Y hYa hYc C hC hYb,ae_all_iff.mpr he] with ω hω heω
  simpa only [partialSum,heω] using hω

theorem finite_coordinates {I : Type*} [Fintype I]
    (F : Filtration ℕ mΩ) (X : ℕ → Ω → EuclideanSpace ℝ I)
    (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hc : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n, ∀ᵐ ω ∂μ, ‖X n ω‖ ≤ C) :
    ∀ᵐ ω ∂μ, ∀ i,
      Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, X k ω i)/(n:ℝ)) atTop (𝓝 0) ∧
      (∀ᶠ n in atTop, ‖∑ k ∈ Finset.range (n+1), X k ω i‖ ≤
        (C+1)*Real.sqrt (6*((n+1:ℕ):ℝ)*Real.log ((n+2:ℕ):ℝ))) := by
  apply ae_all_iff.mpr
  intro i
  have hai (n : ℕ) : StronglyMeasurable[F (n+1)] (fun ω => X n ω i) :=
    (EuclideanSpace.proj i).continuous.comp_stronglyMeasurable (ha n)
  have hi (n : ℕ) : Integrable (X n) μ := Integrable.of_bound
    ((ha n).mono (F.le (n+1))).aestronglyMeasurable C (hb n)
  have hci (n : ℕ) : μ[(fun ω => X n ω i) | F n] =ᵐ[μ] 0 := by
    have he := (EuclideanSpace.proj i).comp_condExp_comm (m:=F n) (hi n)
    filter_upwards [he,hc n] with ω heω hcω
    simpa [Function.comp_def,hcω] using heω.symm
  have hbi (n : ℕ) : ∀ᵐ ω ∂μ, ‖X n ω i‖ ≤ C := by
    filter_upwards [hb n] with ω hω
    exact (PiLp.norm_apply_le (X n ω) i).trans hω
  have hbi' (n : ℕ) : ∀ᵐ ω ∂μ, ‖X n ω i‖ ≤ C+1 := by
    filter_upwards [hbi n] with ω hω
    linarith
  filter_upwards [strong_law_of_ae_bounded F (fun n ω => X n ω i) hai hci C hC hbi,
    logarithmic_rate_of_ae_bounded F (fun n ω => X n ω i) hai hci (C+1) (by positivity) hbi']
    with ω hω hrω
  exact ⟨hω,hrω⟩

end
end QubitOracle.AdaptiveDesign.BoundedMartingaleLogRate
