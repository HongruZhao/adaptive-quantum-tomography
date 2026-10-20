import QubitOracle.AdaptiveDesign.BoundedAdaptiveResponseCLT

/-!
# Conditional moments of the actual adaptive observations

The conditional-expectation identity is derived from the physical transition
kernel. No independence of the chosen measurements is assumed.
-/

namespace QubitOracle.AdaptiveDesign.AdaptiveConditionalMoments

open Filter MeasureTheory ProbabilityTheory QubitOracle.Paper
open AdaptiveResponseStrongLaw AdaptiveRidgeConsistency BoundedAdaptiveResponseCLT
open scoped BigOperators Topology InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

variable {Theta Action Outcome I : Type}
  [MeasurableSpace Action] [MeasurableSpace Outcome]
  [Fintype Outcome] [MeasurableSingletonClass Outcome]
  [StandardBorelSpace Outcome] [Nonempty Outcome] [Fintype I] [DecidableEq I]

theorem actualResponse_condExp
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta)
    (g : Action → Outcome → ℝ) (C : ℝ) (hbound : ∀ a y, ‖g a y‖ ≤ C) (n : ℕ) :
    (adaptiveInfiniteTrajectoryMeasure protocol theta)[
      actualResponse protocol g (n+1) | MeasureTheory.Filtration.piLE n]
      =ᵐ[adaptiveInfiniteTrajectoryMeasure protocol theta]
        (fun path => ∫ y, g
          (protocol.design (n+1) (adaptiveInfinitePathPrefix (n+1) path)) y
          ∂protocol.response theta
            (protocol.design (n+1) (adaptiveInfinitePathPrefix (n+1) path))) := by
  rw [MeasureTheory.Filtration.piLE_eq_comap_frestrictLe]
  let μ := adaptiveInfiniteTrajectoryMeasure protocol theta
  let X : AdaptiveInfinitePath Outcome → Prefix (Outcome := Outcome) n := Preorder.frestrictLe n
  let Ynext := fun path : AdaptiveInfinitePath Outcome => path (n+1)
  let f := fun z : Prefix (Outcome := Outcome) n × Outcome =>
    g (protocol.design (n+1) (iicToAdaptiveTrajectory z.1)) z.2
  have hX : Measurable X := Preorder.measurable_frestrictLe n
  have hY : Measurable Ynext := measurable_pi_apply (n+1)
  have hf : StronglyMeasurable f := (measurable_of_countable f).stronglyMeasurable
  have hi : Integrable (fun path => f (X path, Ynext path)) μ :=
    actualResponse_integrable protocol theta g C hbound (n+1)
  have hcond := condExp_prod_ae_eq_integral_condDistrib hX hY.aemeasurable hf hi
  have hprefix : condDistrib Ynext X μ =ᵐ[μ.map X]
      adaptiveIonescuStepKernel protocol theta n :=
    adaptiveInfiniteTrajectory_conditionalStep protocol theta n
  have hp := (ae_map_iff hX.aemeasurable
    (Set.Finite.measurableSet (Set.toFinite
      {pref | (condDistrib Ynext X μ) pref =
        adaptiveIonescuStepKernel protocol theta n pref}))).mp hprefix
  apply hcond.trans
  filter_upwards [hp] with path hpath
  rw [hpath]
  rfl

def secondMoment (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (theta : Theta) (g : Action → Outcome → EuclideanSpace ℝ I)
    (u : EuclideanSpace ℝ I) (a : Action) : ℝ :=
  ∫ y, ⟪u, g a y⟫_ℝ ^ 2 ∂protocol.response theta a

theorem projected_conditional_square
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta)
    (g : Action → Outcome → EuclideanSpace ℝ I) (u : EuclideanSpace ℝ I)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ a y, ‖g a y‖ ≤ C) (n k : ℕ) :
    (adaptiveInfiniteTrajectoryMeasure protocol theta)[
      (fun path => projected protocol g u n k path ^ 2) | MeasureTheory.Filtration.piLE k]
      =ᵐ[adaptiveInfiniteTrajectoryMeasure protocol theta]
        (fun path => normalization n ^ 2 * secondMoment protocol theta g u
          (protocol.design (k+1) (adaptiveInfinitePathPrefix (k+1) path))) := by
  have hb2 (a : Action) (y : Outcome) : ‖⟪u, g a y⟫_ℝ ^ 2‖ ≤ (‖u‖ * C)^2 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _)
      ((norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hb a y) (norm_nonneg u))) 2
  have hm := actualResponse_condExp protocol theta
    (fun a y => ⟪u, g a y⟫_ℝ ^ 2) ((‖u‖ * C)^2) hb2 k
  have hscale := condExp_smul (μ := adaptiveInfiniteTrajectoryMeasure protocol theta)
    (normalization n ^ 2)
    (actualResponse protocol (fun a y => ⟪u, g a y⟫_ℝ ^ 2) (k+1))
    (MeasureTheory.Filtration.piLE k)
  have heq : (fun path => projected protocol g u n k path ^ 2) =
      (normalization n ^ 2) • actualResponse protocol (fun a y => ⟪u, g a y⟫_ℝ ^ 2) (k+1) := by
    funext path
    simp only [projected, actualResponse, mul_pow, Pi.smul_apply, smul_eq_mul]
  rw [heq]
  exact hscale.trans (hm.const_smul (normalization n ^ 2))

theorem normalization_sq (n : ℕ) : normalization n ^ 2 = (n : ℝ)⁻¹ := by
  rw [normalization, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

theorem conditionalVariance_eq_average
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta)
    (g : Action → Outcome → EuclideanSpace ℝ I) (u : EuclideanSpace ℝ I)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ a y, ‖g a y‖ ≤ C) (n : ℕ) :
    hallHeydeArrayConditionalVariance (problem protocol theta g).mu
      (problem protocol theta g).filtration ((problem protocol theta g).projectedIncrement u) n
      =ᵐ[adaptiveInfiniteTrajectoryMeasure protocol theta]
        (fun path => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
          secondMoment protocol theta g u
            (protocol.design (k+1) (adaptiveInfinitePathPrefix (k+1) path))) := by
  have hall : ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure protocol theta, ∀ k,
      (adaptiveInfiniteTrajectoryMeasure protocol theta)[
        (fun path => projected protocol g u n k path ^ 2) | MeasureTheory.Filtration.piLE k] path =
          normalization n ^ 2 * secondMoment protocol theta g u
            (protocol.design (k+1) (adaptiveInfinitePathPrefix (k+1) path)) :=
    ae_all_iff.mpr (fun k => projected_conditional_square protocol theta g u C hC hb n k)
  filter_upwards [hall] with path hp
  rw [projected_eq]
  change (∑ k ∈ Finset.range n,
    (adaptiveInfiniteTrajectoryMeasure protocol theta)[
      (fun path => projected protocol g u n k path ^ 2) | MeasureTheory.Filtration.piLE k] path) = _
  simp_rw [hp]
  rw [← Finset.mul_sum, normalization_sq]

/-- Per-shot convergence of the actual conditional second moments suffices.
Its Cesaro consequence and the conditional-expectation identification are
proved here, rather than passed as a martingale-array variance hypothesis. -/
theorem covariance_of_secondMoment_limit
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta)
    (g : Action → Outcome → EuclideanSpace ℝ I)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ a y, ‖g a y‖ ≤ C)
    (M : Matrix I I ℝ)
    (hlim : ∀ u : EuclideanSpace ℝ I,
      ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure protocol theta,
      Tendsto (fun k => secondMoment protocol theta g u
        (protocol.design (k+1) (adaptiveInfinitePathPrefix (k+1) path))) atTop
        (𝓝 (martingaleScoreQuadraticForm M u))) :
    (problem protocol theta g).ConditionalCovarianceConverges M := by
  unfold MartingaleCLTProblem.ConditionalCovarianceConverges
  dsimp only [problem]
  intro u
  have havg : ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure protocol theta,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
        secondMoment protocol theta g u
          (protocol.design (k+1) (adaptiveInfinitePathPrefix (k+1) path))) atTop
          (𝓝 (martingaleScoreQuadraticForm M u)) := by
    filter_upwards [hlim u] with path hp
    exact hp.cesaro_smul
  have hall := ae_all_iff.mpr (fun n => conditionalVariance_eq_average protocol theta g u C hC hb n)
  have hpoint : ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure protocol theta,
      Tendsto (fun n => hallHeydeArrayConditionalVariance (adaptiveInfiniteTrajectoryMeasure protocol theta)
        (fun _ => MeasureTheory.Filtration.piLE) (projected protocol g u) n path)
        atTop (𝓝 (martingaleScoreQuadraticForm M u)) := by
    filter_upwards [havg, hall] with path hp heq
    simp only [projected_eq] at heq
    exact hp.congr (fun n => (heq n).symm)
  have hresult := tendstoInMeasure_of_tendsto_ae (fun n => by
    unfold hallHeydeArrayConditionalVariance
    apply Finset.aestronglyMeasurable_fun_sum
    intro k hk
    exact (stronglyMeasurable_condExp.mono
      (MeasureTheory.Filtration.piLE.le k)).aestronglyMeasurable) hpoint
  change TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure protocol theta)
    (hallHeydeArrayConditionalVariance (adaptiveInfiniteTrajectoryMeasure protocol theta)
      (fun _ => MeasureTheory.Filtration.piLE) ((problem protocol theta g).projectedIncrement u))
    atTop (fun _ => martingaleScoreQuadraticForm M u)
  rw [projected_eq]
  exact hresult

end
end QubitOracle.AdaptiveDesign.AdaptiveConditionalMoments
