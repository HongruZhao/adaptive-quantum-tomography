import QubitOracle.AdaptiveDesign.AdaptiveResponseStrongLaw
import QubitOracle.AdaptiveDesign.AdaptiveRidgeConsistency
import QubitOracle.AdaptiveDesign.BoundedResponseQuarterRate
import QubitOracle.AdaptiveDesign.ProbabilityCalculus
import QubitOracle.AdaptiveDesign.ProbabilityZeroAlgebra
import QubitOracle.Paper.AdaptiveTrajectoryExperiment
import QubitOracle.Paper.FiniteAdaptiveBornScoreClosure
/-! Root-n tightness of bounded adaptive responses, derived from Mathlib's
conditional Hoeffding inequality. No moment or rate theorem is postulated. -/

namespace QubitOracle.AdaptiveDesign.AdaptiveResponseTightness

open Filter MeasureTheory ProbabilityTheory QubitOracle.Paper
open BoundedResponseQuarterRate ProbabilityCalculus
open scoped BigOperators Topology ENNReal NNReal InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

variable {Ω : Type*} [MeasurableSpace Ω]

theorem subGaussian_tight (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (c : ℝ≥0) (hc : 0 < (c : ℝ))
    (h : ∀ n, HasSubgaussianMGF (X n) c μ) : TightNorm μ X atTop := by
  intro ε hε
  by_cases htop : ε = ∞
  · exact ⟨1, by norm_num, Eventually.of_forall (fun _ => htop ▸ le_top)⟩
  have he : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
  let B := Real.sqrt (4*(c : ℝ)/ε.toReal) + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hsq : 4*(c : ℝ) ≤ ε.toReal * B^2 := by
    have hs := Real.sq_sqrt (show 0 ≤ 4*(c : ℝ)/ε.toReal by positivity)
    have hs0 := Real.sqrt_nonneg (4*(c : ℝ)/ε.toReal)
    have hm : ε.toReal * (4*(c : ℝ)/ε.toReal) = 4*(c : ℝ) := by field_simp
    dsimp [B]
    nlinarith
  refine ⟨B,hB, Eventually.of_forall fun n => ?_⟩
  apply (ENNReal.toReal_le_toReal (measure_ne_top μ _) htop).mp
  change μ.real {ω | B ≤ ‖X n ω‖} ≤ ε.toReal
  exact (subGaussian_probability_bound μ (X n) c hc (h n) B hB).trans
    ((div_le_iff₀ (sq_pos_of_pos hB)).mpr (by nlinarith))

theorem rootScaled_sum_tight
    [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (X : ℕ → Ω → ℝ) (ha : StronglyAdapted F X) (hzero : X 0 = 0)
    (hcenter : ∀ n, μ[X (n+1) | F n] =ᵐ[μ] 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n ω, ‖X n ω‖ ≤ C) :
    TightNorm μ (fun n ω => (Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹ *
      ∑ k ∈ Finset.range (n+1), X k ω) atTop := by
  obtain ⟨c,hc,hsg⟩ := boundedMartingale_sum_subGaussian μ F X ha hzero hcenter C hC hb
  apply subGaussian_tight μ _ c hc
  intro n
  have h := (hsg n).const_mul (Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹
  convert h using 1
  apply NNReal.eq
  change (c : ℝ) = (Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹ ^ 2 * (((n+1 : ℕ) : ℝ) * (c : ℝ))
  rw [inv_pow, Real.sq_sqrt (by positivity)]
  field_simp

open AdaptiveResponseStrongLaw AdaptiveRidgeConsistency

variable {Theta Action Outcome E : Type*}
  [MeasurableSpace Action] [MeasurableSpace Outcome]
  [Fintype Outcome] [MeasurableSingletonClass Outcome]
  [StandardBorelSpace Outcome] [Nonempty Outcome]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem actualResponse_rootTight
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta)
    (g : Action → Outcome → ℝ)
    (hmean : ∀ a, ∫ y, g a y ∂protocol.response theta a = 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ a y, ‖g a y‖ ≤ C) :
    TightNorm (adaptiveInfiniteTrajectoryMeasure protocol theta)
      (fun n path => (Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹ *
        ∑ k ∈ Finset.range (n+1), actualResponse protocol g k path) atTop := by
  let μ := adaptiveInfiniteTrajectoryMeasure protocol theta
  let shifted : ℕ → AdaptiveInfinitePath Outcome → ℝ
    | 0, _ => 0
    | k+1, path => actualResponse protocol g (k+1) path
  have ha : StronglyAdapted MeasureTheory.Filtration.piLE shifted := by
    intro n
    cases n with
    | zero => exact stronglyMeasurable_const
    | succ n => exact actualResponse_stronglyMeasurable_piLE protocol g (n+1)
  have hc (n : ℕ) : μ[shifted (n+1) | MeasureTheory.Filtration.piLE n] =ᵐ[μ] 0 :=
    actualResponse_condExp_zero protocol theta g hmean C hb n
  have hbs (n : ℕ) (path : AdaptiveInfinitePath Outcome) : ‖shifted n path‖ ≤ C := by
    cases n with
    | zero => simpa [shifted] using hC
    | succ n => exact hb _ _
  have hs := rootScaled_sum_tight μ MeasureTheory.Filtration.piLE shifted ha rfl hc C hC hbs
  have hi : TendstoInMeasure μ
      (fun n path => (Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹ * actualResponse protocol g 0 path)
      atTop (fun _ => (0 : ℝ)) := by
    apply ProbabilityZeroAlgebra.uniform_norm_bound
      (fun n => (Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹ * C)
      (by simpa only [div_eq_mul_inv, mul_comm, Function.comp_def] using
        (constant_div_sqrt_nat_tendsto_zero C).comp (tendsto_add_atTop_nat 1))
    intro n path
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hb _ _) (by positivity)
  have hadd := tight_add hs (tight_of_zero hi)
  have heq (n : ℕ) (path : AdaptiveInfinitePath Outcome) :
      (∑ k ∈ Finset.range (n+1), shifted k path) + actualResponse protocol g 0 path =
        ∑ k ∈ Finset.range (n+1), actualResponse protocol g k path := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp [shifted]
  convert hadd using 1
  funext n path
  rw [← mul_add, heq]

theorem actualVectorResponse_rootTight
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta)
    (g : Action → Outcome → E)
    (hmean : ∀ a, ∫ y, g a y ∂protocol.response theta a = 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ a y, ‖g a y‖ ≤ C) :
    TightNorm (adaptiveInfiniteTrajectoryMeasure protocol theta)
      (fun n path => (Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹ •
        ∑ k ∈ Finset.range (n+1), actualVectorResponse protocol g k path) atTop := by
  letI : IsMarkovKernel (protocol.response theta) := protocol.response_isMarkov theta
  let b := stdOrthonormalBasis ℝ E
  have hc (i : Fin (Module.finrank ℝ E)) :=
    actualResponse_rootTight protocol theta (fun a y => ⟪b i, g a y⟫_ℝ)
      (fun a => by rw [integral_inner Integrable.of_finite, hmean a, inner_zero_right]) C hC
      (fun a y => (norm_inner_le_norm _ _).trans (by simpa [b.norm_eq_one] using hb a y))
  have hvec (i : Fin (Module.finrank ℝ E)) : TightNorm
      (adaptiveInfiniteTrajectoryMeasure protocol theta)
      (fun n path => ((Real.sqrt ((n+1 : ℕ) : ℝ))⁻¹ *
        ∑ k ∈ Finset.range (n+1), ⟪b i, actualVectorResponse protocol g k path⟫_ℝ) • b i) atTop := by
    apply tight_dominated (hc i) 1 (by norm_num)
    intro n path
    simp only [norm_smul, b.norm_eq_one, mul_one, one_mul]
    rfl
  have hs := tight_finite_sum Finset.univ _ (fun i _ => hvec i)
  simpa only [← inner_sum, ← inner_smul_right, b.sum_repr'] using hs

end
end QubitOracle.AdaptiveDesign.AdaptiveResponseTightness
