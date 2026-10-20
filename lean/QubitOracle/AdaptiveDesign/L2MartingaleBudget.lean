import Mathlib.MeasureTheory.Function.L2Space
import QubitOracle.AdaptiveDesign.BoundedMartingaleSecondMoment
import QubitOracle.AdaptiveDesign.ExplorationBudgetStrongLaw
import QubitOracle.AdaptiveDesign.ExplorationKronecker
/-! The exploration-budget strong law with square-integrable increments.
There is no deterministic bound on an individual increment. This supplies
the probability lemma at the generality stated in the supplement. -/
namespace QubitOracle.AdaptiveDesign.L2MartingaleBudget
open Filter MeasureTheory ProbabilityTheory
open BoundedMartingaleSecondMoment ExplorationBudgetStrongLaw
open scoped BigOperators Topology ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (F : Filtration ℕ ‹MeasurableSpace Ω›) (X : ℕ → Ω → ℝ)
  (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n))
  (hc : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
  (hL2 : ∀ n, MemLp (X n) 2 μ)

include hL2 in
lemma partialSum_memLp (n : ℕ) : MemLp (partialSum X n) 2 μ := by
  have he : partialSum X n = ∑ k ∈ Finset.range n, X k := by
    funext ω
    simp [partialSum]
  rw [he]
  exact memLp_finsetSum' (Finset.range n) (fun k _ => hL2 k)

include ha hc hL2 in
lemma integral_cross_zero (n : ℕ) : ∫ ω, partialSum X n ω * X n ω ∂μ = 0 := by
  have hs := partialSum_memLp μ X hL2 n
  have h := condExp_mul_of_stronglyMeasurable_left (partialSum_adapted F X ha n)
    (hs.integrable_mul (hL2 n)) ((hL2 n).integrable (by norm_num))
  have hz : μ[partialSum X n * X n | F n] =ᵐ[μ] 0 := by
    filter_upwards [h,hc n] with ω hω hω'
    simpa only [Pi.mul_apply, hω', Pi.zero_apply, mul_zero] using hω
  calc
    _ = ∫ ω, μ[partialSum X n * X n | F n] ω ∂μ := (integral_condExp (F.le n)).symm
    _ = 0 := by rw [integral_congr_ae hz]; simp

include ha hc hL2 in
theorem integral_partialSum_square (n : ℕ) :
    ∫ ω, partialSum X n ω ^ 2 ∂μ = ∑ k ∈ Finset.range n, ∫ ω, X k ω ^ 2 ∂μ := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
    have hs := partialSum_memLp μ X hL2 n
    have hic : Integrable (fun ω => partialSum X n ω * X n ω) μ := hs.integrable_mul (hL2 n)
    have he : (fun ω => partialSum X (n+1) ω ^ 2) =
        (fun ω => partialSum X n ω ^ 2 + 2*(partialSum X n ω * X n ω) + X n ω ^ 2) := by
      funext ω
      rw [partialSum_succ]
      simp only [Pi.add_apply]
      ring
    have hplus := integral_add (hs.integrable_sq.add (hic.const_mul 2)) (hL2 n).integrable_sq
    have hplus' := integral_add hs.integrable_sq (hic.const_mul 2)
    simp only [Pi.add_apply] at hplus hplus'
    rw [he, hplus, hplus', integral_const_mul,
      integral_cross_zero μ F X ha hc hL2 n, mul_zero, add_zero, ih, Finset.sum_range_succ]

include ha hc hL2 in
theorem partialSum_martingale : Martingale (partialSum X) F μ := by
  have hi (n : ℕ) := (partialSum_memLp μ X hL2 n).integrable (by norm_num : (1:ENNReal) ≤ 2)
  apply martingale_nat (partialSum_adapted F X ha) hi
  intro n
  have ha' := condExp_add (hi n) ((hL2 n).integrable (by norm_num)) (F n)
  have hs := condExp_of_stronglyMeasurable (F.le n) (partialSum_adapted F X ha n) (hi n)
  rw [partialSum_succ]
  filter_upwards [ha',hc n] with ω hω hω'
  rw [hs] at hω
  simpa only [Pi.add_apply, hω', Pi.zero_apply, add_zero] using hω.symm

include ha hc hL2 in
theorem partialSum_ae_converges (V : ℝ)
    (hv : ∀ n, ∑ k ∈ Finset.range n, ∫ ω, X k ω ^ 2 ∂μ ≤ V) :
    ∀ᵐ ω ∂μ, ∃ c : ℝ, Tendsto (fun n => partialSum X n ω) atTop (𝓝 c) := by
  apply (partialSum_martingale μ F X ha hc hL2).submartingale.exists_ae_tendsto_of_bdd
    (R := Real.toNNReal (V+1))
  intro n
  have hi := (partialSum_memLp μ X hL2 n).integrable (by norm_num : (1:ENNReal) ≤ 2)
  rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hi]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∫ ω, partialSum X n ω ^ 2 + 1 ∂μ := by
      apply integral_mono hi.norm
        ((partialSum_memLp μ X hL2 n).integrable_sq.add (integrable_const 1))
      intro ω
      change ‖partialSum X n ω‖ ≤ partialSum X n ω ^ 2 + 1
      rw [Real.norm_eq_abs]
      nlinarith [sq_nonneg (|partialSum X n ω|-1), sq_abs (partialSum X n ω)]
    _ = (∑ k ∈ Finset.range n, ∫ ω, X k ω ^ 2 ∂μ)+1 := by
      rw [integral_add (partialSum_memLp μ X hL2 n).integrable_sq (integrable_const 1),
        integral_partialSum_square μ F X ha hc hL2 n]
      simp
    _ ≤ V+1 := by linarith [hv n]

include ha hc hL2 in
/-- A divergent deterministic variance budget suffices; increments need
only be in L2. The bound on their unconditional second moments is enough. -/
theorem normalized_sum_ae
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hinf : Tendsto (mass ε) atTop atTop)
    (V : ℝ) (hV : 0 ≤ V) (hv : ∀ n, ∫ ω, X n ω ^ 2 ∂μ ≤ V*ε n) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => partialSum X n ω / mass ε n) atTop (𝓝 0) := by
  let Y := fun n ω => (mass ε (n+1))⁻¹ * X n ω
  have hYa (n : ℕ) : StronglyMeasurable[F (n+1)] (Y n) := (ha n).const_mul _
  have hYc (n : ℕ) : μ[Y n | F n] =ᵐ[μ] 0 := by
    change μ[(mass ε (n+1))⁻¹ • X n | F n] =ᵐ[μ] 0
    exact (condExp_smul (μ:=μ) _ (X n) (F n)).trans (by simpa using (hc n).const_smul ((mass ε (n+1))⁻¹))
  have hY2 (n : ℕ) : MemLp (Y n) 2 μ := (hL2 n).const_mul _
  have hYv (n : ℕ) : ∫ ω, Y n ω ^ 2 ∂μ ≤ V * (ε n / mass ε (n+1)^2) := by
    simp only [Y, mul_pow, integral_const_mul]
    calc
      _ ≤ (mass ε (n+1))⁻¹^2 * (V*ε n) :=
        mul_le_mul_of_nonneg_left (hv n) (sq_nonneg _)
      _ = _ := by rw [inv_pow]; ring
  have hall (n : ℕ) : ∑ k ∈ Finset.range n, ∫ ω, Y k ω ^ 2 ∂μ ≤ V := by
    calc
      _ ≤ ∑ k ∈ Finset.range n, V*(ε k/mass ε (k+1)^2) := Finset.sum_le_sum (fun k _ => hYv k)
      _ = V*(∑ k ∈ Finset.range n, ε k/mass ε (k+1)^2) := by rw [Finset.mul_sum]
      _ ≤ V := by simpa using mul_le_mul_of_nonneg_left (variance_weight_bound ε hε n) hV
  have hconv := partialSum_ae_converges μ F Y hYa hYc hY2 V hall
  filter_upwards [hconv] with ω hω
  obtain ⟨c,hc'⟩ := hω
  apply ExplorationKronecker.normalized_sum_zero (mass ε) (fun k => X k ω)
    (mass_pos ε hε) (mass_mono ε hε) hinf c
  simpa only [partialSum, Y, div_eq_mul_inv, mul_comm] using hc'

include ha hc hL2 in
theorem normalized_sum_ae_of_conditional_variance
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hinf : Tendsto (mass ε) atTop atTop)
    (hv : ∀ n, ∀ᵐ ω ∂μ, μ[fun ω => X n ω ^ 2 | F n] ω ≤ ε n) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => partialSum X n ω / mass ε n) atTop (𝓝 0) := by
  apply normalized_sum_ae μ F X ha hc hL2 ε hε hinf 1 (by norm_num)
  intro n
  rw [← integral_condExp (F.le n)]
  simpa using integral_mono_ae integrable_condExp (integrable_const (ε n)) (hv n)

end
end QubitOracle.AdaptiveDesign.L2MartingaleBudget

namespace QubitOracle.AdaptiveDesign.L2MartingaleBudget
open Filter MeasureTheory ProbabilityTheory
open ExplorationBudgetStrongLaw
open scoped BigOperators Topology InnerProductSpace ENNReal
noncomputable section

/-- Finite-dimensional version, with an unconditional second-moment budget.
Conditional variance bounds imply this hypothesis by integration. -/
theorem vector_normalized_sum_ae {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ ‹MeasurableSpace Ω›) (X : ℕ → Ω → E)
    (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hc : ∀ n, μ[X n | F n] =ᵐ[μ] 0) (hL2 : ∀ n, MemLp (X n) 2 μ)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hinf : Tendsto (mass ε) atTop atTop)
    (V : ℝ) (hV : 0 ≤ V) (hv : ∀ n, ∫ ω, ‖X n ω‖ ^ 2 ∂μ ≤ V*ε n) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => (mass ε n)⁻¹ • ∑ k ∈ Finset.range n, X k ω)
      atTop (𝓝 0) := by
  classical
  let b := stdOrthonormalBasis ℝ E
  have hi (i : Fin (Module.finrank ℝ E)) :
      ∀ᵐ ω ∂μ, Tendsto (fun n =>
        (∑ k ∈ Finset.range n, ⟪b i, X k ω⟫_ℝ) / mass ε n) atTop (𝓝 0) := by
    have hcenter (n : ℕ) : μ[(fun ω => ⟪b i, X n ω⟫_ℝ) | F n] =ᵐ[μ] 0 := by
      have h := (innerSL ℝ (b i)).comp_condExp_comm (m := F n)
        ((hL2 n).integrable (by norm_num : (1:ENNReal) ≤ 2))
      filter_upwards [h,hc n] with ω hω hω'
      simpa [Function.comp_def, hω'] using hω.symm
    apply normalized_sum_ae μ F (fun n ω => ⟪b i, X n ω⟫_ℝ)
      (fun n => stronglyMeasurable_const.inner (ha n))
      hcenter (fun n => (hL2 n).const_inner (b i)) ε hε hinf V hV
    intro n
    apply (integral_mono ((hL2 n).const_inner (b i)).integrable_sq
      (hL2 n).norm.integrable_sq (fun ω => ?_)).trans (hv n)
    have h : ‖⟪b i, X n ω⟫_ℝ‖ ≤ ‖b i‖*‖X n ω‖ := norm_inner_le_norm _ _
    rw [b.norm_eq_one, one_mul, Real.norm_eq_abs] at h
    nlinarith [sq_abs ⟪b i, X n ω⟫_ℝ, abs_nonneg ⟪b i, X n ω⟫_ℝ, norm_nonneg (X n ω)]
  have hall := ae_all_iff.mpr hi
  filter_upwards [hall] with ω hω
  have hsum := tendsto_finset_sum Finset.univ (fun i _ => (hω i).smul_const (b i))
  simpa only [div_eq_mul_inv, mul_comm, ← inner_sum, ← inner_smul_right,
    b.sum_repr', zero_smul, Finset.sum_const_zero] using hsum

theorem vector_normalized_sum_ae_of_conditional_variance
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ ‹MeasurableSpace Ω›) (X : ℕ → Ω → E)
    (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hc : ∀ n, μ[X n | F n] =ᵐ[μ] 0) (hL2 : ∀ n, MemLp (X n) 2 μ)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hinf : Tendsto (mass ε) atTop atTop)
    (hv : ∀ n, ∀ᵐ ω ∂μ, μ[fun ω => ‖X n ω‖^2 | F n] ω ≤ ε n) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => (mass ε n)⁻¹ • ∑ k ∈ Finset.range n, X k ω)
      atTop (𝓝 0) := by
  apply vector_normalized_sum_ae μ F X ha hc hL2 ε hε hinf 1 (by norm_num)
  intro n
  rw [← integral_condExp (F.le n)]
  simpa using integral_mono_ae integrable_condExp (integrable_const (ε n)) (hv n)

end
end QubitOracle.AdaptiveDesign.L2MartingaleBudget
