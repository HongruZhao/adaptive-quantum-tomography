import QubitOracle.AdaptiveDesign.AdaptiveConditionalMoments
import Mathlib.Probability.Martingale.Convergence

/-! Elementary second-moment accounting for bounded martingale differences.
Unlike a uniform Azuma bound, this retains the exploration probabilities. -/
namespace QubitOracle.AdaptiveDesign.BoundedMartingaleSecondMoment
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (F : Filtration ℕ ‹MeasurableSpace Ω›) (X : ℕ → Ω → ℝ)
  (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n))
  (hc : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
  (B : ℕ → ℝ) (hb : ∀ n ω, ‖X n ω‖ ≤ B n)

def partialSum (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ := ∑ k ∈ Finset.range n, X k ω

include ha hb in
lemma increment_integrable (n : ℕ) : Integrable (X n) μ :=
  Integrable.of_bound ((ha n).mono (F.le (n+1))).aestronglyMeasurable (B n) (ae_of_all _ (hb n))

include ha hb in
lemma increment_square_integrable (n : ℕ) : Integrable (fun ω => X n ω ^ 2) μ := by
  apply Integrable.of_bound (((ha n).mono (F.le (n+1))).pow 2).aestronglyMeasurable (B n ^ 2)
  filter_upwards [] with ω
  change ‖X n ω ^ 2‖ ≤ B n ^ 2
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hb n ω) 2

include ha in
lemma partialSum_adapted (n : ℕ) : StronglyMeasurable[F n] (partialSum X n) := by
  have h := Finset.stronglyMeasurable_sum (Finset.range n) (fun k hk =>
    (ha k).mono (F.mono (Nat.succ_le_iff.mpr (Finset.mem_range.mp hk))))
  convert h using 1
  funext ω
  simp [partialSum]

include hb in
lemma partialSum_bound (n : ℕ) (ω : Ω) : ‖partialSum X n ω‖ ≤ ∑ k ∈ Finset.range n, B k :=
  (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => hb k ω))

include ha hb in
lemma partialSum_integrable (n : ℕ) : Integrable (partialSum X n) μ :=
  Integrable.of_bound ((partialSum_adapted F X ha n).mono (F.le n)).aestronglyMeasurable
    (∑ k ∈ Finset.range n, B k) (ae_of_all _ (partialSum_bound X B hb n))

include ha hb in
lemma partialSum_square_integrable (n : ℕ) : Integrable (fun ω => partialSum X n ω ^ 2) μ := by
  apply Integrable.of_bound (((partialSum_adapted F X ha n).mono (F.le n)).pow 2).aestronglyMeasurable
    ((∑ k ∈ Finset.range n, B k)^2)
  filter_upwards [] with ω
  change ‖partialSum X n ω ^ 2‖ ≤ (∑ k ∈ Finset.range n, B k)^2
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (partialSum_bound X B hb n ω) 2

include ha hb in
lemma cross_integrable (n : ℕ) : Integrable (partialSum X n * X n) μ := by
  apply Integrable.of_bound
    (((partialSum_adapted F X ha n).mono (F.le n)).mul
      ((ha n).mono (F.le (n+1)))).aestronglyMeasurable
    ((∑ k ∈ Finset.range n, B k) * B n)
  filter_upwards [] with ω
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul (partialSum_bound X B hb n ω) (hb n ω) (norm_nonneg _)
    ((norm_nonneg _).trans (partialSum_bound X B hb n ω))

include ha hc hb in
lemma integral_cross_zero (n : ℕ) : ∫ ω, partialSum X n ω * X n ω ∂μ = 0 := by
  have h := condExp_mul_of_stronglyMeasurable_left (partialSum_adapted F X ha n)
    (cross_integrable μ F X ha B hb n) (increment_integrable μ F X ha B hb n)
  have hz : μ[partialSum X n * X n | F n] =ᵐ[μ] 0 := by
    filter_upwards [h,hc n] with ω hω hω'
    simp only [Pi.mul_apply, Pi.zero_apply, hω', mul_zero] at hω
    exact hω
  calc
    _ = ∫ ω, μ[partialSum X n * X n | F n] ω ∂μ := (integral_condExp (F.le n)).symm
    _ = 0 := by rw [integral_congr_ae hz]; simp

lemma partialSum_succ (n : ℕ) : partialSum X (n+1) = partialSum X n + X n := by
  funext ω
  exact Finset.sum_range_succ _ _

include ha hc hb in
theorem integral_partialSum_square (n : ℕ) :
    ∫ ω, partialSum X n ω ^ 2 ∂μ = ∑ k ∈ Finset.range n, ∫ ω, X k ω ^ 2 ∂μ := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
    have hic : Integrable (fun ω => partialSum X n ω * X n ω) μ := cross_integrable μ F X ha B hb n
    have he : (fun ω => partialSum X (n+1) ω ^ 2) =
        (fun ω => partialSum X n ω ^ 2 + 2*(partialSum X n ω * X n ω) + X n ω ^ 2) := by
      funext ω
      rw [partialSum_succ]
      simp only [Pi.add_apply]
      ring
    have hplus := integral_add
      ((partialSum_square_integrable μ F X ha B hb n).add (hic.const_mul 2))
      (increment_square_integrable μ F X ha B hb n)
    have hplus2 := integral_add (partialSum_square_integrable μ F X ha B hb n) (hic.const_mul 2)
    simp only [Pi.add_apply, Pi.mul_apply] at hplus hplus2
    rw [he, hplus, hplus2,
      integral_const_mul, integral_cross_zero μ F X ha hc B hb n,
      mul_zero, add_zero, ih, Finset.sum_range_succ]

include ha hc hb in
theorem partialSum_martingale : Martingale (partialSum X) F μ := by
  apply martingale_nat (partialSum_adapted F X ha) (partialSum_integrable μ F X ha B hb)
  intro n
  have ha' := condExp_add (partialSum_integrable μ F X ha B hb n)
    (increment_integrable μ F X ha B hb n) (F n)
  have hs := condExp_of_stronglyMeasurable (F.le n) (partialSum_adapted F X ha n)
    (partialSum_integrable μ F X ha B hb n)
  rw [partialSum_succ]
  filter_upwards [ha',hc n] with ω hω hω'
  rw [hs] at hω
  simp only [Pi.add_apply, hω', Pi.zero_apply, add_zero] at hω
  exact hω.symm

include ha hc hb in
/-- Finite total variance gives almost-sure convergence of the series.
This will be applied to exploration innovations divided by their budget. -/
theorem partialSum_ae_converges (V : ℝ)
    (hv : ∀ n, ∑ k ∈ Finset.range n, ∫ ω, X k ω ^ 2 ∂μ ≤ V) :
    ∀ᵐ ω ∂μ, ∃ c : ℝ, Tendsto (fun n => partialSum X n ω) atTop (𝓝 c) := by
  apply (partialSum_martingale μ F X ha hc B hb).submartingale.exists_ae_tendsto_of_bdd
    (R := Real.toNNReal (V+1))
  intro n
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm (partialSum_integrable μ F X ha B hb n)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∫ ω, partialSum X n ω ^ 2 + 1 ∂μ := by
      apply integral_mono (partialSum_integrable μ F X ha B hb n).norm
        ((partialSum_square_integrable μ F X ha B hb n).add (integrable_const 1))
      intro ω
      change ‖partialSum X n ω‖ ≤ partialSum X n ω ^ 2 + 1
      rw [Real.norm_eq_abs]
      nlinarith [sq_nonneg (|partialSum X n ω|-1), sq_abs (partialSum X n ω)]
    _ = (∑ k ∈ Finset.range n, ∫ ω, X k ω ^ 2 ∂μ)+1 := by
      rw [integral_add (partialSum_square_integrable μ F X ha B hb n) (integrable_const 1),
        integral_partialSum_square μ F X ha hc B hb n]
      simp
    _ ≤ V+1 := by linarith [hv n]

end
end QubitOracle.AdaptiveDesign.BoundedMartingaleSecondMoment
