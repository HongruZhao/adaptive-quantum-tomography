import QubitOracle.AdaptiveDesign.BoundedMartingaleSecondMoment
import QubitOracle.AdaptiveDesign.ExplorationKronecker

/-! Exploration-normalized strong law. The cumulative exploration need only
diverge; its rate relative to n is not used for consistency. -/
namespace QubitOracle.AdaptiveDesign.ExplorationBudgetStrongLaw
open Filter MeasureTheory ProbabilityTheory BoundedMartingaleSecondMoment
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false

def mass (ε : ℕ → ℝ) (n : ℕ) : ℝ := 1+∑ k ∈ Finset.range n, ε k

lemma mass_succ (ε : ℕ → ℝ) (n : ℕ) : mass ε (n+1) = mass ε n+ε n := by
  simp only [mass, Finset.sum_range_succ]
  ring

lemma mass_ge_one (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (n : ℕ) : 1 ≤ mass ε n := by
  have h := Finset.sum_nonneg (s:=Finset.range n) (fun k _ => hε k)
  dsimp [mass]
  linarith

lemma mass_pos (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (n : ℕ) : 0 < mass ε n :=
  lt_of_lt_of_le zero_lt_one (mass_ge_one ε hε n)

lemma mass_mono (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) : Monotone (mass ε) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [mass_succ]
  linarith [hε n]

lemma variance_weight_bound (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (n : ℕ) :
    ∑ k ∈ Finset.range n, ε k / mass ε (k+1)^2 ≤ 1 := by
  have hterm (k : ℕ) : ε k / mass ε (k+1)^2 ≤ (mass ε k)⁻¹-(mass ε (k+1))⁻¹ := by
    have hp := mass_pos ε hε k
    have hq := mass_pos ε hε (k+1)
    have hle := mass_mono ε hε (Nat.le_succ k)
    have heq : (mass ε k)⁻¹-(mass ε (k+1))⁻¹ = ε k/(mass ε k*mass ε (k+1)) := by
      have hq' : mass ε k+ε k ≠ 0 := by rw [← mass_succ]; exact hq.ne'
      rw [mass_succ]
      field_simp [hp.ne', hq']
      ring
    rw [heq]
    exact div_le_div_of_nonneg_left (hε k) (mul_pos hp hq)
      (by nlinarith [mul_le_mul_of_nonneg_right hle hq.le])
  calc
    _ ≤ ∑ k ∈ Finset.range n, ((mass ε k)⁻¹-(mass ε (k+1))⁻¹) :=
      Finset.sum_le_sum (fun k _ => hterm k)
    _ = 1-(mass ε n)⁻¹ := by
      induction n with
      | zero => simp [mass]
      | succ n ih => rw [Finset.sum_range_succ, ih]; ring
    _ ≤ 1 := by have h := inv_nonneg.mpr (mass_pos ε hε n).le; linarith

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (F : Filtration ℕ ‹MeasurableSpace Ω›) (X : ℕ → Ω → ℝ)
  (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n))
  (hc : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
  (B : ℕ → ℝ) (hb : ∀ n ω, ‖X n ω‖ ≤ B n)

include ha hc hb in
/-- A literal martingale strong law with a variance budget. It assumes
conditional centering and a second-moment bound, not estimator consistency. -/
theorem normalized_sum_ae
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hinf : Tendsto (mass ε) atTop atTop)
    (V : ℝ) (hV : 0 ≤ V) (hv : ∀ n, ∫ ω, X n ω ^ 2 ∂μ ≤ V*ε n) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => partialSum X n ω / mass ε n) atTop (𝓝 0) := by
  let Y := fun n ω => (mass ε (n+1))⁻¹ * X n ω
  have hYa (n : ℕ) : StronglyMeasurable[F (n+1)] (Y n) := (ha n).const_mul _
  have hYc (n : ℕ) : μ[Y n | F n] =ᵐ[μ] 0 := by
    change μ[(mass ε (n+1))⁻¹ • X n | F n] =ᵐ[μ] 0
    have h := condExp_smul (μ:=μ) ((mass ε (n+1))⁻¹) (X n) (F n)
    simpa only [smul_zero] using h.trans ((hc n).const_smul ((mass ε (n+1))⁻¹))
  have hYb (n : ℕ) (ω : Ω) : ‖Y n ω‖ ≤ (mass ε (n+1))⁻¹*B n := by
    dsimp only [Y]
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (mass_pos ε hε (n+1)).le)]
    exact mul_le_mul_of_nonneg_left (hb n ω) (inv_nonneg.mpr (mass_pos ε hε (n+1)).le)
  have hYv (n : ℕ) : ∫ ω, Y n ω ^ 2 ∂μ ≤ V * (ε n / mass ε (n+1)^2) := by
    simp only [Y, mul_pow, integral_const_mul]
    calc
      _ ≤ (mass ε (n+1))⁻¹^2 * (V*ε n) :=
        mul_le_mul_of_nonneg_left (hv n) (sq_nonneg ((mass ε (n+1))⁻¹))
      _ = _ := by rw [inv_pow]; ring
  have hall (n : ℕ) : ∑ k ∈ Finset.range n, ∫ ω, Y k ω ^ 2 ∂μ ≤ V := by
    calc
      _ ≤ ∑ k ∈ Finset.range n, V*(ε k/mass ε (k+1)^2) := Finset.sum_le_sum (fun k _ => hYv k)
      _ = V*(∑ k ∈ Finset.range n, ε k/mass ε (k+1)^2) := by rw [Finset.mul_sum]
      _ ≤ V := by simpa using mul_le_mul_of_nonneg_left (variance_weight_bound ε hε n) hV
  have hconv := partialSum_ae_converges μ F Y hYa hYc
    (fun n => (mass ε (n+1))⁻¹*B n) hYb V hall
  filter_upwards [hconv] with ω hω
  obtain ⟨c,hc⟩ := hω
  apply ExplorationKronecker.normalized_sum_zero (mass ε) (fun k => X k ω)
    (mass_pos ε hε) (mass_mono ε hε) hinf c
  simpa only [partialSum, Y, div_eq_mul_inv, mul_comm] using hc

include ha hc hb in
/-- The mean-square size of the unnormalized noise is its exploration
budget, not the total number of copies. -/
theorem integral_sum_square_le
    (ε : ℕ → ℝ) (V : ℝ) (hv : ∀ n, ∫ ω, X n ω ^ 2 ∂μ ≤ V*ε n) (n : ℕ) :
    ∫ ω, partialSum X n ω ^ 2 ∂μ ≤ V * (∑ k ∈ Finset.range n, ε k) := by
  rw [integral_partialSum_square μ F X ha hc B hb n, Finset.mul_sum]
  exact Finset.sum_le_sum (fun k _ => hv k)

end
end QubitOracle.AdaptiveDesign.ExplorationBudgetStrongLaw
