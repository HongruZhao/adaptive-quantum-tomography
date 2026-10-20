import QubitOracle.AdaptiveDesign.BoundedVarianceMGF

/-! An all-threshold Bernstein bound from the proved conditional MGF.
The variance budget is deterministic; no independence is assumed. -/
namespace QubitOracle.AdaptiveDesign.BoundedVarianceMGF
open MeasureTheory ProbabilityTheory Filter BoundedMartingaleSecondMoment
open scoped BigOperators Topology ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem bernstein_upper
    (F : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hc : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n ω, ‖X n ω‖ ≤ C)
    (v : ℕ → ℝ) (hv : ∀ n, ∀ᵐ ω ∂μ, μ[fun ω => X n ω^2 | F n] ω ≤ v n)
    (n : ℕ) (V : ℝ) (hV : 0 ≤ V) (hbudget : ∑ k ∈ Finset.range n, v k ≤ V)
    (x : ℝ) (hx : 0 ≤ x) :
    μ.real {ω | x ≤ partialSum X n ω} ≤
      Real.exp (-(x^2)/(4*(1+C)*(1+V+x))) := by
  let B := (1+C)*(1+V+x)
  have hB : 0 < B := mul_pos (by linarith) (by linarith)
  let t := x/(2*B)
  have ht : 0 ≤ t := div_nonneg hx (by positivity)
  have hBV : V ≤ B := by dsimp [B]; nlinarith [mul_nonneg hC hV,mul_nonneg hC hx]
  have htC : t*C ≤ 1 := by
    dsimp [t]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 2*B)).mpr
    dsimp [B]
    nlinarith [mul_nonneg hC hV,mul_nonneg hC hx]
  have htV : t*V ≤ x/2 := by
    dsimp [t]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 2*B)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hBV hx]
  apply (upper_tail F X ha hc C hC hb v hv n x t ht htC).trans
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ -t*x+t^2*V := by nlinarith [mul_le_mul_of_nonneg_left hbudget (sq_nonneg t)]
    _ ≤ -t*x/2 := by nlinarith [mul_le_mul_of_nonneg_left htV ht]
    _ = _ := by dsimp [t,B]; field_simp; ring

theorem bernstein_abs
    (F : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hc : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n ω, ‖X n ω‖ ≤ C)
    (v : ℕ → ℝ) (hv : ∀ n, ∀ᵐ ω ∂μ, μ[fun ω => X n ω^2 | F n] ω ≤ v n)
    (n : ℕ) (V : ℝ) (hV : 0 ≤ V) (hbudget : ∑ k ∈ Finset.range n, v k ≤ V)
    (x : ℝ) (hx : 0 ≤ x) :
    μ.real {ω | x ≤ |partialSum X n ω|} ≤
      2*Real.exp (-(x^2)/(4*(1+C)*(1+V+x))) := by
  have hp := bernstein_upper F X ha hc C hC hb v hv n V hV hbudget x hx
  have hn := bernstein_upper F (fun k ω => -X k ω) (fun k => (ha k).neg)
    (fun k => by
      change μ[-X k | F k] =ᵐ[μ] 0
      exact (condExp_neg (X k) (F k)).trans (by simpa using (hc k).neg))
    C hC (fun k ω => by simpa using hb k ω) v (by simpa only [neg_sq] using hv)
    n V hV hbudget x hx
  have hs : {ω | x ≤ |partialSum X n ω|} ⊆
      {ω | x ≤ partialSum X n ω} ∪ {ω | x ≤ partialSum (fun k ω => -X k ω) n ω} := by
    intro ω hω
    change x ≤ |partialSum X n ω| at hω
    rcases le_abs.mp hω with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa [partialSum] using h)
  exact (measureReal_mono hs).trans ((measureReal_union_le _ _).trans (by linarith))

end
end QubitOracle.AdaptiveDesign.BoundedVarianceMGF
