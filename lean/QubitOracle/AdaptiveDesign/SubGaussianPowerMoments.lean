import QubitOracle.AdaptiveDesign.AdaptiveResponseTightness

/-! Polynomial moments from actual exponential-moment bounds. These
proofs do not assume a martingale moment inequality. Constants are deliberately
loose: only uniform finiteness at fixed moment orders is needed for risk. -/
namespace QubitOracle.AdaptiveDesign.SubGaussianPowerMoments
open MeasureTheory ProbabilityTheory Filter
open BoundedResponseQuarterRate
open scoped Topology BigOperators NNReal ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem abs_pow_le_exponentials (x : ℝ) (p : ℕ) :
    |x|^p ≤ (p:ℝ)^p * (Real.exp x + Real.exp (-x)) := by
  have h := rpow_abs_le_mul_max_exp_of_pos x (p := (p:ℝ)) (t := 1)
    (Nat.cast_nonneg p) zero_lt_one
  simp only [div_one, one_mul, neg_mul, Real.rpow_natCast] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (max_le_add_of_nonneg (Real.exp_pos x).le (Real.exp_pos (-x)).le) (by positivity))

theorem integral_abs_pow_le {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) (p : ℕ) :
    ∫ ω, |X ω|^p ∂μ ≤ 2 * (p:ℝ)^p * Real.exp ((c:ℝ)/2) := by
  have hi : Integrable (fun ω => |X ω|^p) μ :=
    integrable_pow_abs_of_integrable_exp_mul (by norm_num : (1:ℝ) ≠ 0)
      (h.integrable_exp_mul 1) (h.integrable_exp_mul (-1)) p
  have hp : Integrable (fun ω => Real.exp (X ω)) μ := by simpa using h.integrable_exp_mul 1
  have hn : Integrable (fun ω => Real.exp (-X ω)) μ := by simpa using h.integrable_exp_mul (-1)
  have bp : ∫ ω, Real.exp (X ω) ∂μ ≤ Real.exp ((c:ℝ)/2) := by simpa [mgf] using h.mgf_le 1
  have bn : ∫ ω, Real.exp (-X ω) ∂μ ≤ Real.exp ((c:ℝ)/2) := by simpa [mgf] using h.mgf_le (-1)
  calc
    _ ≤ ∫ ω, (p:ℝ)^p * (Real.exp (X ω) + Real.exp (-X ω)) ∂μ :=
      integral_mono hi ((hp.add hn).const_mul _) (fun ω => abs_pow_le_exponentials (X ω) p)
    _ = (p:ℝ)^p * ((∫ ω, Real.exp (X ω) ∂μ) + ∫ ω, Real.exp (-X ω) ∂μ) := by
      rw [integral_const_mul, integral_add hp hn]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left (add_le_add bp bn) (show 0 ≤ (p:ℝ)^p by positivity)]

/-- Uniformly bounded, centred martingale increments have uniformly
bounded root-n moments of every natural order. -/
theorem boundedMartingale_root_moments
    [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (X : ℕ → Ω → ℝ) (ha : StronglyAdapted F X) (hz : X 0 = 0)
    (hc : ∀ n, μ[X (n+1) | F n] =ᵐ[μ] 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n ω, ‖X n ω‖ ≤ C) (p : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      ∫ ω, |(Real.sqrt ((n+1:ℕ):ℝ))⁻¹ * ∑ k ∈ Finset.range (n+1), X k ω|^p ∂μ ≤ K := by
  obtain ⟨c,hc',hsg⟩ := boundedMartingale_sum_subGaussian μ F X ha hz hc C hC hb
  refine ⟨2*(p:ℝ)^p*Real.exp ((c:ℝ)/2), by positivity, fun n => ?_⟩
  have hs : HasSubgaussianMGF
      (fun ω => (Real.sqrt ((n+1:ℕ):ℝ))⁻¹ * ∑ k ∈ Finset.range (n+1), X k ω) c μ := by
    have h := (hsg n).const_mul (Real.sqrt ((n+1:ℕ):ℝ))⁻¹
    convert h using 1
    apply NNReal.eq
    change (c:ℝ) = (Real.sqrt ((n+1:ℕ):ℝ))⁻¹ ^ 2 * (((n+1:ℕ):ℝ)*(c:ℝ))
    rw [inv_pow, Real.sq_sqrt (by positivity)]
    field_simp
  exact integral_abs_pow_le hs p

end
end QubitOracle.AdaptiveDesign.SubGaussianPowerMoments
