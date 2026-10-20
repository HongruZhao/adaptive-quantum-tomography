import QubitOracle.AdaptiveDesign.AdaptiveResponseStrongLaw
import QubitOracle.Paper.FiniteAdaptiveBornScoreClosure
import QubitOracle.AdaptiveDesign.ProbabilityZeroAlgebra
import QubitOracle.AdaptiveDesign.AdaptiveRidgeConsistency

/-!
# A sufficient preliminary rate from bounded adaptive noise

This is a proof-only rate, with no sample split or change of estimator.
Conditional Hoeffding bounds show that a bounded martingale average is
`o_P(n^(-1/4))`. This suffices to make its squared error negligible at the
root-n scale in the one-step argument. No moment or rate axiom is used.
-/

namespace QubitOracle.AdaptiveDesign.BoundedResponseQuarterRate

open Filter MeasureTheory ProbabilityTheory QubitOracle.Paper
open scoped BigOperators Topology ENNReal NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

variable {Omega : Type*} [MeasurableSpace Omega]

theorem subGaussian_mono {mu : Measure Omega} {X : Omega → ℝ} {c d : ℝ≥0}
    (h : HasSubgaussianMGF X c mu) (hcd : c ≤ d) : HasSubgaussianMGF X d mu where
  integrable_exp_mul := h.integrable_exp_mul
  mgf_le t := (h.mgf_le t).trans (Real.exp_le_exp.mpr (by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show (c : ℝ) ≤ (d : ℝ) from hcd) (sq_nonneg t))
      (by norm_num)))

theorem subGaussian_twoSided (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X : Omega → ℝ) (c : ℝ≥0) (h : HasSubgaussianMGF X c mu)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    mu.real {omega | epsilon ≤ ‖X omega‖} ≤
      2 * Real.exp (-epsilon ^ 2 / (2 * (c : ℝ))) := by
  have hsubset : {omega | epsilon ≤ ‖X omega‖} ⊆
      {omega | epsilon ≤ X omega} ∪ {omega | epsilon ≤ -X omega} := by
    intro omega ho
    change epsilon ≤ ‖X omega‖ at ho
    change epsilon ≤ X omega ∨ epsilon ≤ -X omega
    rw [Real.norm_eq_abs] at ho
    exact (le_abs.mp ho)
  have hp := h.measure_ge_le hepsilon
  have hm := h.neg.measure_ge_le hepsilon
  calc
    _ ≤ mu.real ({omega | epsilon ≤ X omega} ∪ {omega | epsilon ≤ -X omega}) :=
      measureReal_mono hsubset (by finiteness)
    _ ≤ mu.real {omega | epsilon ≤ X omega} + mu.real {omega | epsilon ≤ -X omega} :=
      measureReal_union_le _ _
    _ ≤ Real.exp (-epsilon ^ 2 / (2 * (c : ℝ))) + Real.exp (-epsilon ^ 2 / (2 * (c : ℝ))) :=
      add_le_add hp hm
    _ = _ := by ring

theorem exp_neg_le_inverse {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ x⁻¹ := by
  rw [Real.exp_neg]
  have he : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  exact (inv_le_inv₀ (Real.exp_pos x) hx).mpr he

theorem subGaussian_probability_bound (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X : Omega → ℝ) (c : ℝ≥0) (hc : 0 < (c : ℝ))
    (h : HasSubgaussianMGF X c mu) (epsilon : ℝ) (he : 0 < epsilon) :
    mu.real {omega | epsilon ≤ ‖X omega‖} ≤ 4 * (c : ℝ) / epsilon ^ 2 := by
  have hexp := exp_neg_le_inverse (div_pos (sq_pos_of_pos he) (mul_pos two_pos hc))
  have hbound := subGaussian_twoSided mu X c h epsilon he.le
  have heq : 2 * (epsilon ^ 2 / (2 * (c : ℝ)))⁻¹ = 4 * (c : ℝ) / epsilon ^ 2 := by
    field_simp
    ring
  calc
    _ ≤ 2 * Real.exp (-(epsilon ^ 2 / (2 * (c : ℝ)))) := by simpa only [neg_div] using hbound
    _ ≤ 2 * (epsilon ^ 2 / (2 * (c : ℝ)))⁻¹ := mul_le_mul_of_nonneg_left hexp two_pos.le
    _ = _ := heq

theorem subGaussian_tendstoInMeasure (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X : ℕ → Omega → ℝ) (c : ℕ → ℝ≥0)
    (hc : ∀ n, 0 < (c n : ℝ)) (h : ∀ n, HasSubgaussianMGF (X n) (c n) mu)
    (hlim : Tendsto (fun n => (c n : ℝ)) atTop (𝓝 0)) :
    TendstoInMeasure mu X atTop (fun _ => (0 : ℝ)) := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro epsilon he
  simp only [sub_zero]
  apply squeeze_zero (fun _ => measureReal_nonneg)
    (fun n => subGaussian_probability_bound mu (X n) (c n) (hc n) (h n) epsilon he)
  simpa using (hlim.const_mul 4).div_const (epsilon ^ 2)

/-- A positive sub-Gaussian envelope for every finite partial sum. -/
theorem boundedMartingale_sum_subGaussian
    [StandardBorelSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Omega))
    (X : ℕ → Omega → ℝ) (ha : StronglyAdapted F X) (hzero : X 0 = 0)
    (hcenter : ∀ n, mu[X (n+1) | F n] =ᵐ[mu] 0)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ n omega, ‖X n omega‖ ≤ C) :
    ∃ c : ℝ≥0, 0 < (c : ℝ) ∧ ∀ n,
      HasSubgaussianMGF (fun omega => ∑ i ∈ Finset.range (n+1), X i omega)
        (((n+1 : ℕ) : ℝ≥0) * c) mu := by
  let B := C+1
  have hB : 0 < B := by dsimp [B]; linarith
  let c : ℝ≥0 := (‖B - (-B)‖₊ / 2)^2
  have hc : 0 < (c : ℝ) := by
    change 0 < (‖B-(-B)‖ / 2 : ℝ)^2
    have : B - (-B) ≠ 0 := by linarith
    positivity
  let cX : ℕ → ℝ≥0 := fun n => if n = 0 then 0 else c
  have hsumc (n : ℕ) : ∑ i ∈ Finset.range (n+1), cX i = (n : ℝ≥0) * c := by
    induction n with
    | zero => simp [cX]
    | succ n ih =>
      rw [show Nat.succ n + 1 = (n+1)+1 by omega, Finset.sum_range_succ, ih]
      simp [cX, Nat.cast_succ]
      ring
  have hsub0 : HasSubgaussianMGF (X 0) (cX 0) mu := by
    simpa [cX, hzero] using (HasSubgaussianMGF.fun_zero (mu := mu))
  have hsub (n : ℕ) : HasCondSubgaussianMGF (F n) (F.le n) (X (n+1)) (cX (n+1)) mu := by
    have hm := (ha (n+1)).mono (F.le (n+1))
    have hb (omega : Omega) : X (n+1) omega ∈ Set.Icc (-B) B := by
      have h : |X (n+1) omega| ≤ B := by
        simpa only [Real.norm_eq_abs] using (hbound (n+1) omega).trans (show C ≤ B by dsimp [B]; linarith)
      exact abs_le.mp h
    simpa [cX, c] using hasCondSubgaussianMGF_of_mem_Icc_of_condExp_zero (F.le n) hm hb (hcenter n)
  refine ⟨c, hc, fun n => ?_⟩
  have h := HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF ha hsub0 (n+1) (fun i _ => hsub i)
  rw [hsumc n] at h
  apply subGaussian_mono h
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ n) (show 0 ≤ c from zero_le)

def quarterScale (n : ℕ) : ℝ := Real.sqrt (Real.sqrt ((n+1 : ℕ) : ℝ))

theorem quarterScale_pos (n : ℕ) : 0 < quarterScale n := by
  unfold quarterScale
  positivity

theorem quarterScale_sq (n : ℕ) : quarterScale n ^ 2 = Real.sqrt ((n+1 : ℕ) : ℝ) :=
  Real.sq_sqrt (Real.sqrt_nonneg _)

theorem quarterScaled_sum_tendstoInMeasure
    [StandardBorelSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Filtration ℕ (inferInstance : MeasurableSpace Omega))
    (X : ℕ → Omega → ℝ) (ha : StronglyAdapted F X) (hzero : X 0 = 0)
    (hcenter : ∀ n, mu[X (n+1) | F n] =ᵐ[mu] 0)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ n omega, ‖X n omega‖ ≤ C) :
    TendstoInMeasure mu
      (fun n omega => (quarterScale n / ((n+1 : ℕ) : ℝ)) *
        ∑ i ∈ Finset.range (n+1), X i omega) atTop (fun _ => (0 : ℝ)) := by
  obtain ⟨c, hc, hsg⟩ := boundedMartingale_sum_subGaussian mu F X ha hzero hcenter C hC hbound
  let b : ℕ → ℝ≥0 := fun n => ⟨(c : ℝ) / Real.sqrt ((n+1 : ℕ) : ℝ), by positivity⟩
  have hb (n : ℕ) : 0 < (b n : ℝ) :=
    div_pos hc (Real.sqrt_pos.mpr (by positivity))
  have hnormalized (n : ℕ) : HasSubgaussianMGF
      (fun omega => (quarterScale n / ((n+1 : ℕ) : ℝ)) *
        ∑ i ∈ Finset.range (n+1), X i omega) (b n) mu := by
    have h := (hsg n).const_mul (quarterScale n / ((n+1 : ℕ) : ℝ))
    convert h using 1
    apply NNReal.eq
    change (c : ℝ) / Real.sqrt ((n+1 : ℕ) : ℝ) =
      (quarterScale n / ((n+1 : ℕ) : ℝ)) ^ 2 * (((n+1 : ℕ) : ℝ) * (c : ℝ))
    rw [div_pow, quarterScale_sq]
    have hn : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
    have hs := Real.sq_sqrt hn.le
    have hspos := Real.sqrt_pos.mpr hn
    field_simp
    nlinarith
  apply subGaussian_tendstoInMeasure mu _ b hb hnormalized
  exact (constant_div_sqrt_nat_tendsto_zero (c : ℝ)).comp (tendsto_add_atTop_nat 1)

theorem quarterScale_div_tendsto_zero :
    Tendsto (fun n : ℕ => quarterScale n / ((n+1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hb (n : ℕ) : quarterScale n ≤ Real.sqrt ((n+1 : ℕ) : ℝ) := by
    unfold quarterScale
    have h1 : 1 ≤ Real.sqrt ((n+1 : ℕ) : ℝ) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      norm_num
    have hs := Real.sq_sqrt (Real.sqrt_nonneg ((n+1 : ℕ) : ℝ))
    nlinarith [Real.sqrt_nonneg (Real.sqrt ((n+1 : ℕ) : ℝ))]
  apply squeeze_zero (fun n => (div_pos (quarterScale_pos n) (by positivity)).le)
    (fun n => (div_le_div_of_nonneg_right (hb n) (by positivity)).trans_eq ?_)
    ((constant_div_sqrt_nat_tendsto_zero 1).comp (tendsto_add_atTop_nat 1))
  have hn : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  have hs := Real.sq_sqrt hn.le
  have hsp := Real.sqrt_pos.mpr hn
  change Real.sqrt ((n+1 : ℕ) : ℝ) / ((n+1 : ℕ) : ℝ) = 1 / Real.sqrt ((n+1 : ℕ) : ℝ)
  field_simp
  nlinarith

section ActualResponses

open AdaptiveResponseStrongLaw AdaptiveRidgeConsistency
open scoped InnerProductSpace

variable {Theta Action Outcome E : Type*}
  [MeasurableSpace Action] [MeasurableSpace Outcome]
  [Fintype Outcome] [MeasurableSingletonClass Outcome]
  [StandardBorelSpace Outcome] [Nonempty Outcome]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem actualResponse_quarterRate
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta)
    (g : Action → Outcome → ℝ)
    (hmean : ∀ a, ∫ y, g a y ∂protocol.response theta a = 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ a y, ‖g a y‖ ≤ C) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure protocol theta)
      (fun n path => (quarterScale n / ((n+1 : ℕ) : ℝ)) *
        ∑ k ∈ Finset.range (n+1), actualResponse protocol g k path) atTop (fun _ => (0 : ℝ)) := by
  let mu := adaptiveInfiniteTrajectoryMeasure protocol theta
  let shifted : ℕ → AdaptiveInfinitePath Outcome → ℝ
    | 0, _ => 0
    | k+1, path => actualResponse protocol g (k+1) path
  have ha : StronglyAdapted MeasureTheory.Filtration.piLE shifted := by
    intro n
    cases n with
    | zero => exact stronglyMeasurable_const
    | succ n => exact actualResponse_stronglyMeasurable_piLE protocol g (n+1)
  have hc (n : ℕ) : mu[shifted (n+1) | MeasureTheory.Filtration.piLE n] =ᵐ[mu] 0 :=
    actualResponse_condExp_zero protocol theta g hmean C hb n
  have hbs (n : ℕ) (path : AdaptiveInfinitePath Outcome) : ‖shifted n path‖ ≤ C := by
    cases n with
    | zero => simpa [shifted] using hC
    | succ n => exact hb _ _
  have hs := quarterScaled_sum_tendstoInMeasure mu MeasureTheory.Filtration.piLE shifted ha rfl hc C hC hbs
  have hi : TendstoInMeasure mu
      (fun n path => (quarterScale n / ((n+1 : ℕ) : ℝ)) * actualResponse protocol g 0 path)
      atTop (fun _ => (0 : ℝ)) := by
    apply ProbabilityZeroAlgebra.uniform_norm_bound
      (fun n => (quarterScale n / ((n+1 : ℕ) : ℝ)) * C)
      (by simpa using quarterScale_div_tendsto_zero.mul_const C)
    intro n path
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg
      (div_pos (quarterScale_pos n) (by positivity)).le]
    exact mul_le_mul_of_nonneg_left (hb _ _) (div_pos (quarterScale_pos n) (by positivity)).le
  have hadd := ProbabilityZeroAlgebra.add hs hi
  have heq (n : ℕ) (path : AdaptiveInfinitePath Outcome) :
      (∑ k ∈ Finset.range (n+1), shifted k path) + actualResponse protocol g 0 path =
        ∑ k ∈ Finset.range (n+1), actualResponse protocol g k path := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp [shifted]
  convert hadd using 1
  funext n path
  rw [← mul_add, heq]

theorem actualVectorResponse_quarterRate
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta)
    (g : Action → Outcome → E)
    (hmean : ∀ a, ∫ y, g a y ∂protocol.response theta a = 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ a y, ‖g a y‖ ≤ C) :
    TendstoInMeasure (adaptiveInfiniteTrajectoryMeasure protocol theta)
      (fun n path => (quarterScale n / ((n+1 : ℕ) : ℝ)) •
        ∑ k ∈ Finset.range (n+1), actualVectorResponse protocol g k path) atTop (fun _ => (0 : E)) := by
  letI : IsMarkovKernel (protocol.response theta) := protocol.response_isMarkov theta
  let b := stdOrthonormalBasis ℝ E
  have hc (i : Fin (Module.finrank ℝ E)) :=
    actualResponse_quarterRate protocol theta (fun a y => ⟪b i, g a y⟫_ℝ)
      (fun a => by rw [integral_inner Integrable.of_finite, hmean a, inner_zero_right]) C hC
      (fun a y => (norm_inner_le_norm _ _).trans (by simpa [b.norm_eq_one] using hb a y))
  have hs := ProbabilityZeroAlgebra.finite_sum Finset.univ
    (fun i n path => ((quarterScale n / ((n+1 : ℕ) : ℝ)) *
      ∑ k ∈ Finset.range (n+1), ⟪b i, actualVectorResponse protocol g k path⟫_ℝ) • b i)
    (fun i _ => ProbabilityZeroAlgebra.smul_fixed (hc i) (b i))
  simpa only [← inner_sum, ← inner_smul_right, b.sum_repr', zero_smul, Finset.sum_const_zero] using hs

end ActualResponses

end
end QubitOracle.AdaptiveDesign.BoundedResponseQuarterRate
