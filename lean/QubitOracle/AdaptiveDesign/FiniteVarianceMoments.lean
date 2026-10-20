import QubitOracle.AdaptiveDesign.FiniteBernsteinTails
import QubitOracle.AdaptiveDesign.RealMomentBounds

/-! Variance-budget moments for arbitrary filtered finite-dimensional
martingale differences. No adaptive-tomography law is assumed here. -/
namespace QubitOracle.AdaptiveDesign.BoundedVarianceMGF
open MeasureTheory ProbabilityTheory Filter BoundedMartingaleSecondMoment AdaptiveResponseMoments
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem vector_uniformMoment {I : Type*} [Fintype I]
    (F : Filtration ℕ mΩ) (X : ℕ → Ω → EuclideanSpace ℝ I)
    (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hc : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n ω, ‖X n ω‖ ≤ C)
    (v : ℕ → ℝ) (hv : ∀ n, ∀ᵐ ω ∂μ, μ[fun ω => ‖X n ω‖^2 | F n] ω ≤ v n)
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n) (hCR : ∀ n, C ≤ R n)
    (hVR : ∀ n, (∑ k ∈ Finset.range n, v k) ≤ (R n)^2) (p : ℕ) :
    UniformMoment μ (fun n ω => (R n)⁻¹ • ∑ k ∈ Finset.range n, X k ω) p := by
  classical
  have hai (i : I) (k : ℕ) : StronglyMeasurable[F (k+1)] (fun ω => X k ω i) :=
    (EuclideanSpace.proj i).continuous.comp_stronglyMeasurable (ha k)
  have hib (i : I) (k : ℕ) (ω : Ω) : ‖X k ω i‖ ≤ C :=
    (PiLp.norm_apply_le (X k ω) i).trans (hb k ω)
  have hi (k : ℕ) : Integrable (X k) μ := Integrable.of_bound
    ((ha k).mono (F.le (k+1))).aestronglyMeasurable C (Eventually.of_forall (hb k))
  have hci (i : I) (k : ℕ) : μ[(fun ω => X k ω i) | F k] =ᵐ[μ] 0 := by
    have he := (EuclideanSpace.proj i).comp_condExp_comm (m:=F k) (hi k)
    filter_upwards [he,hc k] with ω heω hcω
    simpa [Function.comp_def,hcω] using heω.symm
  have hvi (i : I) (k : ℕ) :
      ∀ᵐ ω ∂μ, μ[fun ω => (X k ω i)^2 | F k] ω ≤ v k := by
    have hleft : Integrable (fun ω => (X k ω i)^2) μ := Integrable.of_bound
      (((hai i k).mono (F.le (k+1))).pow 2).aestronglyMeasurable (C^2)
      (Eventually.of_forall (fun ω => by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hib i k ω) 2))
    have hright : Integrable (fun ω => ‖X k ω‖^2) μ := Integrable.of_bound
      (((ha k).mono (F.le (k+1))).norm.pow 2).aestronglyMeasurable (C^2)
      (Eventually.of_forall (fun ω => by rw [norm_pow,norm_norm]; exact pow_le_pow_left₀ (norm_nonneg _) (hb k ω) 2))
    have hm := condExp_mono (m:=F k) hleft hright (Eventually.of_forall (fun ω => by
      have hh := pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le (X k ω) i) 2
      simpa only [Real.norm_eq_abs,sq_abs] using hh))
    filter_upwards [hm,hv k] with ω hmω hvω
    exact hmω.trans hvω
  have hs (i : I) := (uniformMoment F _ (hai i) (hci i) C hC (hib i) v (hvi i)
    R hR hCR hVR p).norm
  have hsum := UniformMoment.finite_sum Finset.univ _ (fun i _ => hs i)
  refine hsum.of_dominated _ ?_ 1 (by norm_num) ?_
  · intro n
    have hm (k : ℕ) : StronglyMeasurable (X k) := (ha k).mono (F.le (k+1))
    fun_prop
  · intro n ω
    simp only [one_mul]
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ => norm_nonneg _))]
    simpa only [PiLp.smul_apply,smul_eq_mul,WithLp.ofLp_sum,Finset.sum_apply,
      partialSum,Real.norm_eq_abs] using
      euclidean_norm_le_sum_abs ((R n)⁻¹ • ∑ k ∈ Finset.range n, X k ω)

theorem vector_real_moments {I : Type*} [Fintype I]
    (F : Filtration ℕ mΩ) (X : ℕ → Ω → EuclideanSpace ℝ I)
    (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hc : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n ω, ‖X n ω‖ ≤ C)
    (v : ℕ → ℝ) (hv : ∀ n, ∀ᵐ ω ∂μ, μ[fun ω => ‖X n ω‖^2 | F n] ω ≤ v n)
    (V : ℕ → ℝ) (hV : ∀ n, 0 ≤ V n)
    (hbudget : ∀ n, ∑ k ∈ Finset.range n, v k ≤ V n)
    (r : ℝ) (hr : 0 ≤ r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n,
      Integrable (fun ω => ‖∑ k ∈ Finset.range n, X k ω‖^r) μ ∧
      (∫ ω, ‖∑ k ∈ Finset.range n, X k ω‖^r ∂μ) ≤ K*(1+V n)^(r/2) := by
  let R := fun n => (1+C)*Real.sqrt (1+V n)
  have hVp (n : ℕ) : 0 < 1+V n := by linarith [hV n]
  have hR (n : ℕ) : 0 < R n := by dsimp [R]; exact mul_pos (by positivity) (Real.sqrt_pos.mpr (hVp n))
  have hs (n : ℕ) : 1 ≤ Real.sqrt (1+V n) := by
    rw [Real.le_sqrt (by norm_num) (hVp n).le]
    linarith [hV n]
  have hCR (n : ℕ) : C ≤ R n := by
    have hh := mul_le_mul_of_nonneg_left (hs n) (by positivity : 0 ≤ 1+C)
    dsimp [R]
    nlinarith
  have hVR (n : ℕ) : (∑ k ∈ Finset.range n, v k) ≤ (R n)^2 := by
    have he : (R n)^2=(1+C)^2*(1+V n) := by
      dsimp [R]
      rw [mul_pow,Real.sq_sqrt (hVp n).le]
    rw [he]
    exact (hbudget n).trans (by nlinarith [sq_nonneg C,mul_nonneg (hV n) (sq_nonneg C),mul_nonneg (hV n) hC])
  obtain ⟨K,hK,hKm⟩ := real_moments_of_all_integer
    (fun p _ => vector_uniformMoment F X ha hc C hC hb v hv R hR hCR hVR p) r hr
  refine ⟨K*(1+C)^r,by positivity,fun n => ?_⟩
  have he (ω : Ω) : ‖∑ k ∈ Finset.range n, X k ω‖^r=
      (R n)^r*‖(R n)⁻¹ • ∑ k ∈ Finset.range n, X k ω‖^r := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (hR n).le),
      Real.mul_rpow (by positivity) (norm_nonneg _),Real.inv_rpow (hR n).le]
    rw [← mul_assoc,mul_inv_cancel₀ (Real.rpow_pos_of_pos (hR n) r).ne',one_mul]
  have hi : Integrable (fun ω => ‖∑ k ∈ Finset.range n, X k ω‖^r) μ := by
    simpa only [he] using (hKm n).1.const_mul ((R n)^r)
  refine ⟨hi,?_⟩
  calc
    _ = (R n)^r*(∫ ω, ‖(R n)⁻¹ • ∑ k ∈ Finset.range n, X k ω‖^r ∂μ) := by
      simp only [he,integral_const_mul]
    _ ≤ (R n)^r*K := mul_le_mul_of_nonneg_left (hKm n).2 (by positivity)
    _ = _ := by
      dsimp only [R]
      rw [Real.mul_rpow (by positivity) (by positivity),Real.sqrt_eq_rpow,
        ← Real.rpow_mul (hVp n).le]
      rw [show (1 / 2:ℝ)*r=r/2 by ring]
      ring

end
end QubitOracle.AdaptiveDesign.BoundedVarianceMGF
