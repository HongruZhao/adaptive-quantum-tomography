import QubitOracle.AdaptiveDesign.MartingaleCharacteristicBounds
import QubitOracle.AdaptiveDesign.FiniteAdaptiveResponseCLT

/-! A direct Gaussian limit for bounded martingale differences on arbitrary
filtered probability spaces. Current conditional covariance converges to a
deterministic limit; no independence, finite outcome space, or black-box
martingale central limit axiom is assumed. -/
namespace QubitOracle.AdaptiveDesign.MartingaleCharacteristic
open QubitOracle.Paper Filter MeasureTheory ProbabilityTheory
open BoundedMartingaleSecondMoment
open scoped BigOperators Topology InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem normalized_characteristic_tendsto (F : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hc : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n ω, ‖X n ω‖ ≤ C) (v : ℝ) (hv : 0 ≤ v)
    (hvar : ∀ᵐ ω ∂μ, Tendsto (fun k => variance (μ:=μ) F X k ω) atTop (𝓝 v)) (t : ℝ) :
    Tendsto (fun n : ℕ => characteristicSum (μ:=μ) X (t/Real.sqrt (n:ℝ)) n) atTop
      (𝓝 (Complex.exp (-(v:ℂ)*(t:ℂ)^2/2))) := by
  let e := varianceError (μ:=μ) F X v
  let K := |t|^3*C^3*Real.exp (|t| * C)
  have he := (varianceError_tendsto F X C hb v hvar).cesaro_smul
  have hlim : Tendsto (fun n : ℕ => t^2/2*((n:ℝ)⁻¹*∑ k ∈ Finset.range n,e k)+K/Real.sqrt (n:ℝ))
      atTop (𝓝 0) := by
    simpa only [smul_eq_mul,mul_zero,zero_add] using
      (he.const_mul (t^2/2)).add (constant_div_sqrt_nat_tendsto_zero K)
  have hd : Tendsto (fun n : ℕ =>
      ‖characteristicSum (μ:=μ) X (t/Real.sqrt (n:ℝ)) n-
        (1-((t/Real.sqrt (n:ℝ):ℝ):ℂ)^2*(v:ℂ)/2)^n‖) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
    filter_upwards [FiniteAdaptiveCharacteristic.normalized_euler_norm t v hv,eventually_ge_atTop 1] with n hn hn1
    have hh := characteristicSum_bound F X ha hc C hC hb (t/Real.sqrt (n:ℝ)) v hn n
    have hr := FiniteAdaptiveCharacteristic.normalized_remainder_bound C hC t n hn1
    rw [FiniteAdaptiveCharacteristic.sqrt_normalized_sq] at hh
    calc
      _ ≤ t^2/(n:ℝ)/2*(∑ k ∈ Finset.range n,e k)+
          (n:ℝ)*FiniteAdaptiveCharacteristic.characteristicRemainder (t/Real.sqrt (n:ℝ)) C := hh
      _ ≤ t^2/(n:ℝ)/2*(∑ k ∈ Finset.range n,e k)+K/Real.sqrt (n:ℝ) := by linarith
      _ = _ := by ring
  have hzero := tendsto_zero_iff_norm_tendsto_zero.mpr hd
  have hp := FiniteAdaptiveCharacteristic.normalized_euler_tendsto t v
  simpa only [sub_add_cancel,zero_add] using hzero.add hp

def normalizedSum (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Real.sqrt (n:ℝ))⁻¹*partialSum X n ω

theorem normalizedSum_measurable (F : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n)) (n : ℕ) : Measurable (normalizedSum X n) :=
  ((partialSum_adapted F X ha n).mono (F.le n)).measurable.const_mul _

theorem normalizedSum_charFun (F : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n)) (n : ℕ) (t : ℝ) :
    charFun (μ.map (normalizedSum X n)) t = characteristicSum (μ:=μ) X (t/Real.sqrt (n:ℝ)) n := by
  rw [charFun_apply_real,integral_map (normalizedSum_measurable F X ha n).aemeasurable (by fun_prop)]
  apply integral_congr_ae
  filter_upwards [] with ω
  unfold normalizedSum FiniteCharacteristicTaylor.phase
  congr 1
  push_cast
  ring

theorem scalar_clt (F : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hc : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n ω, ‖X n ω‖ ≤ C) (v : ℝ) (hv : 0 ≤ v)
    (hvar : ∀ᵐ ω ∂μ, Tendsto (fun k => variance (μ:=μ) F X k ω) atTop (𝓝 v)) :
    TendstoInDistribution (normalizedSum X) atTop id (fun _ => μ) (gaussianReal 0 v.toNNReal) where
  forall_aemeasurable n := (normalizedSum_measurable F X ha n).aemeasurable
  aemeasurable_limit := measurable_id.aemeasurable
  tendsto := by
    apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.2
    intro t
    change Tendsto (fun n => charFun (μ.map (normalizedSum X n)) t)
      atTop (𝓝 (charFun ((gaussianReal 0 v.toNNReal).map id) t))
    simp only [Measure.map_id,normalizedSum_charFun F X ha,charFun_gaussianReal,Complex.ofReal_zero,
      mul_zero,zero_mul,zero_sub,Real.toNNReal_of_nonneg hv,NNReal.coe_mk]
    convert normalized_characteristic_tendsto F X ha hc C hC hb v hv hvar t using 1 <;> congr 1 <;> ring

variable {I : Type} [Fintype I] [DecidableEq I]

theorem vector_clt (F : Filtration ℕ mΩ) (X : ℕ → Ω → EuclideanSpace ℝ I)
    (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hc : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n ω, ‖X n ω‖ ≤ C)
    (M : Matrix I I ℝ) (hM : M.PosSemidef)
    (hvar : ∀ u : EuclideanSpace ℝ I, ∀ᵐ ω ∂μ,
      Tendsto (fun k => variance (μ:=μ) F (fun k ω => ⟪u,X k ω⟫_ℝ) k ω) atTop
        (𝓝 (martingaleScoreQuadraticForm M u))) :
    TendstoInDistribution (fun (n : ℕ) ω => (Real.sqrt (n:ℝ))⁻¹ • ∑ k ∈ Finset.range n, X k ω)
      atTop id (fun _ => μ) (multivariateGaussian 0 M) := by
  let Y := fun (n : ℕ) ω => (Real.sqrt (n:ℝ))⁻¹ • ∑ k ∈ Finset.range n, X k ω
  have hYm (n : ℕ) : Measurable (Y n) := by
    apply StronglyMeasurable.measurable
    convert (Finset.stronglyMeasurable_sum (Finset.range n) (fun k _ => (ha k).mono (F.le (k+1)))).const_smul ((Real.sqrt (n:ℝ))⁻¹) using 1
    funext ω
    simp [Y]
  apply cramerWold_tendstoInDistribution Y (fun n => (hYm n).aemeasurable)
  intro u
  have hXi (n : ℕ) : Integrable (X n) μ := Integrable.of_bound
    ((ha n).mono (F.le (n+1))).aestronglyMeasurable C (Eventually.of_forall (hb n))
  have hcenter (n : ℕ) : μ[(fun ω => ⟪u,X n ω⟫_ℝ) | F n] =ᵐ[μ] 0 := by
    have he := (innerSL ℝ u).comp_condExp_comm (m:=F n) (hXi n)
    filter_upwards [he,hc n] with ω hω hcω
    simpa [Function.comp_def,hcω] using hω.symm
  have hscalar := scalar_clt F (fun k ω => ⟪u,X k ω⟫_ℝ)
    (fun n => stronglyMeasurable_const.inner (ha n)) hcenter
    (‖u‖*C) (mul_nonneg (norm_nonneg _) hC)
    (fun n ω => (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hb n ω) (norm_nonneg _)))
    (martingaleScoreQuadraticForm M u) (hM.dotProduct_mulVec_nonneg u.ofLp) (hvar u)
  have hprojection (n : ℕ) (ω : Ω) : ⟪u,Y n ω⟫_ℝ = normalizedSum (fun k ω => ⟪u,X k ω⟫_ℝ) n ω := by
    simp [Y,normalizedSum,partialSum,inner_smul_right,inner_sum]
  have hlimit := multivariateGaussian_map_inner M hM u
  refine
    { forall_aemeasurable := fun n => hscalar.forall_aemeasurable n |>.congr
        (Eventually.of_forall (fun ω => (hprojection n ω).symm))
      aemeasurable_limit := (Continuous.inner continuous_const continuous_id').aemeasurable
      tendsto := ?_ }
  let pvec : ProbabilityMeasure ℝ :=
    ⟨Measure.map ((innerSL ℝ) u) (multivariateGaussian 0 M),
      Measure.isProbabilityMeasure_map ((innerSL ℝ) u).measurable.aemeasurable⟩
  let pscalar : ProbabilityMeasure ℝ :=
    ⟨gaussianReal 0 (martingaleScoreQuadraticForm M u).toNNReal,inferInstance⟩
  have he : pvec=pscalar := Subtype.ext hlimit
  have ht : (⟨Measure.map (fun x => ⟪u,x⟫_ℝ) (multivariateGaussian 0 M),
    Measure.isProbabilityMeasure_map (Continuous.inner continuous_const continuous_id').aemeasurable⟩ :
    ProbabilityMeasure ℝ) = pvec := Subtype.ext rfl
  rw [ht,he]
  simpa only [pscalar,hprojection,Measure.map_id] using hscalar.tendsto

end
end QubitOracle.AdaptiveDesign.MartingaleCharacteristic
