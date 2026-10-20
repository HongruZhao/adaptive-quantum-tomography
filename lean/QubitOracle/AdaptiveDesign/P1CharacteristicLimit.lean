import QubitOracle.AdaptiveDesign.P1CharacteristicBounds
import QubitOracle.AdaptiveDesign.AdaptiveRidgeConsistency

/-! A direct characteristic-function limit for bounded adaptive responses
whose current conditional variance converges. -/
namespace QubitOracle.AdaptiveDesign.P1Weighted
open QubitOracle QubitOracle.Paper Filter MeasureTheory ProbabilityTheory
open AdaptiveResponseStrongLaw AdaptiveRidgeConsistency FiniteCharacteristicTaylor
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
local instance P1CharacteristicLimit_outcomeMeasurable : MeasurableSpace LabeledBinaryOutcome := ⊤
local instance P1CharacteristicLimit_outcomeNonempty : Nonempty LabeledBinaryOutcome := ⟨(0, .plus)⟩

theorem sqrt_normalized_sq (t : ℝ) (n : ℕ) : (t/Real.sqrt (n:ℝ))^2 = t^2/(n:ℝ) := by
  rw [div_pow,Real.sq_sqrt (Nat.cast_nonneg n)]

theorem normalized_remainder_bound (C : ℝ) (hC : 0 ≤ C) (t : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (n:ℝ)*characteristicRemainder (t/Real.sqrt (n:ℝ)) C ≤
      (|t|^3*C^3*Real.exp (|t| * C))/Real.sqrt (n:ℝ) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hsn : 0<Real.sqrt (n:ℝ) := Real.sqrt_pos.2 hn0
  have hs1 : 1≤Real.sqrt (n:ℝ) := by
    simpa using Real.sqrt_le_sqrt (show (1:ℝ)≤n by exact_mod_cast hn)
  have hu : |t/Real.sqrt (n:ℝ)| = |t|/Real.sqrt (n:ℝ) := by rw [abs_div,abs_of_pos hsn]
  have hub : |t/Real.sqrt (n:ℝ)| ≤ |t| := by
    rw [hu]
    exact div_le_self (abs_nonneg t) hs1
  unfold characteristicRemainder
  calc
    _ ≤ (n:ℝ)*(|t/Real.sqrt (n:ℝ)|^3*C^3*Real.exp (|t| * C)) := by gcongr
    _ = _ := by
      rw [hu]
      have hs := Real.sq_sqrt (Nat.cast_nonneg n)
      field_simp
      rw [hs]
      ring

theorem normalized_euler_norm (t v : ℝ) (hv : 0 ≤ v) :
    ∀ᶠ n : ℕ in atTop, ‖(1-((t/Real.sqrt (n:ℝ):ℝ):ℂ)^2*(v:ℂ)/2)‖≤1 := by
  have hu := constant_div_sqrt_nat_tendsto_zero t
  have hh : Tendsto (fun n : ℕ => (t/Real.sqrt (n:ℝ))^2*v/2) atTop (𝓝 0) := by
    simpa using ((hu.pow 2).mul_const v).div_const 2
  filter_upwards [hh.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))] with n hn
  have ha : 0≤(t/Real.sqrt (n:ℝ))^2*v/2 := by positivity
  have he : (1-((t/Real.sqrt (n:ℝ):ℝ):ℂ)^2*(v:ℂ)/2) =
      ((1-(t/Real.sqrt (n:ℝ))^2*v/2:ℝ):ℂ) := by push_cast; rfl
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith)]
  linarith

theorem normalized_euler_tendsto (t v : ℝ) :
    Tendsto (fun n : ℕ => (1-((t/Real.sqrt (n:ℝ):ℝ):ℂ)^2*(v:ℂ)/2)^n)
      atTop (𝓝 (Complex.exp (-(v:ℂ)*(t:ℂ)^2/2))) := by
  have hh := Complex.tendsto_one_add_div_pow_exp (-(v:ℂ)*(t:ℂ)^2/2)
  convert hh using 1
  funext n
  congr 1
  rw [← Complex.ofReal_pow,sqrt_normalized_sq]
  push_cast
  ring

theorem normalized_characteristic_tendsto (p : Policy) (θ : OneQubitPhysicalParameter)
    (g : Action → LabeledBinaryOutcome → ℝ)
    (hm : ∀ a, ∫ z, g a z ∂kernel θ a = 0)
    (C : ℝ) (hC : 0 ≤ C) (hg : ∀ a z, |g a z| ≤ C) (v : ℝ) (hv : 0≤v)
    (hvar : ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (protocol p) θ,
      Tendsto (fun k => responseVariance θ g (actualAction p (k+1) path)) atTop (𝓝 v)) (t : ℝ) :
    Tendsto (fun n : ℕ => characteristicSum p θ g (t/Real.sqrt (n:ℝ)) n) atTop
      (𝓝 (Complex.exp (-(v:ℂ)*(t:ℂ)^2/2))) := by
  let e := varianceError p θ g v
  let K := |t|^3*C^3*Real.exp (|t| * C)
  have he := (varianceError_tendsto p θ g C hC hg v hvar).cesaro_smul
  have hb : Tendsto (fun n : ℕ => t^2/2*((n:ℝ)⁻¹*∑ k ∈ Finset.range n,e k)+K/Real.sqrt (n:ℝ))
      atTop (𝓝 0) := by
    simpa only [smul_eq_mul,mul_zero,zero_add] using
      (he.const_mul (t^2/2)).add (constant_div_sqrt_nat_tendsto_zero K)
  have hd : Tendsto (fun n : ℕ =>
      ‖characteristicSum p θ g (t/Real.sqrt (n:ℝ)) n-
        (1-((t/Real.sqrt (n:ℝ):ℝ):ℂ)^2*(v:ℂ)/2)^n‖) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hb
    filter_upwards [normalized_euler_norm t v hv,eventually_ge_atTop 1] with n hn hn1
    have hh := characteristicSum_bound p θ g hm C hC hg (t/Real.sqrt (n:ℝ)) v hn n
    have hr := normalized_remainder_bound C hC t n hn1
    rw [sqrt_normalized_sq] at hh
    calc
      _ ≤ t^2/(n:ℝ)/2*(∑ k ∈ Finset.range n,e k)+(n:ℝ)*characteristicRemainder (t/Real.sqrt (n:ℝ)) C := hh
      _ ≤ t^2/(n:ℝ)/2*(∑ k ∈ Finset.range n,e k)+K/Real.sqrt (n:ℝ) := by linarith
      _ = _ := by ring
  have hc := tendsto_zero_iff_norm_tendsto_zero.mpr hd
  have hp := normalized_euler_tendsto t v
  have hh := hc.add hp
  simpa only [sub_add_cancel,zero_add] using hh

def normalizedResponse (p : Policy) (g : Action → LabeledBinaryOutcome → ℝ) (n : ℕ) (path : Path) : ℝ :=
  (Real.sqrt (n:ℝ))⁻¹*shiftedSum p g n path

theorem normalizedResponse_measurable (p : Policy) (g : Action → LabeledBinaryOutcome → ℝ) (n : ℕ) :
    Measurable (normalizedResponse p g n) :=
  ((shiftedSum_measurable p g n).mono (Filtration.piLE.le n)).measurable.const_mul _

theorem normalizedResponse_charFun (p : Policy) (θ : OneQubitPhysicalParameter)
    (g : Action → LabeledBinaryOutcome → ℝ) (n : ℕ) (t : ℝ) :
    charFun ((adaptiveInfiniteTrajectoryMeasure (protocol p) θ).map (normalizedResponse p g n)) t =
      characteristicSum p θ g (t/Real.sqrt (n:ℝ)) n := by
  rw [charFun_apply_real,integral_map (normalizedResponse_measurable p g n).aemeasurable (by fun_prop)]
  apply integral_congr_ae
  filter_upwards [] with path
  unfold normalizedResponse FiniteCharacteristicTaylor.phase
  congr 1
  push_cast
  ring

theorem bounded_response_scalar_clt (p : Policy) (θ : OneQubitPhysicalParameter)
    (g : Action → LabeledBinaryOutcome → ℝ)
    (hm : ∀ a, ∫ z, g a z ∂kernel θ a = 0)
    (C : ℝ) (hC : 0 ≤ C) (hg : ∀ a z, |g a z| ≤ C) (v : ℝ) (hv : 0≤v)
    (hvar : ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (protocol p) θ,
      Tendsto (fun k => responseVariance θ g (actualAction p (k+1) path)) atTop (𝓝 v)) :
    TendstoInDistribution (normalizedResponse p g) atTop id
      (fun _ => adaptiveInfiniteTrajectoryMeasure (protocol p) θ) (gaussianReal 0 v.toNNReal) where
  forall_aemeasurable n := (normalizedResponse_measurable p g n).aemeasurable
  aemeasurable_limit := measurable_id.aemeasurable
  tendsto := by
    apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.2
    intro t
    change Tendsto (fun n => charFun ((adaptiveInfiniteTrajectoryMeasure (protocol p) θ).map (normalizedResponse p g n)) t)
      atTop (𝓝 (charFun ((gaussianReal 0 v.toNNReal).map id) t))
    simp only [Measure.map_id,normalizedResponse_charFun,charFun_gaussianReal,Complex.ofReal_zero,
      mul_zero,zero_mul,zero_sub,Real.toNNReal_of_nonneg hv,NNReal.coe_mk]
    convert normalized_characteristic_tendsto p θ g hm C hC hg v hv hvar t using 1 <;> congr 1 <;> ring

end
end QubitOracle.AdaptiveDesign.P1Weighted
