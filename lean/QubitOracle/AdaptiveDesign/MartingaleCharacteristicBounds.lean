import QubitOracle.AdaptiveDesign.FiniteAdaptiveCharacteristicLimit
import QubitOracle.AdaptiveDesign.BoundedVarianceMGF

/-! Characteristic-function estimates for general bounded martingale
differences. The underlying probability space and filtration are arbitrary. -/
namespace QubitOracle.AdaptiveDesign.MartingaleCharacteristic
open Filter MeasureTheory ProbabilityTheory FiniteCharacteristicTaylor
open BoundedMartingaleSecondMoment
open scoped BigOperators Topology ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
local notation "phase" => FiniteCharacteristicTaylor.phase
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem phase_integrable (X : Ω → ℝ) (hX : AEStronglyMeasurable X μ) (u : ℝ) :
    Integrable (fun ω => phase (u*X ω)) μ := by
  apply Integrable.of_bound _ 1 (Eventually.of_forall (fun ω => (phase_norm _).le))
  exact (show Continuous (fun x : ℝ => phase (u*x)) by unfold FiniteCharacteristicTaylor.phase; fun_prop).comp_aestronglyMeasurable hX

theorem conditional_taylor {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (X : Ω → ℝ) (hmX : StronglyMeasurable[mΩ] X) (hc : μ[X | m] =ᵐ[μ] 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ ω, ‖X ω‖ ≤ C) (u : ℝ) :
    ∀ᵐ ω ∂μ,
      ‖μ[fun ω => phase (u*X ω) | m] ω-
        (1-(u:ℂ)^2*(μ[fun ω => X ω^2 | m] ω:ℂ)/2)‖ ≤
          FiniteAdaptiveCharacteristic.characteristicRemainder u C := by
  letI : MeasurableSpace Ω := mΩ
  let a : ℂ := (u:ℂ)*Complex.I
  let b : ℂ := (u:ℂ)^2/2
  let Y : Ω → ℂ := fun ω => (X ω:ℂ)
  let Z : Ω → ℂ := fun ω => Complex.ofReal (X ω^2)
  let P : Ω → ℂ := fun ω => 1+a*Y ω-b*Z ω
  have hiX : Integrable X μ := Integrable.of_bound hmX.aestronglyMeasurable C (Eventually.of_forall hb)
  have hiXsq : Integrable (fun ω => X ω^2) μ := by
    apply Integrable.of_bound (hmX.pow 2).aestronglyMeasurable (C^2)
    exact Eventually.of_forall (fun ω => by change ‖X ω^2‖ ≤ _; rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hb ω) 2)
  have hiY : Integrable Y μ := Complex.ofRealCLM.integrable_comp hiX
  have hiZ : Integrable Z μ := Complex.ofRealCLM.integrable_comp hiXsq
  have hiP : Integrable P μ := ((integrable_const (1:ℂ)).add (hiY.const_mul a)).sub (hiZ.const_mul b)
  have heY := Complex.ofRealCLM.comp_condExp_comm (m:=m) hiX
  have heZ := Complex.ofRealCLM.comp_condExp_comm (m:=m) hiXsq
  have hpoly : μ[P | m] =ᵐ[μ]
      (fun ω => 1-(u:ℂ)^2*(μ[fun ω => X ω^2 | m] ω:ℂ)/2) := by
    have ha := condExp_smul (μ:=μ) a Y m
    have hb' := condExp_smul (μ:=μ) b Z m
    have had := condExp_add (integrable_const (1:ℂ)) (hiY.const_mul a) m
    have hsu := condExp_sub ((integrable_const (1:ℂ)).add (hiY.const_mul a)) (hiZ.const_mul b) m
    filter_upwards [heY,heZ,hc,ha,hb',had,hsu] with ω hy hz hcω haω hbω hadω hsuω
    change μ[(fun ω => (1:ℂ))+a•Y | m] ω = μ[fun ω => (1:ℂ) | m] ω+μ[a•Y | m] ω at hadω
    change μ[P | m] ω = μ[(fun ω => (1:ℂ))+a•Y | m] ω-μ[b•Z | m] ω at hsuω
    rw [hsuω, hadω, haω, hbω, condExp_const hm]
    change 1+a*μ[Y | m] ω-b*μ[Z | m] ω = _
    have hy' : (μ[X | m] ω:ℂ) = μ[Y | m] ω := hy
    have hz' : (μ[fun ω => X ω^2 | m] ω:ℂ) = μ[Z | m] ω := hz
    rw [← hy',← hz',hcω]
    dsimp [a,b]
    push_cast
    ring
  let R := fun ω => phase (u*X ω)-P ω
  have hR (ω : Ω) : ‖R ω‖ ≤ FiniteAdaptiveCharacteristic.characteristicRemainder u C := by
    have he : R ω = phase (u*X ω)-(1+(u*X ω:ℝ)*Complex.I-(u*X ω:ℝ)^2/2) := by
      dsimp [R,P,a,b,Y,Z]
      push_cast
      ring
    rw [he]
    apply (phase_taylor (u*X ω)).trans
    have hu : |u*X ω| ≤ |u| * C := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hb ω) (abs_nonneg u)
    unfold FiniteAdaptiveCharacteristic.characteristicRemainder
    calc
      _ ≤ (|u| * C)^3*Real.exp (|u| * C) := by gcongr
      _ = _ := by ring
  have he := condExp_sub (phase_integrable X hmX.aestronglyMeasurable u) hiP m
  have hbound := ae_bdd_norm_condExp_of_ae_bdd_norm (m:=m) (μ:=μ) (Eventually.of_forall hR)
  filter_upwards [hpoly,he,hbound] with ω hp heω hbω
  change ‖μ[R | m] ω‖ ≤ _ at hbω
  change μ[R | m] ω = μ[fun ω => phase (u*X ω) | m] ω-μ[P | m] ω at heω
  rwa [heω,hp] at hbω

def variance (F : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (k : ℕ) : Ω → ℝ :=
  μ[fun ω => X k ω^2 | F k]

def varianceError (F : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (v : ℝ) (k : ℕ) : ℝ :=
  ∫ ω, |variance (μ:=μ) F X k ω-v| ∂μ

theorem variance_norm_bound (F : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (C : ℝ) (hb : ∀ n ω, ‖X n ω‖ ≤ C) (k : ℕ) :
    ∀ᵐ ω ∂μ, ‖variance (μ:=μ) F X k ω‖ ≤ C^2 := by
  apply ae_bdd_norm_condExp_of_ae_bdd_norm
  exact Eventually.of_forall (fun ω => by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hb k ω) 2)

theorem varianceError_integrable (F : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (v : ℝ) (k : ℕ) :
    Integrable (fun ω => |variance (μ:=μ) F X k ω-v|) μ :=
  (integrable_condExp.sub (integrable_const v)).abs

theorem varianceError_tendsto (F : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (C : ℝ) (hb : ∀ n ω, ‖X n ω‖ ≤ C) (v : ℝ)
    (hv : ∀ᵐ ω ∂μ, Tendsto (fun k => variance (μ:=μ) F X k ω) atTop (𝓝 v)) :
    Tendsto (varianceError (μ:=μ) F X v) atTop (𝓝 0) := by
  have hh := tendsto_integral_of_dominated_convergence (μ:=μ)
    (F:=fun k ω => |variance (μ:=μ) F X k ω-v|) (f:=fun _ => (0:ℝ)) (fun _ => C^2+|v|)
    (fun k => (varianceError_integrable (μ:=μ) F X v k).aestronglyMeasurable) (integrable_const _)
    (fun k => ?_) ?_
  · change Tendsto (fun k => ∫ ω, |variance (μ:=μ) F X k ω-v| ∂μ) atTop (𝓝 0)
    simpa only [integral_zero] using hh
  · filter_upwards [variance_norm_bound (μ:=μ) F X C hb k] with ω hω
    simp only [Real.norm_eq_abs,abs_abs] at *
    exact (abs_sub _ _).trans (add_le_add hω le_rfl)
  · filter_upwards [hv] with ω hω
    simpa using (hω.sub_const v).abs

def characteristicSum (X : ℕ → Ω → ℝ) (u : ℝ) (n : ℕ) : ℂ :=
  ∫ ω, phase (u*partialSum X n ω) ∂μ

theorem characteristicSum_zero (X : ℕ → Ω → ℝ) (u : ℝ) :
    characteristicSum (μ:=μ) X u 0 = 1 := by simp [characteristicSum,partialSum,phase_zero]

theorem phaseSum_integrable (F : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n)) (u : ℝ) (n : ℕ) :
    Integrable (fun ω => phase (u*partialSum X n ω)) μ :=
  phase_integrable _ ((partialSum_adapted F X ha n).mono (F.le n)).aestronglyMeasurable u

theorem characteristicSum_succ (F : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n)) (u : ℝ) (n : ℕ) :
    characteristicSum (μ:=μ) X u (n+1) =
      ∫ ω, phase (u*partialSum X n ω)*μ[fun ω => phase (u*X n ω) | F n] ω ∂μ := by
  let W := fun ω => phase (u*partialSum X n ω)
  let Y := fun ω => phase (u*X n ω)
  have hW : StronglyMeasurable[F n] W :=
    (show Continuous (fun x : ℝ => phase (u*x)) by unfold FiniteCharacteristicTaylor.phase; fun_prop).comp_stronglyMeasurable
      (partialSum_adapted F X ha n)
  have hiY : Integrable Y μ := phase_integrable _ ((ha n).mono (F.le (n+1))).aestronglyMeasurable u
  have hi : Integrable (W*Y) μ := hiY.bdd_mul (hW.mono (F.le n)).aestronglyMeasurable
    (Eventually.of_forall (fun ω => (phase_norm _).le))
  have he := condExp_bilin_of_aestronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ)
    hW.aestronglyMeasurable hi hiY
  calc
    _ = ∫ ω, W ω*Y ω ∂μ := by
      unfold characteristicSum
      simp only [partialSum_succ,Pi.add_apply,mul_add,phase_add,W,Y]
    _ = ∫ ω, μ[W*Y | F n] ω ∂μ := (integral_condExp (F.le n)).symm
    _ = _ := integral_congr_ae he

theorem conditional_comparison (F : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hc : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n ω, ‖X n ω‖ ≤ C) (u v : ℝ) (k : ℕ) :
    ∀ᵐ ω ∂μ, ‖μ[fun ω => phase (u*X k ω) | F k] ω-(1-(u:ℂ)^2*(v:ℂ)/2)‖ ≤
      u^2/2*|variance (μ:=μ) F X k ω-v|+FiniteAdaptiveCharacteristic.characteristicRemainder u C := by
  filter_upwards [conditional_taylor (F.le k) (X k) ((ha k).mono (F.le (k+1))) (hc k) C hC (hb k) u]
    with ω hω
  let c := μ[fun ω => phase (u*X k ω) | F k] ω
  let V := variance (μ:=μ) F X k ω
  have he : c-(1-(u:ℂ)^2*(v:ℂ)/2) =
      (c-(1-(u:ℂ)^2*(V:ℂ)/2))+((u:ℂ)^2/2*((v:ℂ)-(V:ℂ))) := by ring
  change ‖c-(1-(u:ℂ)^2*(v:ℂ)/2)‖ ≤ _
  rw [he]
  have hn : ‖(u:ℂ)^2/2*((v:ℂ)-(V:ℂ))‖ = u^2/2*|V-v| := by
    rw [norm_mul,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    norm_num only [Complex.norm_ofNat]
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm]
  have hh := norm_add_le (c-(1-(u:ℂ)^2*(V:ℂ)/2)) ((u:ℂ)^2/2*((v:ℂ)-(V:ℂ)))
  rw [hn] at hh
  exact hh.trans (by dsimp [c,V,variance] at *; linarith)

theorem characteristicSum_step_bound (F : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hc : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n ω, ‖X n ω‖ ≤ C) (u v : ℝ) (k : ℕ) :
    ‖characteristicSum (μ:=μ) X u (k+1)-(1-(u:ℂ)^2*(v:ℂ)/2)*characteristicSum (μ:=μ) X u k‖ ≤
      u^2/2*varianceError (μ:=μ) F X v k+FiniteAdaptiveCharacteristic.characteristicRemainder u C := by
  let f := fun ω => phase (u*partialSum X k ω)
  let c := μ[fun ω => phase (u*X k ω) | F k]
  let α : ℂ := 1-(u:ℂ)^2*(v:ℂ)/2
  have hfm : AEStronglyMeasurable f μ := (phaseSum_integrable (μ:=μ) F X ha u k).aestronglyMeasurable
  have hfc : Integrable (fun ω => f ω*c ω) μ := integrable_condExp.bdd_mul hfm
    (Eventually.of_forall (fun ω => (phase_norm _).le))
  have hfa : Integrable (fun ω => α*f ω) μ := (phaseSum_integrable (μ:=μ) F X ha u k).const_mul α
  have he : characteristicSum (μ:=μ) X u (k+1)-α*characteristicSum (μ:=μ) X u k =
      ∫ ω, f ω*(c ω-α) ∂μ := by
    rw [characteristicSum_succ F X ha,characteristicSum,← integral_const_mul,← integral_sub hfc hfa]
    apply integral_congr_ae
    exact Eventually.of_forall (fun ω => by dsimp [f,c]; ring)
  rw [he]
  have hib := (varianceError_integrable (μ:=μ) F X v k).const_mul (u^2/2) |>.add
    (integrable_const (FiniteAdaptiveCharacteristic.characteristicRemainder u C))
  have he' : (fun ω => f ω*(c ω-α)) = (fun ω => f ω*c ω-α*f ω) := by funext ω; ring
  have hdi : Integrable (fun ω => f ω*(c ω-α)) μ := by rw [he']; exact hfc.sub hfa
  calc
    _ ≤ ∫ ω, ‖f ω*(c ω-α)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, u^2/2*|variance (μ:=μ) F X k ω-v|+FiniteAdaptiveCharacteristic.characteristicRemainder u C ∂μ := by
      apply integral_mono_ae hdi.norm hib
      filter_upwards [conditional_comparison F X ha hc C hC hb u v k] with ω hω
      change ‖f ω*(c ω-α)‖ ≤ _
      rw [norm_mul,show ‖f ω‖=1 from phase_norm _,one_mul]
      exact hω
    _ = _ := by
      rw [integral_add ((varianceError_integrable (μ:=μ) F X v k).const_mul _) (integrable_const _),
        integral_const_mul,integral_const]
      simp [varianceError]

theorem characteristicSum_bound (F : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ)
    (ha : ∀ n, StronglyMeasurable[F (n+1)] (X n))
    (hc : ∀ n, μ[X n | F n] =ᵐ[μ] 0)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n ω, ‖X n ω‖ ≤ C) (u v : ℝ)
    (hα : ‖(1-(u:ℂ)^2*(v:ℂ)/2)‖ ≤ 1) (n : ℕ) :
    ‖characteristicSum (μ:=μ) X u n-(1-(u:ℂ)^2*(v:ℂ)/2)^n‖ ≤
      u^2/2*(∑ k ∈ Finset.range n,varianceError (μ:=μ) F X v k)+
        (n:ℝ)*FiniteAdaptiveCharacteristic.characteristicRemainder u C := by
  have hh := FiniteAdaptiveCharacteristic.characteristic_telescope (characteristicSum (μ:=μ) X u) _ _
    (characteristicSum_zero X u) hα (characteristicSum_step_bound F X ha hc C hC hb u v) n
  simpa only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_range,nsmul_eq_mul] using hh

end
end QubitOracle.AdaptiveDesign.MartingaleCharacteristic
