import Mathlib.MeasureTheory.Function.FactorsThrough
import QubitOracle.AdaptiveDesign.AdaptiveResponseStrongLaw
import QubitOracle.AdaptiveDesign.FiniteCharacteristicTaylor
import QubitOracle.Paper.AdaptiveTrajectoryExperiment
/-! Exact conditional characteristic-function recursion for any finite-outcome
adaptive experiment. Generalized from the direct P1 proof. No limit theorem is assumed. -/
namespace QubitOracle.AdaptiveDesign.FiniteAdaptiveCharacteristic
open QubitOracle QubitOracle.Paper Filter MeasureTheory ProbabilityTheory
open AdaptiveResponseStrongLaw FiniteCharacteristicTaylor
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

variable {Theta Action Outcome : Type}
  [MeasurableSpace Action] [MeasurableSpace Outcome]
  [Fintype Outcome] [MeasurableSingletonClass Outcome]
  [StandardBorelSpace Outcome] [Nonempty Outcome]

local instance responseMarkov (p : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta) :
    IsMarkovKernel (p.response theta) := p.response_isMarkov theta


def actualAction (p : PredictableAdaptiveProtocol Theta Action Outcome) (n : ℕ)
    (path : AdaptiveInfinitePath Outcome) : Action :=
  p.design n (adaptiveInfinitePathPrefix n path)

def probability (p : PredictableAdaptiveProtocol Theta Action Outcome) (θ : Theta)
    (a : Action) (z : Outcome) : ℝ := (p.response θ a).real {z}

lemma probability_nonneg (p : PredictableAdaptiveProtocol Theta Action Outcome) (θ : Theta)
    (a : Action) (z : Outcome) : 0 ≤ probability p θ a z := measureReal_nonneg

lemma probability_sum (p : PredictableAdaptiveProtocol Theta Action Outcome) (θ : Theta)
    (a : Action) : ∑ z, probability p θ a z = 1 := by
  simp [probability, ← Finset.sum_const_zero]

lemma integral_eq_sum (p : PredictableAdaptiveProtocol Theta Action Outcome) (θ : Theta)
    (a : Action) (f : Outcome → ℝ) :
    ∫ z, f z ∂p.response θ a = ∑ z, probability p θ a z * f z := by
  simpa only [probability, smul_eq_mul] using
    (integral_fintype (μ := p.response θ a) (f := f) Integrable.of_finite)

theorem integral_complex_eq_sum (p : PredictableAdaptiveProtocol Theta Action Outcome) (θ : Theta)
    (a : Action) (f : Outcome → ℂ) :
    ∫ z, f z ∂p.response θ a = ∑ z, (probability p θ a z:ℂ)*f z := by
  simpa only [probability, Complex.real_smul] using
    (integral_fintype (μ := p.response θ a) (f := f) Integrable.of_finite)

theorem weighted_step_integral (p : PredictableAdaptiveProtocol Theta Action Outcome) (θ : Theta) (n : ℕ)
    (w : Prefix (Outcome := Outcome) n → ℂ) (hw : ∀ x, ‖w x‖ ≤ 1)
    (g : Action → Outcome → ℂ) (hg : ∀ a z, ‖g a z‖ ≤ 1) :
    ∫ path, w (Preorder.frestrictLe n path)*g (actualAction p (n+1) path) (path (n+1))
      ∂adaptiveInfiniteTrajectoryMeasure p θ =
    ∫ path, w (Preorder.frestrictLe n path) *
      (∑ z, (probability p θ (actualAction p (n+1) path) z:ℂ)*g (actualAction p (n+1) path) z)
      ∂adaptiveInfiniteTrajectoryMeasure p θ := by
  let μ := adaptiveInfiniteTrajectoryMeasure p θ
  let X : (AdaptiveInfinitePath Outcome) → Prefix (Outcome := Outcome) n := Preorder.frestrictLe n
  let Y := fun path : (AdaptiveInfinitePath Outcome) => path (n+1)
  let f := fun z : Prefix (Outcome := Outcome) n × Outcome =>
    w z.1*g (p.design (n+1) (iicToAdaptiveTrajectory z.1)) z.2
  have hX : Measurable X := Preorder.measurable_frestrictLe n
  have hY : Measurable Y := measurable_pi_apply (n+1)
  have hf : StronglyMeasurable f := (measurable_of_countable f).stronglyMeasurable
  have hfi : Integrable (fun path => f (X path,Y path)) μ := by
    apply Integrable.of_bound (hf.comp_measurable (hX.prodMk hY)).aestronglyMeasurable 1
    filter_upwards [] with path
    dsimp [f]
    rw [norm_mul]
    exact (mul_le_mul (hw _) (hg _ _) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hc := condExp_prod_ae_eq_integral_condDistrib hX hY.aemeasurable hf hfi
  have hprefix : condDistrib Y X μ =ᵐ[μ.map X] adaptiveIonescuStepKernel p θ n :=
    adaptiveInfiniteTrajectory_conditionalStep p θ n
  have hp := (ae_map_iff hX.aemeasurable
    (Set.Finite.measurableSet (Set.toFinite {pref | condDistrib Y X μ pref =
      adaptiveIonescuStepKernel p θ n pref}))).mp hprefix
  have heq : μ[(fun path => f (X path,Y path)) | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
      (fun path => w (X path) * (∑ z, (probability p θ (actualAction p (n+1) path) z:ℂ)*
        g (actualAction p (n+1) path) z)) := by
    apply hc.trans
    filter_upwards [hp] with path hh
    rw [hh]
    change (∫ z, w (X path)*g (actualAction p (n+1) path) z ∂p.response θ (actualAction p (n+1) path)) = _
    rw [integral_const_mul,integral_complex_eq_sum]
  have hi := integral_congr_ae heq
  rw [integral_condExp hX.comap_le] at hi
  exact hi

def shiftedSum (p : PredictableAdaptiveProtocol Theta Action Outcome) (g : Action → Outcome → ℝ) (n : ℕ) (path : (AdaptiveInfinitePath Outcome)) : ℝ :=
  ∑ k ∈ Finset.range n, actualResponse p g (k+1) path

theorem shiftedSum_measurable (p : PredictableAdaptiveProtocol Theta Action Outcome) (g : Action → Outcome → ℝ) (n : ℕ) :
    StronglyMeasurable[Filtration.piLE n] (shiftedSum p g n) := by
  have he : shiftedSum p g n = ∑ k ∈ Finset.range n, actualResponse p g (k+1) := by
    funext path
    simp [shiftedSum]
  rw [he]
  exact Finset.stronglyMeasurable_sum (Finset.range n) (fun k hk =>
    (actualResponse_stronglyMeasurable_piLE p g (k+1)).mono
      (Filtration.piLE.mono (Nat.succ_le_iff.mpr (Finset.mem_range.mp hk))))

theorem shiftedSum_succ (p : PredictableAdaptiveProtocol Theta Action Outcome) (g : Action → Outcome → ℝ) (n : ℕ) (path : (AdaptiveInfinitePath Outcome)) :
    shiftedSum p g (n+1) path = shiftedSum p g n path + actualResponse p g (n+1) path := by
  simp [shiftedSum,Finset.sum_range_succ]

def characteristicSum (p : PredictableAdaptiveProtocol Theta Action Outcome) (θ : Theta)
    (g : Action → Outcome → ℝ) (u : ℝ) (n : ℕ) : ℂ :=
  ∫ path, FiniteCharacteristicTaylor.phase (u*shiftedSum p g n path) ∂adaptiveInfiniteTrajectoryMeasure p θ

theorem characteristicSum_zero (p : PredictableAdaptiveProtocol Theta Action Outcome) (θ : Theta)
    (g : Action → Outcome → ℝ) (u : ℝ) : characteristicSum p θ g u 0 = 1 := by
  simp [characteristicSum,shiftedSum,phase_zero]

def kernelCharacteristic (p : PredictableAdaptiveProtocol Theta Action Outcome) (θ : Theta) (g : Action → Outcome → ℝ)
    (u : ℝ) (a : Action) : ℂ :=
  ∑ z, (probability p θ a z:ℂ)*FiniteCharacteristicTaylor.phase (u*g a z)

theorem characteristicSum_succ (p : PredictableAdaptiveProtocol Theta Action Outcome) (θ : Theta)
    (g : Action → Outcome → ℝ) (u : ℝ) (n : ℕ) :
    characteristicSum p θ g u (n+1) =
      ∫ path, FiniteCharacteristicTaylor.phase (u*shiftedSum p g n path)*
        kernelCharacteristic p θ g u (actualAction p (n+1) path)
        ∂adaptiveInfiniteTrajectoryMeasure p θ := by
  have hS := shiftedSum_measurable p g n
  rw [Filtration.piLE_eq_comap_frestrictLe] at hS
  obtain ⟨h,hm,he⟩ := hS.exists_eq_measurable_comp
  have hh := weighted_step_integral p θ n (fun pref => FiniteCharacteristicTaylor.phase (u*h pref))
    (fun pref => (phase_norm _).le)
    (fun a z => FiniteCharacteristicTaylor.phase (u*g a z)) (fun a z => (phase_norm _).le)
  change characteristicSum p θ g u (n+1) = _
  unfold characteristicSum
  simp_rw [shiftedSum_succ,mul_add,phase_add]
  simpa only [he,Function.comp_apply,actualResponse,actualAction,kernelCharacteristic] using hh

theorem actualAction_statistic_measurable {E : Type*} [MeasurableSpace E]
    (p : PredictableAdaptiveProtocol Theta Action Outcome) (n : ℕ) (f : Action → E) : Measurable (fun path => f (actualAction p n path)) :=
  (measurable_of_countable (fun history => f (p.design n history))).comp (measurable_adaptiveInfinitePathPrefix n)

theorem phaseSum_integrable (p : PredictableAdaptiveProtocol Theta Action Outcome) (θ : Theta)
    (g : Action → Outcome → ℝ) (u : ℝ) (n : ℕ) :
    Integrable (fun path => FiniteCharacteristicTaylor.phase (u*shiftedSum p g n path))
      (adaptiveInfiniteTrajectoryMeasure p θ) := by
  apply Integrable.of_bound _ 1 (ae_of_all _ (fun path => (phase_norm _).le))
  have hs := (shiftedSum_measurable p g n).mono (Filtration.piLE.le n)
  have hc : Continuous (fun x : ℝ => FiniteCharacteristicTaylor.phase (u*x)) := by
    unfold FiniteCharacteristicTaylor.phase
    fun_prop
  exact (hc.comp_stronglyMeasurable hs).aestronglyMeasurable

theorem kernelCharacteristic_bound (p : PredictableAdaptiveProtocol Theta Action Outcome) (θ : Theta) (g : Action → Outcome → ℝ)
    (u : ℝ) (a : Action) : ‖kernelCharacteristic p θ g u a‖ ≤ 1 := by
  unfold kernelCharacteristic
  calc
    _ ≤ ∑ z, ‖(probability p θ a z:ℂ)*FiniteCharacteristicTaylor.phase (u*g a z)‖ := norm_sum_le _ _
    _ = 1 := by
      simp_rw [norm_mul,phase_norm,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (probability_nonneg p θ a _)]
      exact probability_sum p θ a

end
end QubitOracle.AdaptiveDesign.FiniteAdaptiveCharacteristic
