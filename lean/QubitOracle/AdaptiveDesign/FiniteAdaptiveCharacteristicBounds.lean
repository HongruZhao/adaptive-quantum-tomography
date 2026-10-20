import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Normed
import QubitOracle.AdaptiveDesign.FiniteAdaptiveCharacteristicProcess
import QubitOracle.AdaptiveDesign.FiniteCharacteristicTaylor
import QubitOracle.Paper.AdaptiveTrajectoryExperiment
/-! Quantitative characteristic-function comparison for bounded adaptive
responses. All bounds are proved for the actual finite Born experiment. -/
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

local instance FiniteAdaptiveCharacteristicBounds_responseMarkov (p : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta) :
    IsMarkovKernel (p.response theta) := p.response_isMarkov theta


def responseVariance (p : PredictableAdaptiveProtocol Theta Action Outcome) (θ : Theta)
    (g : Action → Outcome → ℝ) (a : Action) : ℝ :=
  ∑ z, probability p θ a z * g a z ^ 2

lemma responseVariance_eq_integral (p : PredictableAdaptiveProtocol Theta Action Outcome) (θ : Theta)
    (g : Action → Outcome → ℝ) (a : Action) :
    responseVariance p θ g a = ∫ z, g a z ^ 2 ∂p.response θ a := by
  rw [integral_eq_sum]
  rfl

theorem responseVariance_nonneg (p : PredictableAdaptiveProtocol Theta Action Outcome) (θ : Theta)
    (g : Action → Outcome → ℝ) (a : Action) : 0 ≤ responseVariance p θ g a :=
  Finset.sum_nonneg (fun z _ => mul_nonneg (probability_nonneg p θ a z) (sq_nonneg _))

theorem responseVariance_bound (p : PredictableAdaptiveProtocol Theta Action Outcome) (θ : Theta)
    (g : Action → Outcome → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ a z, |g a z| ≤ C) (a : Action) : responseVariance p θ g a ≤ C^2 := by
  calc
    _ ≤ ∑ z, probability p θ a z*C^2 := by
      apply Finset.sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_left _ (probability_nonneg p θ a z)
      exact (sq_abs (g a z)) ▸ (pow_le_pow_left₀ (abs_nonneg _) (hg a z) 2)
    _ = C^2 := by rw [← Finset.sum_mul,probability_sum,one_mul]

def characteristicRemainder (u C : ℝ) : ℝ := |u|^3*C^3*Real.exp (|u| * C)

theorem kernelCharacteristic_taylor (p : PredictableAdaptiveProtocol Theta Action Outcome) (θ : Theta)
    (g : Action → Outcome → ℝ)
    (hm : ∀ a, ∫ z, g a z ∂p.response θ a = 0)
    (C : ℝ) (hC : 0 ≤ C) (hg : ∀ a z, |g a z| ≤ C) (u : ℝ) (a : Action) :
    ‖kernelCharacteristic p θ g u a - (1-(u:ℂ)^2*(responseVariance p θ g a:ℂ)/2)‖ ≤
      characteristicRemainder u C := by
  have hh := finite_centered_taylor (probability p θ a) (g a)
    (probability_nonneg p θ a) (probability_sum p θ a)
    (by simpa only [integral_eq_sum] using hm a) C hC (hg a) u
  simpa only [kernelCharacteristic,responseVariance,Complex.ofReal_sum,Complex.ofReal_mul,
    Complex.ofReal_pow,characteristicRemainder] using hh

theorem kernelCharacteristic_comparison (p : PredictableAdaptiveProtocol Theta Action Outcome) (θ : Theta)
    (g : Action → Outcome → ℝ)
    (hm : ∀ a, ∫ z, g a z ∂p.response θ a = 0)
    (C : ℝ) (hC : 0 ≤ C) (hg : ∀ a z, |g a z| ≤ C) (u v : ℝ) (a : Action) :
    ‖kernelCharacteristic p θ g u a - (1-(u:ℂ)^2*(v:ℂ)/2)‖ ≤
      u^2/2*|responseVariance p θ g a-v| + characteristicRemainder u C := by
  have he : kernelCharacteristic p θ g u a-(1-(u:ℂ)^2*(v:ℂ)/2) =
      (kernelCharacteristic p θ g u a-(1-(u:ℂ)^2*(responseVariance p θ g a:ℂ)/2)) +
        ((u:ℂ)^2/2*((v:ℂ)-(responseVariance p θ g a:ℂ))) := by ring
  rw [he]
  refine (norm_add_le _ _).trans ?_
  have hn : ‖(u:ℂ)^2/2*((v:ℂ)-(responseVariance p θ g a:ℂ))‖ =
      u^2/2*|responseVariance p θ g a-v| := by
    rw [norm_mul,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    norm_num only [Complex.norm_ofNat]
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm]
  rw [hn]
  linarith [kernelCharacteristic_taylor p θ g hm C hC hg u a]

def varianceError (p : PredictableAdaptiveProtocol Theta Action Outcome) (θ : Theta)
    (g : Action → Outcome → ℝ) (v : ℝ) (k : ℕ) : ℝ :=
  ∫ path, |responseVariance p θ g (actualAction p (k+1) path)-v|
    ∂adaptiveInfiniteTrajectoryMeasure p θ

theorem varianceError_integrable (p : PredictableAdaptiveProtocol Theta Action Outcome) (θ : Theta)
    (g : Action → Outcome → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ a z, |g a z| ≤ C) (v : ℝ) (k : ℕ) :
    Integrable (fun path => |responseVariance p θ g (actualAction p (k+1) path)-v|)
      (adaptiveInfiniteTrajectoryMeasure p θ) := by
  apply Integrable.of_bound
    ((actualAction_statistic_measurable p (k+1) (fun a => |responseVariance p θ g a-v|)).stronglyMeasurable.aestronglyMeasurable)
    (C^2+|v|)
  filter_upwards [] with path
  rw [Real.norm_eq_abs,abs_abs]
  exact (abs_sub _ _).trans (by
    rw [abs_of_nonneg (responseVariance_nonneg p θ g _)]
    linarith [responseVariance_bound p θ g C hC hg (actualAction p (k+1) path)])

theorem varianceError_tendsto (p : PredictableAdaptiveProtocol Theta Action Outcome) (θ : Theta)
    (g : Action → Outcome → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ a z, |g a z| ≤ C) (v : ℝ)
    (hv : ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure p θ,
      Tendsto (fun k => responseVariance p θ g (actualAction p (k+1) path)) atTop (𝓝 v)) :
    Tendsto (varianceError p θ g v) atTop (𝓝 0) := by
  have hh := tendsto_integral_of_dominated_convergence (μ := adaptiveInfiniteTrajectoryMeasure p θ)
    (F := fun k path => |responseVariance p θ g (actualAction p (k+1) path)-v|)
    (f := fun _ => (0:ℝ)) (fun _ => C^2+|v|)
    (fun k => (varianceError_integrable p θ g C hC hg v k).aestronglyMeasurable)
    (integrable_const _) (fun k => ?_) ?_
  · change Tendsto (fun k => ∫ path, |responseVariance p θ g (actualAction p (k+1) path)-v|
      ∂adaptiveInfiniteTrajectoryMeasure p θ) atTop (𝓝 0)
    simpa only [integral_zero] using hh
  · filter_upwards [] with path
    rw [Real.norm_eq_abs,abs_abs]
    exact (abs_sub _ _).trans (by
      rw [abs_of_nonneg (responseVariance_nonneg p θ g _)]
      linarith [responseVariance_bound p θ g C hC hg (actualAction p (k+1) path)])
  · filter_upwards [hv] with path hp
    simpa using (hp.sub (tendsto_const_nhds (x := v))).abs

theorem characteristicSum_step_bound (p : PredictableAdaptiveProtocol Theta Action Outcome) (θ : Theta)
    (g : Action → Outcome → ℝ)
    (hm : ∀ a, ∫ z, g a z ∂p.response θ a = 0)
    (C : ℝ) (hC : 0 ≤ C) (hg : ∀ a z, |g a z| ≤ C) (u v : ℝ) (k : ℕ) :
    ‖characteristicSum p θ g u (k+1) - (1-(u:ℂ)^2*(v:ℂ)/2)*characteristicSum p θ g u k‖ ≤
      u^2/2*varianceError p θ g v k + characteristicRemainder u C := by
  let μ := adaptiveInfiniteTrajectoryMeasure p θ
  let f := fun path => FiniteCharacteristicTaylor.phase (u*shiftedSum p g k path)
  let c := fun path => kernelCharacteristic p θ g u (actualAction p (k+1) path)
  let α : ℂ := 1-(u:ℂ)^2*(v:ℂ)/2
  have hfm : AEStronglyMeasurable f μ := (phaseSum_integrable p θ g u k).aestronglyMeasurable
  have hcm : AEStronglyMeasurable c μ :=
    (actualAction_statistic_measurable p (k+1) (kernelCharacteristic p θ g u)).stronglyMeasurable.aestronglyMeasurable
  have hfc : Integrable (fun path => f path*c path) μ := by
    apply Integrable.of_bound (hfm.mul hcm) 1
    filter_upwards [] with path
    change ‖f path*c path‖ ≤ 1
    rw [norm_mul,show ‖f path‖=1 from phase_norm _,one_mul]
    exact kernelCharacteristic_bound p θ g u _
  have hfa : Integrable (fun path => α*f path) μ := (phaseSum_integrable p θ g u k).const_mul α
  have he : characteristicSum p θ g u (k+1)-α*characteristicSum p θ g u k =
      ∫ path, f path*(c path-α) ∂μ := by
    rw [characteristicSum_succ,characteristicSum,← integral_const_mul,← integral_sub hfc hfa]
    apply integral_congr_ae
    filter_upwards [] with path
    dsimp [f,c]
    ring
  rw [he]
  have hib := (varianceError_integrable p θ g C hC hg v k).const_mul (u^2/2) |>.add
    (integrable_const (characteristicRemainder u C))
  calc
    _ ≤ ∫ path, ‖f path*(c path-α)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ path, u^2/2*|responseVariance p θ g (actualAction p (k+1) path)-v|+
        characteristicRemainder u C ∂μ := by
      have he' : (fun path => f path*(c path-α)) = (fun path => f path*c path-α*f path) := by
        funext path; ring
      have hdi : Integrable (fun path => f path*(c path-α)) μ := by
        rw [he']; exact hfc.sub hfa
      apply integral_mono_ae hdi.norm hib
      filter_upwards [] with path
      change ‖f path*(c path-α)‖ ≤ u^2/2*|responseVariance p θ g (actualAction p (k+1) path)-v|+
        characteristicRemainder u C
      rw [norm_mul,show ‖f path‖=1 from phase_norm _,one_mul]
      exact kernelCharacteristic_comparison p θ g hm C hC hg u v _
    _ = _ := by
      rw [integral_add ((varianceError_integrable p θ g C hC hg v k).const_mul _) (integrable_const _),
        integral_const_mul,integral_const]
      simp [varianceError,μ]

theorem characteristic_telescope (f : ℕ → ℂ) (α : ℂ) (e : ℕ → ℝ)
    (h0 : f 0=1) (hα : ‖α‖≤1) (he : ∀ k, ‖f (k+1)-α*f k‖≤e k) (n : ℕ) :
    ‖f n-α^n‖ ≤ ∑ k ∈ Finset.range n, e k := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    have hx : f (n+1)-α^(n+1) = (f (n+1)-α*f n)+α*(f n-α^n) := by rw [pow_succ]; ring
    rw [hx,Finset.sum_range_succ]
    have hh := norm_add_le (f (n+1)-α*f n) (α*(f n-α^n))
    rw [norm_mul] at hh
    have hb : ‖α‖*‖f n-α^n‖ ≤ ∑ k ∈ Finset.range n, e k :=
      (mul_le_mul_of_nonneg_right hα (norm_nonneg _)).trans (by simpa using ih)
    linarith [he n]

theorem characteristicSum_bound (p : PredictableAdaptiveProtocol Theta Action Outcome) (θ : Theta)
    (g : Action → Outcome → ℝ)
    (hm : ∀ a, ∫ z, g a z ∂p.response θ a = 0)
    (C : ℝ) (hC : 0 ≤ C) (hg : ∀ a z, |g a z| ≤ C) (u v : ℝ)
    (hα : ‖(1-(u:ℂ)^2*(v:ℂ)/2)‖≤1) (n : ℕ) :
    ‖characteristicSum p θ g u n-(1-(u:ℂ)^2*(v:ℂ)/2)^n‖ ≤
      u^2/2*(∑ k ∈ Finset.range n,varianceError p θ g v k)+(n:ℝ)*characteristicRemainder u C := by
  have hh := characteristic_telescope (characteristicSum p θ g u) _ _
    (characteristicSum_zero p θ g u) hα (characteristicSum_step_bound p θ g hm C hC hg u v) n
  simpa only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_range,nsmul_eq_mul] using hh

end
end QubitOracle.AdaptiveDesign.FiniteAdaptiveCharacteristic
