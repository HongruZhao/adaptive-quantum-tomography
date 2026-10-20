import QubitOracle.AdaptiveDesign.AdaptiveResponseStrongLaw
import QubitOracle.AdaptiveDesign.P1PositiveBatches
import QubitOracle.AdaptiveDesign.P1WeightedBorn
import QubitOracle.AdaptiveDesign.P1WeightedConsistency
import QubitOracle.AdaptiveDesign.P1WeightedController
import QubitOracle.AdaptiveDesign.P1WeightedPolicy
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.AdaptiveTrajectoryExperiment
import QubitOracle.Paper.MixedAxisFisher
import QubitOracle.Paper.MixedInformationMartingale
import QubitOracle.Paper.MixedProbabilityFloor
import QubitOracle.Paper.MixedRadialTangentStage
import QubitOracle.Paper.MixedRotationalTarget
import QubitOracle.Paper.MixedStageStability
import QubitOracle.Paper.OneQubitCyclicBornPath
import QubitOracle.Paper.OneQubitGeneralScheduleFrobeniusTraceInformation
import QubitOracle.Paper.OneQubitLabeledThreeAxisBornKernel
import QubitOracle.Paper.P1AdaptiveRidgePolicy
import QubitOracle.Paper.P1UniformFrameBorn
/-! Both P1 Fisher limits for the actual protocol, including the empirical
realized-setting average and arbitrary positive finite batch schedules. -/
namespace QubitOracle.AdaptiveDesign.P1Weighted
open QubitOracle QubitOracle.Paper Filter MeasureTheory
open AdaptiveResponseStrongLaw
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
local instance : MeasurableSpace LabeledBinaryOutcome := ⊤
local instance : Nonempty LabeledBinaryOutcome := ⟨(0, .plus)⟩

def informationTarget (loss : Loss) (θ : Fin 3 → ℝ) : Mat :=
  match loss with
  | .bures => mixedBuresTarget θ
  | .frobenius => mixedFrobeniusTraceTarget θ

theorem reference_fisher (loss : Loss) (θ r : Fin 3 → ℝ) (hr : blochNormSq r < 1) :
    fisher θ (referenceAction loss r hr) = mixedStageInformation θ (weight loss r)
      (radialTangentAxes (mixedCanonicalRadialTangentFrame r).tangentFirst
        (mixedCanonicalRadialTangentFrame r).tangentSecond (mixedCanonicalRadialTangentFrame r).radial) := rfl

theorem reference_fisher_tendsto (loss : Loss) (θ : Fin 3 → ℝ) (hθ : blochNormSq θ < 1)
    (r : ℕ → Fin 3 → ℝ) (hr : Tendsto r atTop (𝓝 θ)) (hri : ∀ n, blochNormSq (r n) < 1) :
    Tendsto (fun n => fisher θ (referenceAction loss (r n) (hri n))) atTop (𝓝 (informationTarget loss θ)) := by
  simp_rw [reference_fisher]
  cases loss with
  | bures => exact mixedBuresStage_tendsto θ hθ r hr hri (fun n => mixedCanonicalRadialTangentFrame (r n))
  | frobenius => exact mixedFrobeniusTraceStage_tendsto θ hθ r hr hri (fun n => mixedCanonicalRadialTangentFrame (r n))

theorem controller_consistent (loss : Loss) (ridge : ℝ) (hr : 0 < ridge) (refresh : ℕ → Bool)
    (θ : OneQubitPhysicalParameter) (hθ : blochNormSq θ.1 < 1) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (protocol (policy loss ridge refresh)) θ,
      Tendsto (fun n => controller loss n (estimate loss ridge refresh n path)) atTop (𝓝 θ.1) := by
  filter_upwards [estimate_consistent loss ridge hr refresh θ] with path hp
  exact hp.congr' (controller_eventually_eq hθ loss hp).symm

theorem current_information_tendsto (loss : Loss) (ridge : ℝ) (hr : 0 < ridge)
    (refresh : ℕ → Bool) (hrefresh : ∀ K, ∃ n, K ≤ n ∧ refresh n = true)
    (θ : OneQubitPhysicalParameter) (hθ : blochNormSq θ.1 < 1) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (protocol (policy loss ridge refresh)) θ,
      Tendsto (fun n => fisher θ.1 (actualAction (policy loss ridge refresh) n path))
        atTop (𝓝 (informationTarget loss θ.1)) := by
  filter_upwards [controller_consistent loss ridge hr refresh θ hθ] with path hp
  have hheld := hp.comp (P1.lastRefresh_tendsto refresh hrefresh)
  have hi := reference_fisher_tendsto loss θ.1 hθ _ hheld
    (fun n => controller_interior loss (P1.lastRefresh refresh n) _)
  simpa only [action_eq_lastRefresh,controllerAction,Function.comp_apply] using hi

theorem fisher_entry_bound (θ : Fin 3 → ℝ) (hθ : blochNormSq θ < 1) (a : Action) (i j : Fin 3) :
    |fisher θ a i j| ≤ (1-blochNormSq θ)⁻¹ := by
  simp only [fisher,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  calc
    _ ≤ ∑ k, |a.weight k * mixedAxisFisher θ (axis a k) i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, a.weight k * (1-blochNormSq θ)⁻¹ := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul,abs_of_nonneg (a.nonneg k)]
      exact mul_le_mul_of_nonneg_left
        (mixedAxisInformation_entry_norm_le θ (axis a k) hθ (a.frame.unit_axes k) i j) (a.nonneg k)
    _ = _ := by rw [← Finset.sum_mul,a.total,one_mul]

theorem fisher_innovation_mean (θ : OneQubitPhysicalParameter) (a : Action) (i j : Fin 3) :
    ∫ z, (mixedAxisFisher θ.1 (axis a z.1) i j - fisher θ.1 a i j) ∂kernel θ a = 0 := by
  rw [integral_label θ a (fun k => mixedAxisFisher θ.1 (axis a k) i j - fisher θ.1 a i j)]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib,← Finset.sum_mul,a.total,one_mul]
  simp [fisher,Matrix.sum_apply,Matrix.smul_apply]

theorem fisher_innovation_bound (θ : Fin 3 → ℝ) (hθ : blochNormSq θ < 1)
    (a : Action) (z : LabeledBinaryOutcome) (i j : Fin 3) :
    ‖mixedAxisFisher θ (axis a z.1) i j - fisher θ a i j‖ ≤ 2*(1-blochNormSq θ)⁻¹ := by
  have h1 := mixedAxisInformation_entry_norm_le θ (axis a z.1) hθ (a.frame.unit_axes z.1) i j
  have h2 := fisher_entry_bound θ hθ a i j
  rw [Real.norm_eq_abs] at h1
  rw [Real.norm_eq_abs]
  exact (abs_sub _ _).trans (by simpa only [Real.norm_eq_abs] using (by linarith :
    |mixedAxisFisher θ (axis a z.1) i j| + |fisher θ a i j| ≤ 2*(1-blochNormSq θ)⁻¹))

theorem fisher_innovation_average (p : Policy) (θ : OneQubitPhysicalParameter)
    (hθ : blochNormSq θ.1 < 1) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (protocol p) θ, ∀ i j : Fin 3,
      Tendsto (fun n : ℕ => (n:ℝ)⁻¹ * ∑ t ∈ Finset.range n,
        (mixedAxisFisher θ.1 (actualAxis p t path) i j - fisher θ.1 (actualAction p t path) i j))
        atTop (𝓝 0) := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  apply actualResponse_average_ae_tendsto_zero (protocol p) θ
    (fun a z => mixedAxisFisher θ.1 (axis a z.1) i j - fisher θ.1 a i j)
    (fun a => fisher_innovation_mean θ a i j) (2*(1-blochNormSq θ.1)⁻¹)
    (by have hh := sub_pos.mpr hθ; positivity)
  exact fun a z => fisher_innovation_bound θ.1 hθ a z i j

/-- Both P1 rules: literal estimator and controller consistency, current
information and both accumulated-information limits. No statistical axiom. -/
theorem positive_batches_consistency_information (loss : Loss) (ridge : ℝ) (hr : 0 < ridge)
    (m : ℕ → ℕ) (hm : ∀ j, 0 < m j) (θ : OneQubitPhysicalParameter) (hθ : blochNormSq θ.1 < 1) :
    let p := policy loss ridge (P1.batchRefresh m)
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (protocol p) θ,
      Tendsto (fun n => estimate loss ridge (P1.batchRefresh m) n path) atTop (𝓝 θ.1) ∧
      Tendsto (fun n => controller loss n (estimate loss ridge (P1.batchRefresh m) n path)) atTop (𝓝 θ.1) ∧
      Tendsto (fun n => fisher θ.1 (actualAction p n path)) atTop (𝓝 (informationTarget loss θ.1)) ∧
      (∀ i j, Tendsto (fun n : ℕ => (n:ℝ)⁻¹ * ∑ t ∈ Finset.range n,
        fisher θ.1 (actualAction p t path) i j) atTop (𝓝 (informationTarget loss θ.1 i j))) ∧
      (∀ i j, Tendsto (fun n : ℕ => (n:ℝ)⁻¹ * ∑ t ∈ Finset.range n,
        mixedAxisFisher θ.1 (actualAxis p t path) i j) atTop (𝓝 (informationTarget loss θ.1 i j))) := by
  intro p
  filter_upwards [estimate_consistent loss ridge hr (P1.batchRefresh m) θ,
    controller_consistent loss ridge hr (P1.batchRefresh m) θ hθ,
    current_information_tendsto loss ridge hr (P1.batchRefresh m) (P1.batchRefresh_unbounded m hm) θ hθ,
    fisher_innovation_average p θ hθ] with path he hc hi hn
  have ha : ∀ i j, Tendsto (fun n : ℕ => (n:ℝ)⁻¹ * ∑ t ∈ Finset.range n,
      fisher θ.1 (actualAction p t path) i j) atTop (𝓝 (informationTarget loss θ.1 i j)) := by
    intro i j
    exact (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hi i) j).cesaro_smul
  refine ⟨he,hc,hi,ha,?_⟩
  intro i j
  convert (ha i j).add (hn i j) using 1
  · ext n
    rw [Finset.sum_sub_distrib]
    ring
  · ring

end
end QubitOracle.AdaptiveDesign.P1Weighted
