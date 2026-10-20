import QubitOracle.AdaptiveDesign.P1WeightedNormality
import QubitOracle.AdaptiveDesign.P1WeightedOptimality

/-! Physical-controller and completed-batch endpoints for both P1 rules. -/
namespace QubitOracle.AdaptiveDesign.P1Weighted
open QubitOracle QubitOracle.Paper Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
local instance : MeasurableSpace LabeledBinaryOutcome := ⊤
local instance : Nonempty LabeledBinaryOutcome := ⟨(0, .plus)⟩

theorem densityMap_continuous : Continuous qubitDensityMatrix := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;>
    simp only [qubitDensityMatrix,pauliLinear,Matrix.smul_apply,Matrix.add_apply] <;> fun_prop

theorem physical_state_consistent (loss : Loss) (ridge : ℝ) (hr : 0 < ridge) (refresh : ℕ → Bool)
    (θ : OneQubitPhysicalParameter) (hθ : blochNormSq θ.1 < 1) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (protocol (policy loss ridge refresh)) θ,
      Tendsto (fun n => qubitDensityMatrix (controller loss n (estimate loss ridge refresh n path)))
        atTop (𝓝 (qubitDensityMatrix θ.1)) := by
  filter_upwards [controller_consistent loss ridge hr refresh θ hθ] with path hp
  exact densityMap_continuous.continuousAt.tendsto.comp hp

theorem optimal_criterion_value (loss : Loss) (r : Fin 3 → ℝ) (hr : blochNormSq r < 1) :
    designCriterion loss r (informationTarget loss r) =
      match loss with
      | .bures => (9/4:ℝ)
      | .frobenius => (2+mixedRadialGap r)^2/2 := by
  cases loss with
  | bures => exact P1.mixedBuresTarget_bures_value r hr
  | frobenius => exact frobeniusTarget_value r hr

theorem covariance_at_center (loss : Loss) : covarianceTarget loss 0 = (3:ℝ) • (1:Mat) := by
  have ho : blochOuter (0 : Fin 3 → ℝ) = 0 := by ext i j; simp [blochOuter]
  cases loss <;> norm_num [covarianceTarget,mixedRadialGap,blochNormSq,ho]

def controllerError (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool) (θ : Fin 3 → ℝ)
    (n : ℕ) (path : Path) : Vector :=
  Real.sqrt (n:ℝ) • WithLp.toLp 2 (controller loss n (estimate loss ridge refresh n path)-θ)

theorem normalizedError_measurable (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool) (θ : Fin 3 → ℝ) (n : ℕ) :
    Measurable (normalizedError loss ridge refresh θ n) :=
  historyStatistic_measurable loss ridge refresh n (fun state =>
    Real.sqrt (n:ℝ) • WithLp.toLp 2 (state.gram⁻¹.mulVec state.rhs-θ))

theorem controllerError_measurable (loss : Loss) (ridge : ℝ) (refresh : ℕ → Bool) (θ : Fin 3 → ℝ) (n : ℕ) :
    Measurable (controllerError loss ridge refresh θ n) :=
  historyStatistic_measurable loss ridge refresh n (fun state =>
    Real.sqrt (n:ℝ) • WithLp.toLp 2 (controller loss n (state.gram⁻¹.mulVec state.rhs)-θ))

theorem controller_normal (loss : Loss) (ridge : ℝ) (hr : 0 < ridge)
    (refresh : ℕ → Bool) (hrefresh : ∀ K, ∃ n, K ≤ n ∧ refresh n = true)
    (θ : OneQubitPhysicalParameter) (hθ : blochNormSq θ.1 < 1) :
    TendstoInDistribution (controllerError loss ridge refresh θ.1) atTop id
      (fun _ => adaptiveInfiniteTrajectoryMeasure (protocol (policy loss ridge refresh)) θ)
      (multivariateGaussian 0 (covarianceTarget loss θ.1)) := by
  apply tendstoInDistribution_of_tendstoInMeasure_sub _ _
    (estimate_normal loss ridge hr refresh hrefresh θ hθ) _
    (fun n => (controllerError_measurable loss ridge refresh θ.1 n).aemeasurable)
  apply tendstoInMeasure_of_tendsto_ae
    (fun n => ((controllerError_measurable loss ridge refresh θ.1 n).sub
      (normalizedError_measurable loss ridge refresh θ.1 n)).aestronglyMeasurable)
  filter_upwards [estimate_consistent loss ridge hr refresh θ] with path hp
  have he := controller_eventually_eq hθ loss hp
  apply tendsto_const_nhds.congr'
  filter_upwards [he] with n hn
  simp [controllerError,normalizedError,hn]

theorem completed_batches_normal (loss : Loss) (ridge : ℝ) (hr : 0 < ridge)
    (m : ℕ → ℕ) (hm : ∀ j, 0 < m j) (θ : OneQubitPhysicalParameter) (hθ : blochNormSq θ.1 < 1) :
    TendstoInDistribution (fun j => normalizedError loss ridge (P1.batchRefresh m) θ.1 (P1.batchEndpoint m j)) atTop id
      (fun _ => adaptiveInfiniteTrajectoryMeasure (protocol (policy loss ridge (P1.batchRefresh m))) θ)
      (multivariateGaussian 0 (informationTarget loss θ.1)⁻¹) := by
  have hh := positive_batches_normal loss ridge hr m hm θ hθ
  exact { forall_aemeasurable := fun j => hh.forall_aemeasurable _
          aemeasurable_limit := hh.aemeasurable_limit
          tendsto := hh.tendsto.comp (P1.batchEndpoint_strictMono m hm).tendsto_atTop }

/-- The first theorem and its central-limit extension, stated for the same
literal protocol and all of its actual records. -/
theorem p1_main (loss : Loss) (ridge : ℝ) (hr : 0 < ridge)
    (m : ℕ → ℕ) (hm : ∀ j, 0 < m j) (θ : OneQubitPhysicalParameter) (hθ : blochNormSq θ.1 < 1) :
    (∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (protocol (policy loss ridge (P1.batchRefresh m))) θ,
      Tendsto (fun n => estimate loss ridge (P1.batchRefresh m) n path) atTop (𝓝 θ.1) ∧
      Tendsto (fun n => fisher θ.1 (actualAction (policy loss ridge (P1.batchRefresh m)) n path))
        atTop (𝓝 (informationTarget loss θ.1))) ∧
    TendstoInDistribution (normalizedError loss ridge (P1.batchRefresh m) θ.1) atTop id
      (fun _ => adaptiveInfiniteTrajectoryMeasure (protocol (policy loss ridge (P1.batchRefresh m))) θ)
      (multivariateGaussian 0 (informationTarget loss θ.1)⁻¹) := by
  refine ⟨?_,positive_batches_normal loss ridge hr m hm θ hθ⟩
  filter_upwards [positive_batches_consistency_information loss ridge hr m hm θ hθ] with path hp
  exact ⟨hp.1,hp.2.2.1⟩

end
end QubitOracle.AdaptiveDesign.P1Weighted
