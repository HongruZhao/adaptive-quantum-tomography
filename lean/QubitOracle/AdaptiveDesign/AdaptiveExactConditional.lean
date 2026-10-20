-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.AdaptiveExactMoments
import QubitOracle.AdaptiveDesign.PVMSharpPilot

/-! Conditional vector identities for the actual complete adaptive path. -/
namespace QubitOracle.AdaptiveDesign.AdaptiveExactMoments
open QubitOracle.Paper Filter MeasureTheory ProbabilityTheory
open AdaptiveResponseStrongLaw AdaptiveConditionalMoments AdaptiveRidgeConsistency
open scoped BigOperators Topology InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Theta Action Outcome : Type}
  [MeasurableSpace Action] [MeasurableSpace Outcome]
  [Fintype Outcome] [MeasurableSingletonClass Outcome]
  [StandardBorelSpace Outcome] [Nonempty Outcome]

theorem conditional_response
    (p : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta)
    (g : Action → Outcome → ℝ) (C : ℝ) (hb : ∀ a y, ‖g a y‖≤C) (n : ℕ) :
    (adaptiveInfiniteTrajectoryMeasure p theta)[actualResponse p g n | past n]
      =ᵐ[adaptiveInfiniteTrajectoryMeasure p theta]
      (fun path => ∫ y, g (p.design n (adaptiveInfinitePathPrefix n path)) y
        ∂p.response theta (p.design n (adaptiveInfinitePathPrefix n path))) := by
  cases n with
  | zero =>
    change (adaptiveInfiniteTrajectoryMeasure p theta)[actualResponse p g 0 | ⊥] =ᵐ[_] _
    rw [condExp_bot,initial_integral]
    exact ae_of_all _ (fun _ => rfl)
  | succ n => exact actualResponse_condExp p theta g C hb n

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem vector_response_integrable
    (p : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta)
    (g : Action → Outcome → E) (C : ℝ) (hb : ∀ a y, ‖g a y‖≤C) (n : ℕ) :
    Integrable (actualVectorResponse p g n) (adaptiveInfiniteTrajectoryMeasure p theta) := by
  let b := stdOrthonormalBasis ℝ E
  have he : actualVectorResponse p g n = fun path =>
      ∑ i, actualResponse p (fun a y => ⟪b i,g a y⟫_ℝ) n path • b i := by
    funext path
    exact (b.sum_repr' _).symm
  rw [he]
  apply integrable_finset_sum
  intro i hi
  exact (actualResponse_integrable p theta _ C (fun a y =>
    (norm_inner_le_norm _ _).trans (by simpa [b.norm_eq_one] using hb a y)) n).smul_const _

theorem vector_conditional_zero
    (p : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta)
    (g : Action → Outcome → E) (hm : ∀ a, ∫ y, g a y ∂p.response theta a=0)
    (C : ℝ) (hb : ∀ a y, ‖g a y‖≤C) (n : ℕ) :
    (adaptiveInfiniteTrajectoryMeasure p theta)[actualVectorResponse p g n | past n]
      =ᵐ[adaptiveInfiniteTrajectoryMeasure p theta] 0 := by
  letI : IsMarkovKernel (p.response theta) := p.response_isMarkov theta
  let b := stdOrthonormalBasis ℝ E
  let μ := adaptiveInfiniteTrajectoryMeasure p theta
  have hi := vector_response_integrable p theta g C hb n
  have hcoord (i : Fin (Module.finrank ℝ E)) :
      ∀ᵐ path ∂μ, ⟪b i,μ[actualVectorResponse p g n | past n] path⟫_ℝ=0 := by
    have hcomm := (innerSL ℝ (b i)).comp_condExp_comm (m:=past n) hi
    have hc := centered_past p theta (fun a y => ⟪b i,g a y⟫_ℝ)
      (fun a => by rw [integral_inner Integrable.of_finite,hm a,inner_zero_right])
      C (fun a y => (norm_inner_le_norm _ _).trans (by simpa [b.norm_eq_one] using hb a y)) n
    filter_upwards [hcomm,hc] with path hpath hzero
    exact hpath.trans hzero
  filter_upwards [ae_all_iff.mpr hcoord] with path hpath
  have hh := b.sum_repr' (μ[actualVectorResponse p g n | past n] path)
  change μ[actualVectorResponse p g n | past n] path=0
  simpa only [hpath,zero_smul,Finset.sum_const_zero] using hh.symm

theorem vector_conditional_variance_le
    (p : PredictableAdaptiveProtocol Theta (ℕ × Action) Outcome) (theta : Theta)
    (htime : ∀ n h, (p.design n h).1=n)
    (g : (ℕ × Action) → Outcome → E) (C : ℝ) (hb : ∀ a y, ‖g a y‖≤C)
    (v : ℕ → ℝ) (hv : ∀ a, ∫ y, ‖g a y‖^2 ∂p.response theta a≤v a.1) (n : ℕ) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure p theta,
      (adaptiveInfiniteTrajectoryMeasure p theta)[fun path => ‖actualVectorResponse p g n path‖^2
        | past n] path≤v n := by
  have h := conditional_response p theta (fun a y => ‖g a y‖^2) (C^2)
    (fun a y => by rw [norm_pow,norm_norm]; exact pow_le_pow_left₀ (norm_nonneg _) (hb a y) 2) n
  filter_upwards [h] with path hpath
  change (adaptiveInfiniteTrajectoryMeasure p theta)[actualResponse p (fun a y => ‖g a y‖^2) n | past n] path≤v n
  rw [hpath]
  simpa only [htime] using hv (p.design n (adaptiveInfinitePathPrefix n path))

end
end QubitOracle.AdaptiveDesign.AdaptiveExactMoments

namespace QubitOracle.AdaptiveDesign.PVMSharpPilot
open QubitOracle.Paper GlobalPFSICBorn PVMPilotAdaptive PVMPilotRegression PVMGeometry PVMPilotSchedule
open MeasureTheory ProbabilityTheory
noncomputable section
variable [PVMPilotSchedule.Schedule] {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d]

theorem actual_exploration_conditional_mean (batchSize : ℕ → ℕ)
    (theta : PhysicalParameter (d+1)) (n : ℕ) :
    (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol d batchSize) theta)[AdaptiveRidgeConsistency.actualVectorResponse (adaptiveProtocol d batchSize) (noise theta) n
        | AdaptiveExactMoments.past n]
      =ᵐ[adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol d batchSize) theta] 0 :=
  AdaptiveExactMoments.vector_conditional_zero (adaptiveProtocol d batchSize) theta
    (noise theta) (noise_mean theta) (2*basisBound d) (noise_bound theta) n

theorem actual_exploration_conditional_variance (batchSize : ℕ → ℕ)
    (theta : PhysicalParameter (d+1)) (n : ℕ) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol d batchSize) theta,
      (adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol d batchSize) theta)[fun path => ‖AdaptiveRidgeConsistency.actualVectorResponse (adaptiveProtocol d batchSize)
          (noise theta) n path‖^2 | AdaptiveExactMoments.past n] path≤epsilon n :=
  AdaptiveExactMoments.vector_conditional_variance_le (adaptiveProtocol d batchSize) theta
    (fun _ _ => rfl) (noise theta) (2*basisBound d) (noise_bound theta)
    epsilon (PVMSharpMoments.noise_norm_square_le theta) n

end
end QubitOracle.AdaptiveDesign.PVMSharpPilot

-/
