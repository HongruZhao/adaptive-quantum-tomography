import QubitOracle.AdaptiveDesign.P1WeightedEndpoints

/-! Convergence of the actual inverse-information design criteria, for
the current design and both versions of accumulated information. -/
namespace QubitOracle.AdaptiveDesign.P1Weighted
open QubitOracle QubitOracle.Paper Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
local instance P1CriterionConvergence_measurable : MeasurableSpace LabeledBinaryOutcome := ⊤
local instance P1CriterionConvergence_nonempty : Nonempty LabeledBinaryOutcome := ⟨(0,.plus)⟩

def optimalValue (loss : Loss) (θ : Fin 3 → ℝ) : ℝ := match loss with
  | .bures => 9/4
  | .frobenius => (2+mixedRadialGap θ)^2/2

theorem criterion_tendsto (loss : Loss) (θ : Fin 3 → ℝ) (hθ : blochNormSq θ < 1)
    (A : ℕ → Mat) (hA : Tendsto A atTop (𝓝 (informationTarget loss θ))) :
    Tendsto (fun n => designCriterion loss θ (A n)) atTop (𝓝 (optimalValue loss θ)) := by
  have hI : (informationTarget loss θ).PosDef := by
    have hh := (covariance_posDef loss θ hθ).inv
    rwa [Matrix.inv_eq_left_inv (information_mul_covariance loss θ hθ)] at hh
  have hi := matrix_inv_tendsto hI hA
  have hc : Continuous (fun Q : Mat => match loss with
      | .bures => (1/4:ℝ)*((qubitSLDFisherInv θ)⁻¹*Q).trace
      | .frobenius => (1/2:ℝ)*Q.trace) := by
    cases loss <;> simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply] <;> fun_prop
  have ht := hc.continuousAt.tendsto.comp hi
  have he := optimal_criterion_value loss θ hθ
  change designCriterion loss θ (informationTarget loss θ)=optimalValue loss θ at he
  change Tendsto (fun n => designCriterion loss θ (A n)) atTop
    (𝓝 (designCriterion loss θ (informationTarget loss θ))) at ht
  rwa [he] at ht

theorem criteria_positive_batches (loss : Loss) (ridge : ℝ) (hr : 0 < ridge)
    (m : ℕ → ℕ) (hm : ∀ j, 0 < m j) (θ : OneQubitPhysicalParameter) (hθ : blochNormSq θ.1 < 1) :
    let p := policy loss ridge (P1.batchRefresh m)
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (protocol p) θ,
      Tendsto (fun n => designCriterion loss θ.1 (fisher θ.1 (actualAction p n path)))
        atTop (𝓝 (optimalValue loss θ.1)) ∧
      Tendsto (fun n : ℕ => designCriterion loss θ.1
        ((n:ℝ)⁻¹ • ∑ t ∈ Finset.range n, fisher θ.1 (actualAction p t path)))
        atTop (𝓝 (optimalValue loss θ.1)) ∧
      Tendsto (fun n : ℕ => designCriterion loss θ.1
        ((n:ℝ)⁻¹ • ∑ t ∈ Finset.range n, mixedAxisFisher θ.1 (actualAxis p t path)))
        atTop (𝓝 (optimalValue loss θ.1)) := by
  intro p
  filter_upwards [positive_batches_consistency_information loss ridge hr m hm θ hθ] with path hp
  refine ⟨criterion_tendsto loss θ.1 hθ _ hp.2.2.1,?_,?_⟩
  all_goals
    apply criterion_tendsto loss θ.1 hθ
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    simp only [Matrix.smul_apply,Matrix.sum_apply,smul_eq_mul]
  · exact hp.2.2.2.1 i j
  · exact hp.2.2.2.2 i j

end
end QubitOracle.AdaptiveDesign.P1Weighted
