import QubitOracle.AdaptiveDesign.P1CharacteristicLimit
import QubitOracle.AdaptiveDesign.BoundedAdaptiveResponseCLT

/-! Source-free multivariate CLT for the finite P1 experiment, obtained from
the elementary characteristic-function proof and Cramer--Wold. -/
namespace QubitOracle.AdaptiveDesign.P1Weighted
open QubitOracle QubitOracle.Paper Filter MeasureTheory ProbabilityTheory
open AdaptiveResponseStrongLaw AdaptiveRidgeConsistency
open scoped BigOperators Topology InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
local instance P1BoundedResponseCLT_outcomeMeasurable : MeasurableSpace LabeledBinaryOutcome := ⊤
local instance P1BoundedResponseCLT_outcomeNonempty : Nonempty LabeledBinaryOutcome := ⟨(0, .plus)⟩

theorem bounded_response_vector_clt (p : Policy) (θ : OneQubitPhysicalParameter)
    (g : Action → LabeledBinaryOutcome → Vector)
    (hm : ∀ a, ∫ z, g a z ∂kernel θ a = 0)
    (C : ℝ) (hC : 0 ≤ C) (hg : ∀ a z, ‖g a z‖ ≤ C) (M : Mat) (hM : M.PosDef)
    (hvar : ∀ u : Vector, ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (protocol p) θ,
      Tendsto (fun k => responseVariance θ (fun a z => ⟪u,g a z⟫_ℝ) (actualAction p (k+1) path))
        atTop (𝓝 (martingaleScoreQuadraticForm M u))) :
    (BoundedAdaptiveResponseCLT.problem (protocol p) θ g).VectorSumConvergesToGaussian M := by
  let problem := BoundedAdaptiveResponseCLT.problem (protocol p) θ g
  change TendstoInDistribution (fun n (path : Path) => problem.terminalSum n path) atTop id
    (fun _ => adaptiveInfiniteTrajectoryMeasure (protocol p) θ) (multivariateGaussian 0 M)
  apply cramerWold_tendstoInDistribution (fun n (path : Path) => problem.terminalSum n path)
    (BoundedAdaptiveResponseCLT.problem_terminal_measurable (protocol p) θ g)
  intro u
  have hscalar := bounded_response_scalar_clt p θ (fun a z => ⟪u,g a z⟫_ℝ)
    (fun a => by rw [integral_inner Integrable.of_finite,hm a,inner_zero_right])
    (‖u‖*C) (mul_nonneg (norm_nonneg _) hC)
    (fun a z => by
      change ‖⟪u,g a z⟫_ℝ‖ ≤ _
      exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hg a z) (norm_nonneg _)))
    (martingaleScoreQuadraticForm M u)
    (hM.posSemidef.dotProduct_mulVec_nonneg u.ofLp) (hvar u)
  have hprojection : ∀ n path, ⟪u,problem.terminalSum n path⟫_ℝ =
      normalizedResponse p (fun a z => ⟪u,g a z⟫_ℝ) n path := by
    intro n path
    simp [problem,MartingaleCLTProblem.terminalSum,BoundedAdaptiveResponseCLT.problem,
      BoundedAdaptiveResponseCLT.normalization,normalizedResponse,shiftedSum,
      inner_sum,inner_smul_right,Finset.mul_sum,actualVectorResponse,actualResponse,actualAction,protocol]
  have hlimit := multivariateGaussian_map_inner M hM.posSemidef u
  refine
    { forall_aemeasurable := fun n => hscalar.forall_aemeasurable n |>.congr
        (Eventually.of_forall (fun path => (hprojection n path).symm))
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
end QubitOracle.AdaptiveDesign.P1Weighted
