import QubitOracle.Paper.HallHeydeAxiomConsolidation

/-!
# Martingale score CLT using one Hall--Heyde source atom

The legacy score-CLT layer used a fixed-row Hall--Heyde declaration.  The
source-faithful arbitrary-row theorem is stronger, and
`HallHeydeAxiomConsolidation` derives that fixed-row signature inside Lean.
The theorems below mirror the scalar and vector score CLTs while depending on
only the source-faithful Hall--Heyde declaration.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

noncomputable section

/-- Scalar projections of a finite-dimensional martingale score converge to
the corresponding centered Gaussian laws, using the consolidated source
interface. -/
theorem martingale_score_clt_consolidated
    {D : Type*} [Fintype D]
    (problem : MartingaleCLTProblem D)
    (M : Matrix D D Real) (hM : M.PosDef)
    (hMDS : problem.IsSquareIntegrableMartingaleDifferenceArray)
    (hLindeberg : problem.HasConditionalLindeberg)
    (hCovariance : problem.ConditionalCovarianceConverges M) :
    problem.SumConvergesToGaussian M := by
  letI : MeasurableSpace problem.Omega := problem.measurableSpace
  letI : IsProbabilityMeasure problem.mu := problem.probabilityMeasure
  intro u
  exact hallHeyde1980_corollary3_1_of_deterministicVariance_external
    problem.mu problem.filtration (problem.projectedIncrement u)
    (martingaleScoreQuadraticForm M u)
    ((Matrix.PosDef.posSemidef hM).dotProduct_mulVec_nonneg
      (fun i => u.ofLp i))
    (hMDS.1 u) (hMDS.2.1 u) hMDS.2.2
    (hLindeberg u) (hCovariance u)

/-- Multivariate Cramer--Wold closure of the consolidated scalar score CLT. -/
theorem martingale_score_clt_multivariate_consolidated
    {D : Type*} [Fintype D] [DecidableEq D]
    (problem : MartingaleCLTProblem D)
    (M : Matrix D D Real) (hM : M.PosDef)
    (hMDS : problem.IsSquareIntegrableMartingaleDifferenceArray)
    (hLindeberg : problem.HasConditionalLindeberg)
    (hCovariance : problem.ConditionalCovarianceConverges M)
    (hTerminalMeasurable : forall n,
      AEMeasurable (problem.terminalSum n) problem.mu) :
    problem.VectorSumConvergesToGaussian M := by
  letI : MeasurableSpace problem.Omega := problem.measurableSpace
  letI : IsProbabilityMeasure problem.mu := problem.probabilityMeasure
  apply cramerWold_tendstoInDistribution
    problem.terminalSum hTerminalMeasurable
  intro u
  have hscalar := martingale_score_clt_consolidated
    problem M hM hMDS hLindeberg hCovariance u
  have hprojection : forall n omega,
      inner Real u (problem.terminalSum n omega) =
        martingaleArrayTerminalSum (problem.projectedIncrement u) n omega := by
    intro n omega
    exact inner_sum (Finset.range n)
      (fun i => problem.increment n i omega) u
  have hlimit := multivariateGaussian_map_inner M hM.posSemidef u
  refine
    { forall_aemeasurable := fun n =>
        hscalar.forall_aemeasurable n |>.congr
          (Filter.Eventually.of_forall fun omega => (hprojection n omega).symm)
      aemeasurable_limit :=
        (Continuous.inner continuous_const continuous_id').aemeasurable
      tendsto := ?_ }
  let pvec : ProbabilityMeasure Real :=
    ⟨Measure.map ((innerSL Real) u) (multivariateGaussian 0 M),
      Measure.isProbabilityMeasure_map
        ((innerSL Real) u).measurable.aemeasurable⟩
  let pscalar : ProbabilityMeasure Real :=
    ⟨gaussianReal 0 (martingaleScoreQuadraticForm M u).toNNReal,
      inferInstance⟩
  have hlimitProbability : pvec = pscalar :=
    Subtype.ext hlimit
  have htarget :
      (⟨Measure.map (fun x => inner Real u x) (multivariateGaussian 0 M),
          Measure.isProbabilityMeasure_map
            (Continuous.inner continuous_const continuous_id').aemeasurable⟩ :
        ProbabilityMeasure Real) = pvec :=
    Subtype.ext rfl
  rw [htarget, hlimitProbability]
  simpa only [pscalar, hprojection, Measure.map_id] using hscalar.tendsto

end
end QubitOracle.Paper
