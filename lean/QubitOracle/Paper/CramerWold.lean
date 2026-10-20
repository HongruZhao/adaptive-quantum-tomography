import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

namespace QubitOracle.Paper

open Filter MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

noncomputable section

/-- Finite-dimensional Cramer--Wold device, proved from Mathlib's
characteristic-function criterion.  Convergence of every real inner-product
projection implies convergence in distribution of the vector itself. -/
theorem cramerWold_tendstoInDistribution
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {nu : Measure E} [IsProbabilityMeasure nu]
    (X : ℕ → Omega → E)
    (hX : ∀ n, AEMeasurable (X n) mu)
    (hproj : ∀ u : E,
      TendstoInDistribution
        (fun n omega => ⟪u, X n omega⟫) atTop
        (fun x => ⟪u, x⟫) (fun _ => mu) nu) :
    TendstoInDistribution X atTop id (fun _ => mu) nu := by
  refine ⟨hX, measurable_id.aemeasurable, ?_⟩
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro u
  have hu := ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp (hproj u).tendsto 1
  convert hu using 1 <;>
    simp only [ProbabilityMeasure.coe_mk]
  · congr 2
    funext n
    rw [charFun_eq_charFunDual_toDualMap, charFunDual_eq_charFun_map_one,
      AEMeasurable.map_map_of_aemeasurable
        ((InnerProductSpace.toDualMap ℝ E) u).continuous.measurable.aemeasurable (hX n)]
    rfl
  · rw [charFun_eq_charFunDual_toDualMap, charFunDual_eq_charFun_map_one,
      AEMeasurable.map_map_of_aemeasurable
        ((InnerProductSpace.toDualMap ℝ E) u).continuous.measurable.aemeasurable
        measurable_id.aemeasurable]
    rfl

end


end QubitOracle.Paper
