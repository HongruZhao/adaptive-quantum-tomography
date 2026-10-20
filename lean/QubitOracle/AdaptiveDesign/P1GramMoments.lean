import QubitOracle.AdaptiveDesign.P1FiniteSampleBounds
import QubitOracle.AdaptiveDesign.AdaptiveResponseMoments
import QubitOracle.AdaptiveDesign.AdaptiveResponseStrongLaw
import QubitOracle.AdaptiveDesign.P1ObservedRidge
import QubitOracle.AdaptiveDesign.P1WeightedBorn
import QubitOracle.AdaptiveDesign.P1WeightedConsistency
import QubitOracle.AdaptiveDesign.P1WeightedMoments
import QubitOracle.AdaptiveDesign.P1WeightedPolicy
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.AdaptiveTrajectoryExperiment
import QubitOracle.Paper.MixedProbabilityFloor
import QubitOracle.Paper.OneQubitCyclicBornPath
import QubitOracle.Paper.OneQubitLabeledThreeAxisBornKernel
/-! All polynomial moments of the actual observed-axis Gram martingale,
without independence of the adaptively selected axes. -/
namespace QubitOracle.AdaptiveDesign.P1Weighted
open QubitOracle QubitOracle.Paper Filter MeasureTheory ProbabilityTheory AdaptiveResponseMoments
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
local instance P1GramMoments_measurable : MeasurableSpace LabeledBinaryOutcome := ⊤
local instance P1GramMoments_nonempty : Nonempty LabeledBinaryOutcome := ⟨(0,.plus)⟩

theorem gramDeviation_moments (p : Policy) (θ : OneQubitPhysicalParameter) (r : ℕ) :
    UniformMoment (adaptiveInfiniteTrajectoryMeasure (protocol p) θ)
      (fun n path => (Real.sqrt ((n+1:ℕ):ℝ))⁻¹ * entrySize (gramDeviation p (n+1) path)) r := by
  have hh (ij : Fin 3 × Fin 3) := (actualResponse_uniformMoment (protocol p) θ
    (fun a z => axis a z.1 ij.1*axis a z.1 ij.2-gram a ij.1 ij.2)
    (fun a => gram_centered_mean θ a ij.1 ij.2) 2 (by norm_num)
    (fun a z => gram_innovation_bound a z ij.1 ij.2) r).norm
  have hs := UniformMoment.finite_sum Finset.univ _ (fun ij _ => hh ij)
  simpa only [norm_mul,Real.norm_eq_abs,abs_of_nonneg (by positivity :
    0 ≤ (Real.sqrt ((_:ℕ):ℝ))⁻¹),← Finset.mul_sum,entrySize,gramDeviation,predictedGram,
    Matrix.sub_apply,Matrix.sum_apply,blochOuter,← Finset.sum_sub_distrib,Fintype.sum_prod_type,
    AdaptiveResponseStrongLaw.actualResponse,actualAxis,actualAction,protocol]
    using hs

end
end QubitOracle.AdaptiveDesign.P1Weighted
