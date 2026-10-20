import QubitOracle.AdaptiveDesign.P1WeightedBorn
import QubitOracle.AdaptiveDesign.P1WeightedController
import QubitOracle.AdaptiveDesign.P1WeightedGeometry
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.MixedAxisFisher
import QubitOracle.Paper.MixedProbabilityFloor
import QubitOracle.Paper.MixedRotationalTarget
import QubitOracle.Paper.OneQubitCyclicBornPath
import QubitOracle.Paper.OneQubitLabeledThreeAxisBornKernel
import QubitOracle.Paper.P1UniformFrameBorn
import QubitOracle.Paper.P1UniformFrameInformation
/-! Supporting definitions and proved lemmas used by the manuscript. -/
namespace QubitOracle.AdaptiveDesign.MixedPaperAxisOrder
open QubitOracle QubitOracle.Paper P1Weighted
open scoped BigOperators
noncomputable section

def paperOrder : Equiv.Perm (Fin 3) := (Equiv.swap 0 2).trans (Equiv.swap 0 1)

theorem paperOrder_values : (fun k => paperOrder k) = ![2,0,1] := by
  funext k
  fin_cases k <;> decide

def reindex (a : Action) (e : Equiv.Perm (Fin 3)) : Action where
  frame :=
    { axis := fun k => a.frame.axis (e k)
      unit_axes := fun k => a.frame.unit_axes (e k)
      resolution := fun i j => by
        exact (Equiv.sum_comp e (fun k => (a.frame.axis k).val i *
          (a.frame.axis k).val j)).trans (a.frame.resolution i j) }
  weight := fun k => a.weight (e k)
  nonneg := fun k => a.nonneg (e k)
  total := (Equiv.sum_comp e a.weight).trans a.total

theorem reindex_joint_law (theta : OneQubitPhysicalParameter) (a : Action)
    (e : Equiv.Perm (Fin 3)) (k : Fin 3) (y : BinaryOutcome) :
    probability theta (reindex a e) (k,y) = probability theta a (e k,y) := rfl

theorem reindex_fisher (theta : Fin 3 → ℝ) (a : Action) (e : Equiv.Perm (Fin 3)) :
    fisher theta (reindex a e)=fisher theta a := by
  change (∑ k, a.weight (e k) • mixedAxisFisher theta (axis a (e k))) = _
  exact Equiv.sum_comp e (fun k => a.weight k • mixedAxisFisher theta (axis a k))


theorem paper_frobenius_weights (r : Fin 3 → ℝ) (hr : blochNormSq r < 1) :
    (reindex (referenceAction .frobenius r hr) paperOrder).weight =
      ![mixedRadialGap r/(2+mixedRadialGap r),
        1/(2+mixedRadialGap r),1/(2+mixedRadialGap r)] := by
  funext k
  change (referenceAction .frobenius r hr).weight (paperOrder k) = _
  rw [show paperOrder k = ![2,0,1] k from congrFun paperOrder_values k]
  fin_cases k <;>
    simp [referenceAction,weight,radialTangentMass,
      mixedRadialAllocation,mixedCoherenceAllocation,div_eq_mul_inv]

theorem paper_bures_weights (r : Fin 3 → ℝ) (hr : blochNormSq r < 1) :
    (reindex (referenceAction .bures r hr) paperOrder).weight = ![1/3,1/3,1/3] := by
  funext k
  change (referenceAction .bures r hr).weight (paperOrder k) = _
  rw [show paperOrder k = ![2,0,1] k from congrFun paperOrder_values k]
  fin_cases k <;> rfl

end
end QubitOracle.AdaptiveDesign.MixedPaperAxisOrder
