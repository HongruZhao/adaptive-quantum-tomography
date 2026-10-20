import QubitOracle.AdaptiveDesign.TangentGLSRetraction
import QubitOracle.AdaptiveDesign.TangentGLSProjection
import QubitOracle.AdaptiveDesign.GeneralPOVMQuarterRate
import QubitOracle.AdaptiveDesign.ProtectedBornScore
import QubitOracle.AdaptiveDesign.TangentGLSVarianceStatement

/-!
# Scope-aware audit of the vector GLS revision

Every printed theorem below is proved. `OptimalVarianceStatement` is only a
definition of the outstanding end-to-end claim; checking its type is NOT a
proof of the estimator CLT. No theorem asserting that proposition is audited.
-/

open QubitOracle QubitOracle.Paper QubitOracle.AdaptiveDesign
open PureMatrixController
open scoped BigOperators Topology ComplexOrder
noncomputable section

#print axioms TangentGLS.recordCorrection_minimizes
#print axioms TangentGLS.correction_unique
#print axioms TangentGLS.fittedProbability_eq_Born
#print axioms TangentGLS.unnormalizedVector_norm_sq
#print axioms TangentGLS.actualEstimatedState_physical
#print axioms TangentGLS.updatedState_matrix_formula
#print axioms TangentGLS.updatedState_exact_remainder
#print axioms TangentGLS.tangentProjectionVector_eq_projection
#print axioms TangentGLS.preliminaryError_normal_quadratic
#print axioms TangentGLS.fittedScore_exact_expansion
#print axioms TangentGLS.recordCorrection_exact_cancellation
#print axioms GeneralPOVMQuarterRate.rawEstimator_quarterRate
#print axioms GeneralPOVMQuarterRate.stateEstimator_quarterRate
#print axioms AdaptiveConditionalMoments.actualResponse_condExp
#print axioms ProtectedBornScore.response_mean_zero
#print axioms ProtectedBornScore.actual_secondMoment_limit
#print axioms ProtectedBornScore.actual_score_clt
#print axioms ProtectedBornScore.phasePair_actual_score_clt

-- Elaboration of the intended conclusion; no proof is asserted here.
#check TangentGLS.OptimalVarianceStatement

namespace TangentGLSAudit

variable {O : Type} [Fintype O] [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]

/-- A non-qubit physical estimator, with literal raw and correction ridges. -/
theorem qutrit_estimator_physical
    (P : FinitePOVM (Fin 3) O) (hI : GeneralPOVM.Identifying P) (hp : GeneralPOVM.Regular P)
    (path : AdaptiveInfinitePath O) (n : ℕ) :
    (TangentGLS.actualEstimatedState P hI hp 2 1 (by norm_num) (by norm_num) (fun _ => 1) path n).PosSemidef ∧
    Matrix.trace (TangentGLS.actualEstimatedState P hI hp 2 1 (by norm_num) (by norm_num)
      (fun _ => 1) path n) = 1 ∧
    TangentGLS.actualEstimatedState P hI hp 2 1 (by norm_num) (by norm_num) (fun _ => 1) path n *
      TangentGLS.actualEstimatedState P hI hp 2 1 (by norm_num) (by norm_num) (fun _ => 1) path n =
      TangentGLS.actualEstimatedState P hI hp 2 1 (by norm_num) (by norm_num) (fun _ => 1) path n :=
  TangentGLS.actualEstimatedState_physical P hI hp 2 1 (by norm_num) (by norm_num) (fun _ => 1) path n

/-- The actual qutrit score CLT, using any admissible seed and unit batches. -/
theorem qutrit_score_clt
    (P : FinitePOVM (Fin 3) O) (hI : GeneralPOVM.Identifying P) (hp : GeneralPOVM.Regular P)
    (hR : PhasePair.RankOne P) (truth : PureVector 2) :
    (BoundedAdaptiveResponseCLT.problem
      (GeneralPOVM.adaptiveProtocol (PhasePair.paired P) (PhasePair.paired_identifying P hI)
        2 (by norm_num) (fun _ => 1)) truth
      (ProtectedBornScore.response (PhasePair.paired P) truth
        (TangentGLS.referenceFloor (PhasePair.paired P)))).VectorSumConvergesToGaussian
      ((1/2 : ℝ) • (1 : Matrix (TangentIndex 2) (TangentIndex 2) ℝ)) :=
  ProtectedBornScore.phasePair_actual_score_clt P hI hp hR truth 2 (by norm_num)
    (fun _ => 1) (fun _ => by norm_num)

#print axioms qutrit_estimator_physical
#print axioms qutrit_score_clt

end TangentGLSAudit
end
