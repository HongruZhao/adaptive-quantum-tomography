import QubitOracle.AdaptiveDesign.TangentGLSGeometry
import QubitOracle.AdaptiveDesign.PhasePairAdaptive

/-!
# The actual all-observation estimator

Every record retains its finite POVM and observed label. We fit probabilities
from the unit leading-ray estimate, solve the protected tangent quadratic,
and normalize `h + Delta h`. Both stages use the full sample. Definitions
take no unknown true state, score limit, or asymptotic oracle.
-/

namespace QubitOracle.AdaptiveDesign.TangentGLS

open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController
open Filter MeasureTheory
open scoped BigOperators InnerProductSpace ComplexOrder
noncomputable section

structure Record (d : ℕ) (O : Type) [Fintype O] where
  measurement : FinitePOVM (Fin (d+1)) O
  outcome : O

variable {d n : ℕ} {O : Type} [Fintype O]

def recordFeature (data : Fin n → Record d O) (r : Fin n × O) : HermitianSpace (d+1) :=
  GeneralPOVM.effectVector (data r.1).measurement r.2

def observedIndicator (data : Fin n → Record d O) (r : Fin n × O) : ℝ := by
  classical
  exact if (data r.1).outcome = r.2 then 1 else 0

def fittedProbability (h : PureVector d) (data : Fin n → Record d O)
    (r : Fin n × O) : ℝ :=
  ⟪recordFeature data r, (P2Adaptive.pureParameter d h).val⟫_ℝ

theorem fittedProbability_eq_Born (h : PureVector d) (data : Fin n → Record d O)
    (r : Fin n × O) : fittedProbability h data r =
      (GlobalPFSIC.quadratic ((data r.1).measurement.effect r.2) h.val).re := by
  rw [fittedProbability, inner_eq_trace, Matrix.trace_mul_comm]
  change (Matrix.trace ((data r.1).measurement.effect r.2 *
    GlobalPFSIC.projector h.val)).re = _
  rw [trace_mul_projector]

def tangentFeature (h : PureVector d) (data : Fin n → Record d O)
    (r : Fin n × O) : tangentSpace h :=
  (tangentSpace h).orthogonalProjectionOnto (recordFeature data r)

theorem tangentFeature_inner (h : PureVector d) (data : Fin n → Record d O)
    (r : Fin n × O) (A : tangentSpace h) :
    ⟪tangentFeature h data r, A⟫_ℝ =
      (Matrix.trace ((data r.1).measurement.effect r.2 * toMatrix A.val)).re := by
  rw [tangentFeature, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
    inner_eq_trace, Matrix.trace_mul_comm]
  rfl

def fittedResidual (h : PureVector d) (data : Fin n → Record d O)
    (r : Fin n × O) : ℝ := observedIndicator data r - fittedProbability h data r

def recordCorrection (h : PureVector d) (data : Fin n → Record d O)
    (floor ridge : ℝ) (hf : 0 < floor) (hr : 0 < ridge) : tangentSpace h :=
  fittedCorrection (tangentFeature h data) (fittedProbability h data)
    (fittedResidual h data) floor ridge hf hr

theorem recordCorrection_minimizes (h : PureVector d) (data : Fin n → Record d O)
    (floor ridge : ℝ) (hf : 0 < floor) (hr : 0 < ridge) (A : tangentSpace h) :
    objective (tangentFeature h data)
      (fun r => (denominator floor (fittedProbability h data r))⁻¹)
      (fittedResidual h data) ridge (recordCorrection h data floor ridge hf hr) ≤
    objective (tangentFeature h data)
      (fun r => (denominator floor (fittedProbability h data r))⁻¹)
      (fittedResidual h data) ridge A :=
  correction_minimizes _ _ _ _ _ hr A

def estimateFromRaw (raw : HermitianSpace (d+1)) (data : Fin n → Record d O)
    (floor ridge : ℝ) (hf : 0 < floor) (hr : 0 < ridge) : PureVector d :=
  let h := nearestVector d (toMatrix raw)
  updatedPureVector h (recordCorrection h data floor ridge hf hr)

def referenceFloor [Nonempty O] (P : FinitePOVM (Fin (d+1)) O) : ℝ := by
  classical
  exact (Finset.univ.inf' Finset.univ_nonempty (referenceProbability P)) / 4

theorem referenceFloor_pos [Nonempty O] (P : FinitePOVM (Fin (d+1)) O)
    (hp : GeneralPOVM.Regular P) : 0 < referenceFloor P := by
  classical
  apply div_pos _ (by norm_num)
  exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun y _ => hp y)

def rotatedMeasurement (P : FinitePOVM (Fin (d+1)) O)
    (U : GlobalPFSICBorn.Action d) : FinitePOVM (Fin (d+1)) O where
  effect := GeneralPOVM.effect P U.matrix
  positive := GeneralPOVM.effect_positive P U.matrix
  complete := GeneralPOVM.effect_complete P U.matrix U.unitary

variable [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]

def actualRecords (P : FinitePOVM (Fin (d+1)) O) (hI : GeneralPOVM.Identifying P)
    (regularization : ℝ) (hr : 0 < regularization) (batchSize : ℕ → ℕ)
    (path : AdaptiveInfinitePath O) (n : ℕ) : Fin n → Record d O := fun t =>
  ⟨rotatedMeasurement P
    (GeneralPOVM.actualState P hI regularization hr batchSize path t).action, path t⟩

/-- The literal estimator from the paper under any general POVM protocol.
Reference regularity is used only to define its known positive denominator. -/
def actualEstimate (P : FinitePOVM (Fin (d+1)) O) (hI : GeneralPOVM.Identifying P)
    (hp : GeneralPOVM.Regular P) (regularization ridge : ℝ)
    (hr : 0 < regularization) (hη : 0 < ridge) (batchSize : ℕ → ℕ)
    (path : AdaptiveInfinitePath O) (n : ℕ) : PureVector d :=
  estimateFromRaw (GeneralPOVM.rawEstimator P hI regularization hr batchSize path n)
    (actualRecords P hI regularization hr batchSize path n)
    (referenceFloor P) ridge (referenceFloor_pos P hp) hη

def actualEstimatedState (P : FinitePOVM (Fin (d+1)) O) (hI : GeneralPOVM.Identifying P)
    (hp : GeneralPOVM.Regular P) (regularization ridge : ℝ)
    (hr : 0 < regularization) (hη : 0 < ridge) (batchSize : ℕ → ℕ)
    (path : AdaptiveInfinitePath O) (n : ℕ) : Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  rankOneDensity (actualEstimate P hI hp regularization ridge hr hη batchSize path n).val

theorem actualEstimatedState_physical
    (P : FinitePOVM (Fin (d+1)) O) (hI : GeneralPOVM.Identifying P)
    (hp : GeneralPOVM.Regular P) (regularization ridge : ℝ)
    (hr : 0 < regularization) (hη : 0 < ridge) (batchSize : ℕ → ℕ)
    (path : AdaptiveInfinitePath O) (n : ℕ) :
    (actualEstimatedState P hI hp regularization ridge hr hη batchSize path n).PosSemidef ∧
    Matrix.trace (actualEstimatedState P hI hp regularization ridge hr hη batchSize path n) = 1 ∧
    actualEstimatedState P hI hp regularization ridge hr hη batchSize path n *
      actualEstimatedState P hI hp regularization ridge hr hη batchSize path n =
      actualEstimatedState P hI hp regularization ridge hr hη batchSize path n :=
  ⟨GlobalPFSIC.projector_posSemidef _,
    rankOneDensity_trace_eq_one _ (actualEstimate P hI hp regularization ridge hr hη batchSize path n).property,
    pureProjector_idempotent _⟩

end
end QubitOracle.AdaptiveDesign.TangentGLS
