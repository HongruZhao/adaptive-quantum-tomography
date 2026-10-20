-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMPilotRate
import QubitOracle.AdaptiveDesign.TangentGLSRecordIdentities

/-! The corrected estimator for actual selected PVM records. Selection
probabilities enter the adaptive path law; fitted probabilities here are
conditional on the recorded basis. No sample is discarded or split. -/
namespace QubitOracle.AdaptiveDesign.PVMPilotGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian GlobalPFSICBorn
open PureMatrixController P2Adaptive TangentGLS PVMGeometry PVMPilotBorn
open scoped BigOperators InnerProductSpace ComplexOrder
noncomputable section
variable [PVMPilotSchedule.Schedule]
variable {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d]

def basisMeasurement (U : Action d) : FinitePOVM (Fin (d+1)) (Fin (d+1)) where
  effect k := toMatrix (basisEffect U k)
  positive := basisEffect_positive U
  complete := basisEffect_sum U

def actualRecords (batchSize : ℕ → ℕ) (path : AdaptiveInfinitePath (PVMPilotAdaptive.PVMOutcome d))
    (n : ℕ) : Fin n → Record d (Fin (d+1)) := fun t =>
  ⟨basisMeasurement (settingBasis (PVMPilotAdaptive.actualState d batchSize path t).action
    (path t).1), (path t).2⟩

/-- Floor one makes every probability weight exactly one: ordinary tangent LS. -/
def floor (_d : ℕ) : ℝ := 1
lemma floor_pos (d : ℕ) : 0 < floor d := by unfold floor; positivity

def actualPreliminary (batchSize : ℕ → ℕ)
    (path : AdaptiveInfinitePath (PVMPilotAdaptive.PVMOutcome d)) (n : ℕ) : PureVector d :=
  nearestVector d (toMatrix (PVMPilotAdaptive.rawEstimator d batchSize path n))

def actualDelta (ridge : ℝ) (hr : 0 < ridge) (batchSize : ℕ → ℕ)
    (path : AdaptiveInfinitePath (PVMPilotAdaptive.PVMOutcome d)) (n : ℕ) :
    tangentSpace (actualPreliminary batchSize path n) :=
  recordCorrection (actualPreliminary batchSize path n) (actualRecords batchSize path n)
    (floor d) ridge (floor_pos d) hr

def actualEstimate (ridge : ℝ) (hr : 0 < ridge) (batchSize : ℕ → ℕ)
    (path : AdaptiveInfinitePath (PVMPilotAdaptive.PVMOutcome d)) (n : ℕ) : PureVector d :=
  updatedPureVector (actualPreliminary batchSize path n) (actualDelta ridge hr batchSize path n)

def actualEstimatedState (ridge : ℝ) (hr : 0 < ridge) (batchSize : ℕ → ℕ)
    (path : AdaptiveInfinitePath (PVMPilotAdaptive.PVMOutcome d)) (n : ℕ) :
    Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  rankOneDensity (actualEstimate ridge hr batchSize path n).val

theorem actualEstimatedState_physical (ridge : ℝ) (hr : 0 < ridge) (batchSize : ℕ → ℕ)
    (path : AdaptiveInfinitePath (PVMPilotAdaptive.PVMOutcome d)) (n : ℕ) :
    (actualEstimatedState ridge hr batchSize path n).PosSemidef ∧
    Matrix.trace (actualEstimatedState ridge hr batchSize path n) = 1 ∧
    actualEstimatedState ridge hr batchSize path n * actualEstimatedState ridge hr batchSize path n =
      actualEstimatedState ridge hr batchSize path n :=
  ⟨GlobalPFSIC.projector_posSemidef _, rankOneDensity_trace_eq_one _
    (actualEstimate ridge hr batchSize path n).property, pureProjector_idempotent _⟩

theorem actualDelta_minimizes (ridge : ℝ) (hr : 0 < ridge) (batchSize : ℕ → ℕ)
    (path : AdaptiveInfinitePath (PVMPilotAdaptive.PVMOutcome d)) (n : ℕ)
    (A : tangentSpace (actualPreliminary batchSize path n)) :
    objective (tangentFeature (actualPreliminary batchSize path n) (actualRecords batchSize path n))
      (fun r => (denominator (floor d)
        (fittedProbability (actualPreliminary batchSize path n) (actualRecords batchSize path n) r))⁻¹)
      (fittedResidual (actualPreliminary batchSize path n) (actualRecords batchSize path n)) ridge
      (actualDelta ridge hr batchSize path n) ≤
    objective (tangentFeature (actualPreliminary batchSize path n) (actualRecords batchSize path n))
      (fun r => (denominator (floor d)
        (fittedProbability (actualPreliminary batchSize path n) (actualRecords batchSize path n) r))⁻¹)
      (fittedResidual (actualPreliminary batchSize path n) (actualRecords batchSize path n)) ridge A :=
  recordCorrection_minimizes _ _ _ _ _ _ A

/-- Each record is an actual orthogonal PVM, not a weighted joint effect. -/
theorem recordFeature_eq (batchSize : ℕ → ℕ)
    (path : AdaptiveInfinitePath (PVMPilotAdaptive.PVMOutcome d)) (n : ℕ)
    (r : Fin n × Fin (d+1)) :
    recordFeature (actualRecords batchSize path n) r =
      basisEffect (settingBasis (PVMPilotAdaptive.actualState d batchSize path r.1).action
        (path r.1).1) r.2 := by
  rfl

end
end QubitOracle.AdaptiveDesign.PVMPilotGLS

-/
