-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMPilotGLSEstimator

namespace QubitOracle.AdaptiveDesign.PVMPilotGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian TangentGLS
open MeasureTheory FiniteHistoryStatistics
noncomputable section
variable [PVMPilotSchedule.Schedule]
variable {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d]
variable {E : Type*}

theorem actualState_eq_of_agrees
    (batchSize : ℕ → ℕ)
    (n : ℕ) (path path' : AdaptiveInfinitePath (PVMPilotAdaptive.PVMOutcome d)) (h : ∀ k<n, path k = path' k) :
    PVMPilotAdaptive.actualState d batchSize path n =
      PVMPilotAdaptive.actualState d batchSize path' n := by
  unfold PVMPilotAdaptive.actualState ScheduledRidgeController.pathState
  rw [prefix_eq_of_agrees n path path' h]

theorem rawEstimator_eq_of_agrees
    (batchSize : ℕ → ℕ)
    (n : ℕ) (path path' : AdaptiveInfinitePath (PVMPilotAdaptive.PVMOutcome d)) (h : ∀ k<n, path k = path' k) :
    PVMPilotAdaptive.rawEstimator d batchSize path n =
      PVMPilotAdaptive.rawEstimator d batchSize path' n := by
  unfold PVMPilotAdaptive.rawEstimator
  rw [actualState_eq_of_agrees batchSize n path path' h]

theorem actualRecords_eq_of_agrees
    (batchSize : ℕ → ℕ)
    (n : ℕ) (path path' : AdaptiveInfinitePath (PVMPilotAdaptive.PVMOutcome d)) (h : ∀ k<n, path k = path' k) :
    actualRecords batchSize path n =
      actualRecords batchSize path' n := by
  funext t
  unfold actualRecords
  rw [actualState_eq_of_agrees batchSize t path path'
    (fun k hk => h k (hk.trans t.isLt)), h t t.isLt]

/-- Any function of the raw estimate and the complete records is measurable.
Its definition may use a noncomputable deterministic selector or linear solve. -/
theorem actualStatistic_stronglyMeasurable
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (batchSize : ℕ → ℕ) (n : ℕ)
    (statistic : HermitianSpace (d+1) → (Fin n → Record d (Fin (d+1))) → E) :
    StronglyMeasurable (fun path => statistic
      (PVMPilotAdaptive.rawEstimator d batchSize path n)
      (actualRecords batchSize path n)) := by
  apply stronglyMeasurable_of_past n
  intro path path' h
  rw [rawEstimator_eq_of_agrees batchSize n path path' h,
    actualRecords_eq_of_agrees batchSize n path path' h]

end
end QubitOracle.AdaptiveDesign.PVMPilotGLS

-/
