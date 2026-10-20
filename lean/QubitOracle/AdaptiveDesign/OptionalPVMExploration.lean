-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMPilotBornFisherIdentification
import QubitOracle.AdaptiveDesign.UniformHouseholderFrame

/-! The optional coordinate/two-coordinate library is an actual instance
of the main exploration-pilot theorem, with only a diverging exploration
budget for consistency and information convergence. -/
namespace QubitOracle.AdaptiveDesign.OptionalPVMExploration
open QubitOracle QubitOracle.Paper GlobalPFSIC GlobalPFSICHermitian PureMatrixController
open Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

def library (d : ℕ) : PVMGeneralGeometry.ExplorationLibrary d where
  count := Fintype.card (PVMGeometry.ExplorationIndex d)
  count_pos := by rw [library_card]; positivity
  basis k := PVMGeometry.explorationBasis ((Fintype.equivFin (PVMGeometry.ExplorationIndex d)).symm k)
  identifies A h := PVMGeometry.exploration_separates A (fun l k => by
    simpa using h ((Fintype.equivFin (PVMGeometry.ExplorationIndex d)) l) k)
  exploitationFrame := UniformHouseholderFrame.frame d

theorem library_count (d : ℕ) : (library d).count=(d+1)*(4*(d+1)+1) := library_card (d+1)

section
variable [PVMPilotSchedule.Schedule] (d : ℕ)
local instance : PVMGeneralGeometry.ExplorationLibrary d := library d

/-- No one-step or n^{3/4} exploration rate is required for these limits. -/
theorem consistency_information (hd : 0 < d) (truth : PureVector d)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize)
      (P2Adaptive.pureParameter d truth),
      Tendsto (PVMPilotAdaptive.rawEstimator d batchSize path) atTop (𝓝 (P2Adaptive.pureParameter d truth).val) ∧
      Tendsto (PVMPilotAdaptive.stateEstimator d batchSize path) atTop (𝓝 (rankOneDensity truth.val)) ∧
      Tendsto (fun n => PVMPilotAdaptive.actualBornFisher truth
        (n,(PVMPilotAdaptive.actualState d batchSize path n).action)) atTop
        (𝓝 ((1/2:ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) ∧
      (∀ x y : TangentIndex d, Tendsto (fun N : ℕ => (N:ℝ)⁻¹ * ∑ n ∈ Finset.range N,
        PVMPilotAdaptive.actualBornFisher truth (n,(PVMPilotAdaptive.actualState d batchSize path n).action) x y)
        atTop (𝓝 (((1/2:ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)) x y))) :=
  PVMPilotAdaptive.pureState_PVM_actualBorn_information d hd truth batchSize hpositive

theorem held_alignment (truth : PureVector d) (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize)
      (P2Adaptive.pureParameter d truth),
      Tendsto (fun n => frameProjector (PVMPilotAdaptive.measurementFrame d batchSize path n))
        atTop (𝓝 (rankOneDensity truth.val)) :=
  PVMPilotAdaptive.frozenController_ray_consistent d truth batchSize hpositive
end
end
end QubitOracle.AdaptiveDesign.OptionalPVMExploration

-/
