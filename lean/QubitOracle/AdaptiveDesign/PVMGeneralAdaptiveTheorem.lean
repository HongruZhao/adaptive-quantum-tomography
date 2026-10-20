-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMGeneralExplorationModel
import QubitOracle.AdaptiveDesign.P2AdaptiveTheorem

/-! P2's second algorithm: actual PVMs, an arbitrary identifying exploration library and vanishing exploration,
all-observation consistency and optimal information, for every finite dimension. -/
namespace QubitOracle.AdaptiveDesign.PVMGeneralAdaptive
open Filter MeasureTheory ProbabilityTheory QubitOracle QubitOracle.Paper
open GlobalPFSIC GlobalPFSICHermitian GlobalPFSICBorn PureMatrixController
open PVMGeneralExploration PVMGeometry PVMGeneralGeometry PVMExplorationSchedule
open SequentialRidgeController
open P2Adaptive (pureParameter physicalController trueFrame trueFrame_unitary trueFrame_projector)
open scoped BigOperators Topology ComplexOrder
noncomputable section
variable [PVMExplorationSchedule.Schedule]

abbrev PVMOutcome (d : ℕ) [PVMGeneralGeometry.ExplorationLibrary d] := PVMGeneralExploration.Outcome d

def adaptiveProtocol (d : ℕ) [PVMGeneralGeometry.ExplorationLibrary d] (batchSize : ℕ → ℕ) :
    PredictableAdaptiveProtocol (PhysicalParameter (d+1)) (ℕ × Action d) (PVMOutcome d) :=
  ScheduledRidgeController.protocol PVMGeneralExploration.bornKernel
    PVMGeneralExploration.bornKernel_isMarkov PVMGeneralExploration.regressionFrame
    (fun _ => PVMGeneralExploration.responseVector) (physicalController d) (batchRefresh batchSize)
    1 0 zero_lt_one le_rfl regressionFrame_nonnegative

def actualState (d : ℕ) [PVMGeneralGeometry.ExplorationLibrary d] (batchSize : ℕ → ℕ)
    (path : AdaptiveInfinitePath (PVMOutcome d)) (n : ℕ) :
    State (HermitianSpace (d+1)) (Action d) 1 :=
  ScheduledRidgeController.pathState PVMGeneralExploration.regressionFrame
    (fun _ => PVMGeneralExploration.responseVector) (physicalController d) (batchRefresh batchSize)
    1 0 zero_lt_one le_rfl regressionFrame_nonnegative path n

def rawEstimator (d : ℕ) [PVMGeneralGeometry.ExplorationLibrary d] (batchSize : ℕ → ℕ)
    (path : AdaptiveInfinitePath (PVMOutcome d)) (n : ℕ) : HermitianSpace (d+1) :=
  (actualState d batchSize path n).estimate zero_lt_one

def stateEstimator (d : ℕ) [PVMGeneralGeometry.ExplorationLibrary d] (batchSize : ℕ → ℕ)
    (path : AdaptiveInfinitePath (PVMOutcome d)) (n : ℕ) : Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  projectedMatrix d (toMatrix (rawEstimator d batchSize path n))

theorem stateEstimator_physical (d : ℕ) [PVMGeneralGeometry.ExplorationLibrary d] (batchSize : ℕ → ℕ)
    (path : AdaptiveInfinitePath (PVMOutcome d)) (n : ℕ) :
    (stateEstimator d batchSize path n).PosSemidef ∧
    Matrix.trace (stateEstimator d batchSize path n) = 1 ∧
    stateEstimator d batchSize path n * stateEstimator d batchSize path n = stateEstimator d batchSize path n :=
  ⟨projectedMatrix_posSemidef d _, projectedMatrix_trace d _, projectedMatrix_idempotent d _⟩

def measurementFrame (d : ℕ) [PVMGeneralGeometry.ExplorationLibrary d] (batchSize : ℕ → ℕ)
    (path : AdaptiveInfinitePath (PVMOutcome d)) (n : ℕ) : Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  (actualState d batchSize path n).action.matrix
lemma measurementFrame_unitary (d : ℕ) [PVMGeneralGeometry.ExplorationLibrary d] (batchSize : ℕ → ℕ)
    (path : AdaptiveInfinitePath (PVMOutcome d)) (n : ℕ) :
    measurementFrame d batchSize path n ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ :=
  (actualState d batchSize path n).action.unitary
lemma measurementFrame_eq_frozenController (d : ℕ) [PVMGeneralGeometry.ExplorationLibrary d] (batchSize : ℕ → ℕ)
    (path : AdaptiveInfinitePath (PVMOutcome d)) (n : ℕ) :
    measurementFrame d batchSize path n =
      hermitianController d (rawEstimator d batchSize path (lastRefresh (batchRefresh batchSize) n)) := by
  have h := ScheduledRidgeController.pathState_action_eq_lastRefresh
    PVMGeneralExploration.regressionFrame (fun _ => PVMGeneralExploration.responseVector)
    (physicalController d) (batchRefresh batchSize) 1 0 zero_lt_one le_rfl
    regressionFrame_nonnegative path n
  exact congrArg Action.matrix h

/-- No state-consistency or stochastic-excitation premise is supplied. -/
theorem rawEstimator_consistent (d : ℕ) [PVMGeneralGeometry.ExplorationLibrary d] (batchSize : ℕ → ℕ) (theta : PhysicalParameter (d+1)) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol d batchSize) theta,
      Tendsto (rawEstimator d batchSize path) atTop (𝓝 theta.1) := by
  exact scheduled_estimate_consistent PVMGeneralExploration.bornKernel PVMGeneralExploration.bornKernel_isMarkov
    theta PVMGeneralExploration.regressionFrame (fun _ => PVMGeneralExploration.responseVector) theta.1
    (physicalController d) (batchRefresh batchSize) (PVMGeneralExploration.coercivityConstant d)
    (PVMGeneralExploration.coercivityConstant_pos d) regressionFrame_nonnegative regressionFrame_coercive
    (fun n a => PVMGeneralExploration.responseVector_mean theta (n,a))
    (2 * basisBound d) (mul_nonneg (by norm_num) (basisBound_nonnegative d))
    (fun n a y => PVMGeneralExploration.responseInnovation_bound theta (n,a) y)

def explorationFisher {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d] (T : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    Matrix (TangentIndex d) (TangentIndex d) ℝ :=
  (Fintype.card (PVMGeneralGeometry.ExplorationIndex d):ℝ)⁻¹ • ∑ l : PVMGeneralGeometry.ExplorationIndex d,
    fixedChartBasisFisher (T.conjTranspose * (PVMGeneralGeometry.explorationBasis l).matrix)

/-- Mean information of the recorded randomized basis setting. The subsequent
Born-identification module checks the kernel probabilities and derivatives. -/
def mixtureFisher {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d] (T U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (n : ℕ) :
    Matrix (TangentIndex d) (TangentIndex d) ℝ :=
  (1-epsilon n) • rankOneStageInformation (canonicalOracleFrame d) (T.conjTranspose * U) +
    epsilon n • explorationFisher T

def designFisher (d : ℕ) [PVMGeneralGeometry.ExplorationLibrary d] (batchSize : ℕ → ℕ) (truth : PureVector d)
    (path : AdaptiveInfinitePath (PVMOutcome d)) (n : ℕ) : Matrix (TangentIndex d) (TangentIndex d) ℝ :=
  mixtureFisher (trueFrame d truth) (measurementFrame d batchSize path n) n

/-- Every D=d+1>=2, arbitrary positive batches, and the actual PVM path law. -/
theorem pureState_PVM_consistency_and_information
    (d : ℕ) [PVMGeneralGeometry.ExplorationLibrary d] (_hd : 0 < d) (truth : PureVector d)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol d batchSize) (pureParameter d truth),
      Tendsto (rawEstimator d batchSize path) atTop (𝓝 (pureParameter d truth).1) ∧
      Tendsto (stateEstimator d batchSize path) atTop (𝓝 (rankOneDensity truth.val)) ∧
      Tendsto (designFisher d batchSize truth path) atTop
        (𝓝 ((1/2:ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) ∧
      (∀ x y : TangentIndex d, Tendsto (fun N : ℕ => (N:ℝ)⁻¹ *
        ∑ n ∈ Finset.range N, designFisher d batchSize truth path n x y) atTop
        (𝓝 (((1/2:ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)) x y))) := by
  filter_upwards [rawEstimator_consistent d batchSize (pureParameter d truth)] with path hraw
  have hrawMatrix : Tendsto (fun n => toMatrix (rawEstimator d batchSize path n))
      atTop (𝓝 (rankOneDensity truth.val)) :=
    (toMatrix_continuous (d+1)).continuousAt.tendsto.comp hraw
  have hstate : Tendsto (stateEstimator d batchSize path) atTop (𝓝 (rankOneDensity truth.val)) :=
    projectedMatrix_tendsto d truth _ hrawMatrix
  have hfrozen := consistent_estimate_at_batch_refresh
    (rawEstimator d batchSize path) (pureParameter d truth).1 hraw batchSize hpositive
  have hprojector : Tendsto (fun n => frameProjector (measurementFrame d batchSize path n))
      atTop (𝓝 (frameProjector (trueFrame d truth))) := by
    rw [trueFrame_projector]
    simp only [measurementFrame_eq_frozenController, frameProjector]
    exact hermitianController_firstProjector_tendsto d truth (pureParameter d truth).1 rfl _ hfrozen
  have hoverlap := relative_overlap_tendsto (trueFrame d truth) (trueFrame_unitary d truth)
    (measurementFrame d batchSize path) hprojector
  have hstage := rankOneStageInformation_tendsto (canonicalOracleFrame d)
    (fun n => (trueFrame d truth).conjTranspose * measurementFrame d batchSize path n)
    (fun n => relative_unitary _ _ (trueFrame_unitary d truth) (measurementFrame_unitary d batchSize path n))
    hoverlap
  have hinfo : Tendsto (designFisher d batchSize truth path) atTop
      (𝓝 ((1/2:ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) := by
    have hh := (((show Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) from tendsto_const_nhds).sub epsilon_tendsto_zero).smul hstage).add
      (epsilon_tendsto_zero.smul_const (explorationFisher (trueFrame d truth)))
    unfold designFisher mixtureFisher
    simpa only [sub_zero, one_smul, zero_smul, add_zero] using hh
  exact ⟨hraw, hstate, hinfo, fun x y =>
    (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hinfo x) y).cesaro_smul⟩

theorem pureState_PVM_completedBatches
    (d : ℕ) [PVMGeneralGeometry.ExplorationLibrary d] (hd : 0 < d) (truth : PureVector d)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol d batchSize) (pureParameter d truth),
      Tendsto (fun J => stateEstimator d batchSize path (batchBoundary batchSize J))
        atTop (𝓝 (rankOneDensity truth.val)) ∧
      Tendsto (fun J => designFisher d batchSize truth path (batchBoundary batchSize J)) atTop
        (𝓝 ((1/2:ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) ∧
      (∀ x y : TangentIndex d, Tendsto (fun J : ℕ => (batchBoundary batchSize J:ℝ)⁻¹ *
        ∑ n ∈ Finset.range (batchBoundary batchSize J), designFisher d batchSize truth path n x y) atTop
        (𝓝 (((1/2:ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)) x y))) := by
  have hb : Tendsto (batchBoundary batchSize) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with J hJ
    exact hJ.trans (le_batchBoundary batchSize hpositive J)
  filter_upwards [pureState_PVM_consistency_and_information d hd truth batchSize hpositive] with path hp
  exact ⟨hp.2.1.comp hb, hp.2.2.1.comp hb, fun x y => (hp.2.2.2 x y).comp hb⟩
end
end QubitOracle.AdaptiveDesign.PVMGeneralAdaptive

-/
