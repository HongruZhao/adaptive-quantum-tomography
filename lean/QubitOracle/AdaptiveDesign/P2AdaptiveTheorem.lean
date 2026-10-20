import QubitOracle.AdaptiveDesign.GlobalPFSICBornModel
import QubitOracle.AdaptiveDesign.PureHermitianController
import QubitOracle.AdaptiveDesign.RidgeBatchSchedule

/-!
# P2: the complete implemented pure-state adaptive first theorem

In every complex Hilbert dimension `d+1 >= 2`, a concrete globally identifying
finite POVM supplies an all-observation ridge controller. Its nearest-pure
projection is consistent under the actual adaptive Born law. Arbitrary positive
predetermined batches freeze the measurement between updates. The physical
Fisher information, evaluated in any fixed true frame, converges to half QFI.

No stochastic consistency, excitation, local Fisher continuity, or external
statistical theorem is supplied as a premise of the final endpoint.
-/

namespace QubitOracle.AdaptiveDesign.P2Adaptive

open Filter MeasureTheory ProbabilityTheory QubitOracle.Paper
open GlobalPFSIC GlobalPFSICHermitian GlobalPFSICBorn PureMatrixController
open SequentialRidgeController
open scoped BigOperators Topology ComplexOrder

noncomputable section

def pureParameter (d : ℕ) (truth : PureVector d) : PhysicalParameter (d+1) :=
  ⟨ofMatrix (rankOneDensity truth.val) (projector_posSemidef truth.val).isHermitian,
    projector_posSemidef truth.val,
    rankOneDensity_trace_eq_one truth.val truth.property⟩

def coercivityConstant {d : ℕ} (hd : 0 < d) : ℝ :=
  Classical.choose (exists_uniform_regression_coercivity hd)

theorem coercivityConstant_pos {d : ℕ} (hd : 0 < d) : 0 < coercivityConstant hd :=
  (Classical.choose_spec (exists_uniform_regression_coercivity hd)).1

theorem regressionFrame_coercive {d : ℕ} (hd : 0 < d) (U : Action d) :
    CoerciveLeastSquares.Coercive (regressionFrame hd U) (coercivityConstant hd) :=
  (Classical.choose_spec (exists_uniform_regression_coercivity hd)).2 U

/-- A fully specified nearest-pure controller; its only default is the known
computational reference used by `hermitianController`. -/
def physicalController (d : ℕ) (raw : HermitianSpace (d+1)) : Action d :=
  ⟨hermitianController d raw, hermitianController_unitary d raw⟩

/-- Ridge one, actual one-hot response, and refresh only at cumulative batch
boundaries. The protocol definition itself takes no unknown state. -/
def adaptiveProtocol {d : ℕ} (hd : 0 < d) (batchSize : ℕ → ℕ) :
    PredictableAdaptiveProtocol (PhysicalParameter (d+1)) (Action d) (Outcome d) :=
  protocol (bornKernel hd) (fun theta => bornKernel_isMarkov hd theta)
    (regressionFrame hd) (responseVector hd) (physicalController d) (batchRefresh batchSize)
    1 (coercivityConstant hd) zero_lt_one (coercivityConstant_pos hd).le
    (regressionFrame_coercive hd)

def actualState {d : ℕ} (hd : 0 < d) (batchSize : ℕ → ℕ)
    (path : AdaptiveInfinitePath (Outcome d)) (n : ℕ) :
    State (HermitianSpace (d+1)) (Action d) 1 :=
  pathState (regressionFrame hd) (responseVector hd) (physicalController d) (batchRefresh batchSize)
    1 (coercivityConstant hd) zero_lt_one (coercivityConstant_pos hd).le
    (regressionFrame_coercive hd) path n

def rawEstimator {d : ℕ} (hd : 0 < d) (batchSize : ℕ → ℕ)
    (path : AdaptiveInfinitePath (Outcome d)) (n : ℕ) : HermitianSpace (d+1) :=
  (actualState hd batchSize path n).estimate zero_lt_one

def stateEstimator {d : ℕ} (hd : 0 < d) (batchSize : ℕ → ℕ)
    (path : AdaptiveInfinitePath (Outcome d)) (n : ℕ) :
    Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  projectedMatrix d (toMatrix (rawEstimator hd batchSize path n))

theorem stateEstimator_physical {d : ℕ} (hd : 0 < d) (batchSize : ℕ → ℕ)
    (path : AdaptiveInfinitePath (Outcome d)) (n : ℕ) :
    (stateEstimator hd batchSize path n).PosSemidef ∧
    Matrix.trace (stateEstimator hd batchSize path n) = 1 ∧
    stateEstimator hd batchSize path n * stateEstimator hd batchSize path n =
      stateEstimator hd batchSize path n := by
  exact ⟨projectedMatrix_posSemidef d _, projectedMatrix_trace d _,
    projectedMatrix_idempotent d _⟩

def measurementFrame {d : ℕ} (hd : 0 < d) (batchSize : ℕ → ℕ)
    (path : AdaptiveInfinitePath (Outcome d)) (n : ℕ) :
    Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  (actualState hd batchSize path n).action.matrix

theorem measurementFrame_unitary {d : ℕ} (hd : 0 < d) (batchSize : ℕ → ℕ)
    (path : AdaptiveInfinitePath (Outcome d)) (n : ℕ) :
    measurementFrame hd batchSize path n ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ :=
  (actualState hd batchSize path n).action.unitary

theorem measurementFrame_eq_frozenController {d : ℕ} (hd : 0 < d) (batchSize : ℕ → ℕ)
    (path : AdaptiveInfinitePath (Outcome d)) (n : ℕ) :
    measurementFrame hd batchSize path n =
      hermitianController d (rawEstimator hd batchSize path (lastRefresh (batchRefresh batchSize) n)) := by
  have h := pathState_action_eq_lastRefresh
    (regressionFrame hd) (responseVector hd) (physicalController d) (batchRefresh batchSize)
    1 (coercivityConstant hd) zero_lt_one (coercivityConstant_pos hd).le
    (regressionFrame_coercive hd) path n
  exact congrArg Action.matrix h

/-- The all-observation ridge estimate is strongly consistent under this
literal physical protocol, even before using the pure-state assumption. -/
theorem rawEstimator_consistent {d : ℕ} (hd : 0 < d) (batchSize : ℕ → ℕ)
    (theta : PhysicalParameter (d+1)) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol hd batchSize) theta,
      Tendsto (rawEstimator hd batchSize path) atTop (𝓝 theta.1) := by
  letI : Nonempty (Outcome d) := ⟨(false,0,Sum.inl ⟨0,hd⟩)⟩
  exact pathState_estimate_tendsto_ae
    (bornKernel hd) (fun theta => bornKernel_isMarkov hd theta)
    theta (regressionFrame hd) (responseVector hd) theta.1
    (physicalController d) (batchRefresh batchSize)
    1 (coercivityConstant hd) zero_lt_one (coercivityConstant_pos hd)
    (regressionFrame_coercive hd) (responseVector_mean hd theta)
    (2 * responseBound hd) (mul_nonneg (by norm_num) (responseBound_nonnegative hd))
    (responseInnovation_bound hd theta)

/-- A fixed true frame is used for analysis only. It is never passed to the
measurement policy or estimator. -/
def trueFrame (d : ℕ) (truth : PureVector d) : Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  Classical.choose (exists_unitary_firstColumn truth)

theorem trueFrame_unitary (d : ℕ) (truth : PureVector d) :
    trueFrame d truth ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ :=
  (Classical.choose_spec (exists_unitary_firstColumn truth)).1

theorem trueFrame_projector (d : ℕ) (truth : PureVector d) :
    frameProjector (trueFrame d truth) = rankOneDensity truth.val := by
  rw [frameProjector, trueFrame, (Classical.choose_spec (exists_unitary_firstColumn truth)).2]
  rfl

/-- Physical Fisher information of the actual frozen POVM, expressed in a
fixed QFI-normalized tangent chart of the unknown true state. -/
def designFisher {d : ℕ} (hd : 0 < d) (batchSize : ℕ → ℕ) (truth : PureVector d)
    (path : AdaptiveInfinitePath (Outcome d)) (n : ℕ) :
    Matrix (QubitOracle.TangentIndex d) (QubitOracle.TangentIndex d) ℝ :=
  transportedFisher ((trueFrame d truth).conjTranspose * measurementFrame hd batchSize path n)

/-- P2, in every finite complex dimension and for arbitrary positive batch
sizes: raw and projected-estimator consistency, convergence of the actual
next-shot design, and convergence of its accumulated information. -/
theorem pureState_adaptive_consistency_and_information
    (d : ℕ) (hd : 0 < d) (truth : PureVector d)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol hd batchSize) (pureParameter d truth),
      Tendsto (rawEstimator hd batchSize path) atTop (𝓝 (pureParameter d truth).1) ∧
      Tendsto (stateEstimator hd batchSize path) atTop (𝓝 (rankOneDensity truth.val)) ∧
      Tendsto (designFisher hd batchSize truth path) atTop
        (𝓝 ((1/2 : ℝ) • (1 : Matrix (QubitOracle.TangentIndex d) (QubitOracle.TangentIndex d) ℝ))) ∧
      (∀ x y : QubitOracle.TangentIndex d,
        Tendsto (fun N : ℕ => (N : ℝ)⁻¹ *
          ∑ n ∈ Finset.range N, designFisher hd batchSize truth path n x y)
          atTop (𝓝 (((1/2 : ℝ) •
            (1 : Matrix (QubitOracle.TangentIndex d) (QubitOracle.TangentIndex d) ℝ)) x y))) := by
  filter_upwards [rawEstimator_consistent hd batchSize (pureParameter d truth)] with path hraw
  have hrawMatrix : Tendsto (fun n => toMatrix (rawEstimator hd batchSize path n))
      atTop (𝓝 (rankOneDensity truth.val)) := by
    exact (toMatrix_continuous (d+1)).continuousAt.tendsto.comp hraw
  have hstate : Tendsto (stateEstimator hd batchSize path) atTop (𝓝 (rankOneDensity truth.val)) :=
    projectedMatrix_tendsto d truth _ hrawMatrix
  have hfrozen := consistent_estimate_at_batch_refresh
    (rawEstimator hd batchSize path) (pureParameter d truth).1 hraw batchSize hpositive
  have hprojector : Tendsto (fun n => frameProjector (measurementFrame hd batchSize path n))
      atTop (𝓝 (frameProjector (trueFrame d truth))) := by
    rw [trueFrame_projector]
    simp only [measurementFrame_eq_frozenController, frameProjector]
    exact hermitianController_firstProjector_tendsto d truth (pureParameter d truth).1 rfl
      _ hfrozen
  have hinformation : Tendsto (designFisher hd batchSize truth path) atTop
      (𝓝 ((1/2 : ℝ) • (1 : Matrix (QubitOracle.TangentIndex d) (QubitOracle.TangentIndex d) ℝ))) :=
    transportedFisher_generalTruth_tendsto hd (trueFrame d truth) (trueFrame_unitary d truth)
      (measurementFrame hd batchSize path) (measurementFrame_unitary hd batchSize path) hprojector
  refine ⟨hraw, hstate, hinformation, ?_⟩
  intro x y
  exact (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hinformation x) y).cesaro_smul

/-- The requested `m_1,m_2,...` conclusion at literal completed batch
horizons, including `m_j=1`. This is a consequence of a genuinely frozen
batch protocol, not a relabeling of an estimator updated shot by shot. -/
theorem pureState_adaptive_completedBatches
    (d : ℕ) (hd : 0 < d) (truth : PureVector d)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol hd batchSize) (pureParameter d truth),
      Tendsto (fun J => stateEstimator hd batchSize path (batchBoundary batchSize J))
        atTop (𝓝 (rankOneDensity truth.val)) ∧
      Tendsto (fun J => designFisher hd batchSize truth path (batchBoundary batchSize J)) atTop
        (𝓝 ((1/2 : ℝ) • (1 : Matrix (QubitOracle.TangentIndex d) (QubitOracle.TangentIndex d) ℝ))) ∧
      (∀ x y : QubitOracle.TangentIndex d,
        Tendsto (fun J : ℕ => ((batchBoundary batchSize J : ℕ) : ℝ)⁻¹ *
          ∑ n ∈ Finset.range (batchBoundary batchSize J), designFisher hd batchSize truth path n x y)
          atTop (𝓝 (((1/2 : ℝ) •
            (1 : Matrix (QubitOracle.TangentIndex d) (QubitOracle.TangentIndex d) ℝ)) x y))) := by
  have hboundary : Tendsto (batchBoundary batchSize) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with J hJ
    exact hJ.trans (le_batchBoundary batchSize hpositive J)
  filter_upwards [pureState_adaptive_consistency_and_information d hd truth batchSize hpositive]
    with path hpath
  exact ⟨hpath.2.1.comp hboundary, hpath.2.2.1.comp hboundary,
    fun x y => (hpath.2.2.2 x y).comp hboundary⟩

end

end QubitOracle.AdaptiveDesign.P2Adaptive
