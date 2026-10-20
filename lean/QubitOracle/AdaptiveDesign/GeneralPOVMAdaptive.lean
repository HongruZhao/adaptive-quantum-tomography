import QubitOracle.AdaptiveDesign.GeneralPOVMTransport

/-! # Adaptive tomography with any finite identifying reference POVM
The protocol takes the apparatus, its deterministic identification proof,
a positive ridge constant, and batch sizes. It never takes the true state.
-/
namespace QubitOracle.AdaptiveDesign.GeneralPOVM
open Filter MeasureTheory ProbabilityTheory QubitOracle QubitOracle.Paper
open GlobalPFSICHermitian PureMatrixController SequentialRidgeController
open GlobalPFSIC (frameProjector)
open GlobalPFSICBorn (Action)
open P2Adaptive (pureParameter physicalController trueFrame trueFrame_unitary trueFrame_projector)
open scoped BigOperators Topology ComplexOrder
noncomputable section

variable {d : ℕ} {O : Type} [Fintype O]
  [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]
  (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P)
  (regularization : ℝ) (hregularization : 0 < regularization)

def coercivityConstant : ℝ := Classical.choose (exists_uniform_regression_coercivity P hI)

theorem coercivityConstant_pos : 0 < coercivityConstant P hI :=
  (Classical.choose_spec (exists_uniform_regression_coercivity P hI)).1

theorem regressionFrame_coercive (U : Action d) :
    CoerciveLeastSquares.Coercive (regressionFrame P U) (coercivityConstant P hI) :=
  (Classical.choose_spec (exists_uniform_regression_coercivity P hI)).2 U

def adaptiveProtocol (batchSize : ℕ → ℕ) :
    PredictableAdaptiveProtocol (PureVector d) (Action d) O :=
  protocol (bornKernel P) (fun theta => bornKernel_isMarkov P theta)
    (regressionFrame P) (responseVector P) (physicalController d) (batchRefresh batchSize)
    regularization (coercivityConstant P hI) hregularization (coercivityConstant_pos P hI).le
    (regressionFrame_coercive P hI)

def actualState (batchSize : ℕ → ℕ) (path : AdaptiveInfinitePath O) (n : ℕ) :
    State (HermitianSpace (d+1)) (Action d) regularization :=
  pathState (regressionFrame P) (responseVector P) (physicalController d) (batchRefresh batchSize)
    regularization (coercivityConstant P hI) hregularization (coercivityConstant_pos P hI).le
    (regressionFrame_coercive P hI) path n

def rawEstimator (batchSize : ℕ → ℕ) (path : AdaptiveInfinitePath O) (n : ℕ) :
    HermitianSpace (d+1) :=
  (actualState P hI regularization hregularization batchSize path n).estimate hregularization

def stateEstimator (batchSize : ℕ → ℕ) (path : AdaptiveInfinitePath O) (n : ℕ) :
    Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  projectedMatrix d (toMatrix (rawEstimator P hI regularization hregularization batchSize path n))

theorem stateEstimator_physical (batchSize : ℕ → ℕ) (path : AdaptiveInfinitePath O) (n : ℕ) :
    (stateEstimator P hI regularization hregularization batchSize path n).PosSemidef ∧
    Matrix.trace (stateEstimator P hI regularization hregularization batchSize path n) = 1 ∧
    stateEstimator P hI regularization hregularization batchSize path n *
      stateEstimator P hI regularization hregularization batchSize path n =
      stateEstimator P hI regularization hregularization batchSize path n :=
  ⟨projectedMatrix_posSemidef d _, projectedMatrix_trace d _, projectedMatrix_idempotent d _⟩

def measurementFrame (batchSize : ℕ → ℕ) (path : AdaptiveInfinitePath O) (n : ℕ) :
    Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  (actualState P hI regularization hregularization batchSize path n).action.matrix

theorem measurementFrame_unitary (batchSize : ℕ → ℕ) (path : AdaptiveInfinitePath O) (n : ℕ) :
    measurementFrame P hI regularization hregularization batchSize path n ∈
      Matrix.unitaryGroup (Fin (d+1)) ℂ :=
  (actualState P hI regularization hregularization batchSize path n).action.unitary

theorem measurementFrame_eq_frozenController (batchSize : ℕ → ℕ)
    (path : AdaptiveInfinitePath O) (n : ℕ) :
    measurementFrame P hI regularization hregularization batchSize path n =
      hermitianController d (rawEstimator P hI regularization hregularization batchSize path
        (lastRefresh (batchRefresh batchSize) n)) := by
  have h := pathState_action_eq_lastRefresh
    (regressionFrame P) (responseVector P) (physicalController d) (batchRefresh batchSize)
    regularization (coercivityConstant P hI) hregularization (coercivityConstant_pos P hI).le
    (regressionFrame_coercive P hI) path n
  exact congrArg Action.matrix h

/-- C1 alone, with no local regularity or Fisher hypothesis. -/
theorem rawEstimator_consistent (batchSize : ℕ → ℕ) (truth : PureVector d) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure
      (adaptiveProtocol P hI regularization hregularization batchSize) truth,
      Tendsto (rawEstimator P hI regularization hregularization batchSize path) atTop
        (𝓝 (pureParameter d truth).1) := by
  exact pathState_estimate_tendsto_ae
    (bornKernel P) (fun theta => bornKernel_isMarkov P theta)
    truth (regressionFrame P) (responseVector P) (pureParameter d truth).1
    (physicalController d) (batchRefresh batchSize)
    regularization (coercivityConstant P hI) hregularization (coercivityConstant_pos P hI)
    (regressionFrame_coercive P hI) (responseVector_mean P truth)
    (2 * responseBound P) (mul_nonneg (by norm_num) (responseBound_nonnegative P))
    (responseInnovation_bound P truth)

/-- The arbitrary finite POVM's normalized-chart information at the true ray. -/
def designFisher (batchSize : ℕ → ℕ) (truth : PureVector d)
    (path : AdaptiveInfinitePath O) (n : ℕ) : Matrix (TangentIndex d) (TangentIndex d) ℝ :=
  fisher P ((trueFrame d truth).conjTranspose *
    measurementFrame P hI regularization hregularization batchSize path n)

/-- C1 alone proves both estimator consistency and consistency of the
batch-frozen controller ray, for arbitrary positive finite batches. -/
theorem adaptive_consistency (truth : PureVector d)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure
      (adaptiveProtocol P hI regularization hregularization batchSize) truth,
      Tendsto (rawEstimator P hI regularization hregularization batchSize path) atTop
        (𝓝 (pureParameter d truth).1) ∧
      Tendsto (stateEstimator P hI regularization hregularization batchSize path) atTop
        (𝓝 (rankOneDensity truth.val)) ∧
      Tendsto (fun n => frameProjector
        (measurementFrame P hI regularization hregularization batchSize path n)) atTop
        (𝓝 (rankOneDensity truth.val)) := by
  filter_upwards [rawEstimator_consistent P hI regularization hregularization batchSize truth]
    with path hraw
  have hrawMatrix : Tendsto
      (fun n => toMatrix (rawEstimator P hI regularization hregularization batchSize path n))
      atTop (𝓝 (rankOneDensity truth.val)) :=
    (toMatrix_continuous (d+1)).continuousAt.tendsto.comp hraw
  have hstate := projectedMatrix_tendsto d truth _ hrawMatrix
  have hfrozen := consistent_estimate_at_batch_refresh
    (rawEstimator P hI regularization hregularization batchSize path)
    (pureParameter d truth).1 hraw batchSize hpositive
  refine ⟨hraw, hstate, ?_⟩
  simp only [measurementFrame_eq_frozenController, frameProjector]
  exact hermitianController_firstProjector_tendsto d truth (pureParameter d truth).1 rfl _ hfrozen

/-- C2 and C3 add optimal-information convergence. None of the input
conditions assumes estimator consistency, information convergence, or a
continuous choice of eigenvector, phase, or unitary complement. -/
theorem adaptive_consistency_and_information (hp : Regular P) (hF : FisherSymmetric P)
    (truth : PureVector d) (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure
      (adaptiveProtocol P hI regularization hregularization batchSize) truth,
      Tendsto (rawEstimator P hI regularization hregularization batchSize path) atTop
        (𝓝 (pureParameter d truth).1) ∧
      Tendsto (stateEstimator P hI regularization hregularization batchSize path) atTop
        (𝓝 (rankOneDensity truth.val)) ∧
      Tendsto (designFisher P hI regularization hregularization batchSize truth path) atTop
        (𝓝 ((1/2 : ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) ∧
      (∀ x y : TangentIndex d,
        Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
          designFisher P hI regularization hregularization batchSize truth path n x y) atTop
          (𝓝 (((1/2 : ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)) x y))) := by
  filter_upwards [adaptive_consistency P hI regularization hregularization truth batchSize hpositive]
    with path hpath
  have hproj : Tendsto (fun n => frameProjector
      (measurementFrame P hI regularization hregularization batchSize path n)) atTop
      (𝓝 (frameProjector (trueFrame d truth))) := by
    rw [trueFrame_projector]
    exact hpath.2.2
  have hinfo := fisher_generalTruth_tendsto P hp hF (trueFrame d truth)
    (trueFrame_unitary d truth)
    (measurementFrame P hI regularization hregularization batchSize path)
    (measurementFrame_unitary P hI regularization hregularization batchSize path) hproj
  refine ⟨hpath.1, hpath.2.1, hinfo, ?_⟩
  intro x y
  exact (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hinfo x) y).cesaro_smul

theorem adaptive_completedBatches (hp : Regular P) (hF : FisherSymmetric P)
    (truth : PureVector d) (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure
      (adaptiveProtocol P hI regularization hregularization batchSize) truth,
      Tendsto (fun J => stateEstimator P hI regularization hregularization batchSize path
        (batchBoundary batchSize J)) atTop (𝓝 (rankOneDensity truth.val)) ∧
      Tendsto (fun J => designFisher P hI regularization hregularization batchSize truth path
        (batchBoundary batchSize J)) atTop
        (𝓝 ((1/2 : ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) ∧
      (∀ x y : TangentIndex d, Tendsto (fun J : ℕ =>
        ((batchBoundary batchSize J : ℕ) : ℝ)⁻¹ *
          ∑ n ∈ Finset.range (batchBoundary batchSize J),
            designFisher P hI regularization hregularization batchSize truth path n x y) atTop
        (𝓝 (((1/2 : ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)) x y))) := by
  have hb : Tendsto (batchBoundary batchSize) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with J hJ
    exact hJ.trans (le_batchBoundary batchSize hpositive J)
  filter_upwards [adaptive_consistency_and_information P hI regularization hregularization
    hp hF truth batchSize hpositive] with path hpath
  exact ⟨hpath.2.1.comp hb, hpath.2.2.1.comp hb, fun x y => (hpath.2.2.2 x y).comp hb⟩

end
end QubitOracle.AdaptiveDesign.GeneralPOVM
