import QubitOracle.Paper.PureMultilevelProjectedRLSInformationConvergence
import QubitOracle.Paper.PureMultilevelPFSICLossOptimalMinimax
import QubitOracle.Paper.ConcreteSafeguardedOneStep

/-!
# Sequential batched adaptive PFSIC tomography

This module replaces a frozen two-stage allocation by a genuinely sequential
batch design.  Batch `i` contains `m_i` observations.  A predictable projected
RLS controller is updated between batches, a vanishing fraction of each batch
is reserved for globally identifying exploration, and the remaining
observations use a PFSIC measurement centred at the current controller state.

No polynomial allocation is built into the definitions.  The exact rate
condition is expressed through cumulative sample and exploration counts.  The
deterministic weighted-Cesaro theorem below proves that arbitrary positive
batch sizes preserve the PFSIC information limit.

The final theorem combines this information result with the existing
martingale-LAN and concrete safeguarded one-step interfaces.  Its analytic
hypotheses are explicit: Hall--Heyde conditions, the finite likelihood
remainder, covariance identification, capped-risk convergence, and a uniform
fourth-moment bound.  No new scientific axiom is introduced here.
-/

namespace QubitOracle.Paper
namespace PureMultilevelSequentialBatchAdaptive

open Filter MeasureTheory Asymptotics
open scoped BigOperators Topology ENNReal

noncomputable section

open PureMultilevelProjectedRLSInformationConvergence
open PureMultilevelPFSICLossOptimalMinimax

/-! ## Arbitrary batch and exploration schedules -/

/-- Cumulative count before batch index `n`. -/
def cumulativeCount (count : Nat -> Nat) (n : Nat) : Nat :=
  ∑ i ∈ Finset.range n, count i

/-- A general deterministic sequential exploration budget. -/
structure SequentialExplorationBudget where
  /-- Total number of observations in batch `i`. -/
  batchSize : Nat -> Nat
  /-- Number of globally identifying exploration observations in batch `i`. -/
  explorationSize : Nat -> Nat
  batchSize_pos : forall i, 0 < batchSize i
  exploration_le_batch : forall i, explorationSize i <= batchSize i
  /-- The experiment contains infinitely many observations. -/
  totalSamples_tendsto_atTop :
    Tendsto (fun n => (cumulativeCount batchSize n : Real)) atTop atTop
  /-- Exploration is negligible within late batches. -/
  stageExploration_tendsto_zero :
    Tendsto
      (fun i => (explorationSize i : Real) / (batchSize i : Real))
      atTop (nhds 0)
  /-- The APS/RLS confidence scale is `o(T_n^(-1/4))`.

  In fixed dimension the self-normalized RLS radius is of order
  `sqrt(log T_n / E_n)`.  The displayed condition is exactly what makes its
  product with `T_n^(1/4)` vanish. -/
  quarterRateExploration :
    Tendsto
      (fun n =>
        Real.sqrt (cumulativeCount batchSize n : Real) *
            Real.log ((cumulativeCount batchSize n : Real) + 2) /
          (cumulativeCount explorationSize n : Real))
      atTop (nhds 0)

/-- Per-batch exploration fraction. -/
def SequentialExplorationBudget.explorationFraction
    (budget : SequentialExplorationBudget) (i : Nat) : Real :=
  (budget.explorationSize i : Real) / (budget.batchSize i : Real)

theorem SequentialExplorationBudget.explorationFraction_nonnegative
    (budget : SequentialExplorationBudget) (i : Nat) :
    0 <= budget.explorationFraction i := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem SequentialExplorationBudget.explorationFraction_le_one
    (budget : SequentialExplorationBudget) (i : Nat) :
    budget.explorationFraction i <= 1 := by
  apply (div_le_one (Nat.cast_pos.mpr (budget.batchSize_pos i))).2
  exact_mod_cast budget.exploration_le_batch i

theorem SequentialExplorationBudget.explorationFraction_tendsto_zero
    (budget : SequentialExplorationBudget) :
    Tendsto budget.explorationFraction atTop (nhds 0) := by
  exact budget.stageExploration_tendsto_zero

/-! ## Weighted Cesaro convergence for arbitrary batch sizes -/

/-- Scalar average in which the value from batch `i` is repeated
`weight i` times. -/
def weightedScalarAverage
    (weight : Nat -> Real) (value : Nat -> Real) (n : Nat) : Real :=
  (∑ i ∈ Finset.range n, weight i)⁻¹ *
    ∑ i ∈ Finset.range n, weight i * value i

/-- Toeplitz/weighted-Cesaro lemma for nonnegative arbitrary batch weights.
No upper bound on a single batch is required. -/
theorem weightedScalarAverage_tendsto
    (weight value : Nat -> Real) (target : Real)
    (hweight : forall i, 0 <= weight i)
    (htotal : Tendsto (fun n => ∑ i ∈ Finset.range n, weight i)
      atTop atTop)
    (hvalue : Tendsto value atTop (nhds target)) :
    Tendsto (weightedScalarAverage weight value) atTop (nhds target) := by
  have hzero : Tendsto (fun n => value n - target) atTop (nhds 0) := by
    simpa using hvalue.sub
      (tendsto_const_nhds : Tendsto (fun _ : Nat => target)
        atTop (nhds target))
  have hbase :
      (fun n => value n - target) =o[atTop] (fun _ => (1 : Real)) :=
    (isLittleO_one_iff Real).2 hzero
  have hscaled :
      (fun n => weight n * (value n - target)) =o[atTop] weight := by
    apply isLittleO_iff.2
    intro c hc
    filter_upwards [isLittleO_iff.1 hbase hc] with n hn
    have hw := hweight n
    calc
      ‖weight n * (value n - target)‖ =
          weight n * ‖value n - target‖ := by
            rw [norm_mul, Real.norm_of_nonneg hw]
      _ <= weight n * c :=
        mul_le_mul_of_nonneg_left (by simpa using hn) hw
      _ = c * ‖weight n‖ := by
        rw [Real.norm_of_nonneg hw]
        ring
  have hsum := hscaled.sum_range hweight htotal
  have hratio := hsum.tendsto_div_nhds_zero
  have hpositive :
      ∀ᶠ n in atTop, 0 < ∑ i ∈ Finset.range n, weight i :=
    htotal.eventually (eventually_gt_atTop 0)
  rw [← tendsto_sub_nhds_zero_iff]
  refine hratio.congr' ?_
  filter_upwards [hpositive] with n hn
  have hne : (∑ i ∈ Finset.range n, weight i) ≠ 0 := ne_of_gt hn
  have hsumdiff :
      (∑ i ∈ Finset.range n, weight i * (value i - target)) =
        (∑ i ∈ Finset.range n, weight i * value i) -
          (∑ i ∈ Finset.range n, weight i) * target := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  change
    (∑ i ∈ Finset.range n, weight i * (value i - target)) /
        (∑ i ∈ Finset.range n, weight i) =
      weightedScalarAverage weight value n - target
  rw [hsumdiff]
  simp only [weightedScalarAverage]
  field_simp [hne]

/-- Entrywise convergence of finite real matrices over an arbitrary fixed
coordinate type. -/
def BatchMatrixEntrywiseTendsto {D : Type*}
    (information : Nat -> Matrix D D Real) (target : Matrix D D Real) : Prop :=
  forall i j, Tendsto (fun n => information n i j) atTop (nhds (target i j))

/-- Batch-weighted average of finite real Fisher matrices. -/
def batchWeightedMatrixAverage {D : Type*}
    (batchSize : Nat -> Nat)
    (information : Nat -> Matrix D D Real) :
    Nat -> Matrix D D Real :=
  fun n i j => weightedScalarAverage
    (fun k => (batchSize k : Real)) (fun k => information k i j) n

/-- Entrywise convergence of stage information implies convergence of the
per-observation information for arbitrary positive batch sizes. -/
theorem batchWeightedMatrixAverage_tendsto
    {D : Type*}
    (batchSize : Nat -> Nat)
    (information : Nat -> Matrix D D Real)
    (target : Matrix D D Real)
    (htotal : Tendsto
      (fun n => ∑ i ∈ Finset.range n, (batchSize i : Real)) atTop atTop)
    (hinformation : BatchMatrixEntrywiseTendsto information target) :
    BatchMatrixEntrywiseTendsto
      (batchWeightedMatrixAverage batchSize information) target := by
  intro i j
  exact weightedScalarAverage_tendsto
    (fun k => (batchSize k : Real)) (fun k => information k i j)
    (target i j) (fun _ => Nat.cast_nonneg _)
    htotal (hinformation i j)

/-- Generic exploitation/exploration Fisher mixture for the pure tangent
coordinate type. -/
def sequentialPredictableFisher {D : Type*}
    (epsilon : Nat -> Real)
    (exploitation exploration : Nat -> Matrix D D Real) :
    Nat -> Matrix D D Real :=
  fun n i j =>
    (1 - epsilon n) * exploitation n i j +
      epsilon n * exploration n i j

/-- Vanishing exploration preserves a convergent exploitation Fisher matrix
when exploration information is uniformly bounded around the target. -/
theorem sequentialPredictableFisher_tendsto_of_vanishing_exploration
    {D : Type*}
    (epsilon : Nat -> Real)
    (exploitation exploration : Nat -> Matrix D D Real)
    (target : Matrix D D Real)
    (bound : D -> D -> Real)
    (hboundNonnegative : forall i j, 0 <= bound i j)
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hexploitation : BatchMatrixEntrywiseTendsto exploitation target)
    (hexplorationBound : forall n i j,
      |exploration n i j - target i j| <= bound i j) :
    BatchMatrixEntrywiseTendsto
      (sequentialPredictableFisher epsilon exploitation exploration) target := by
  intro i j
  have hcontrolZero : Tendsto
      (fun n => exploitation n i j - target i j) atTop (nhds 0) := by
    simpa using (hexploitation i j).sub
      (tendsto_const_nhds : Tendsto (fun _ : Nat => target i j)
        atTop (nhds (target i j)))
  have honeMinus : Tendsto (fun n => 1 - epsilon n) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hepsilon
  have hcontrolled : Tendsto
      (fun n => (1 - epsilon n) *
        (exploitation n i j - target i j)) atTop (nhds 0) := by
    simpa using honeMinus.mul hcontrolZero
  have hepsilonAbs : Tendsto (fun n => |epsilon n|) atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero] at hepsilon
    change Tendsto (abs ∘ epsilon) atTop (nhds 0)
    exact hepsilon
  have hexplorationZero : Tendsto
      (fun n => epsilon n * (exploration n i j - target i j))
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    have hupper : Tendsto (fun n => |epsilon n| * bound i j)
        atTop (nhds 0) := by
      simpa using hepsilonAbs.mul_const (bound i j)
    exact squeeze_zero'
      (Eventually.of_forall fun _ => abs_nonneg _)
      (Eventually.of_forall fun n => by
        change |epsilon n * (exploration n i j - target i j)| <=
          |epsilon n| * bound i j
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (hexplorationBound n i j) (abs_nonneg _))
      hupper
  have hsum := hcontrolled.add hexplorationZero
  rw [← tendsto_sub_nhds_zero_iff]
  simpa [sequentialPredictableFisher] using hsum.congr'
    (Eventually.of_forall fun n => by ring)

/-! ## Sequential projected-RLS/PFSIC information -/

/-- Data required to identify the predictable information limit of a
sequential projected-RLS/PFSIC controller.  The controller state may be a
rank-one projector, a normalized vector with deterministic phase convention,
or any equivalent fixed-dimensional representation. -/
structure SequentialBatchPFSICControllerData
    (d : Nat) (Controller : Type*) [TopologicalSpace Controller] where
  budget : SequentialExplorationBudget
  controller : Nat -> Controller
  truth : Controller
  controller_tendsto : Tendsto controller atTop (nhds truth)
  pfsicFisher : Controller ->
    Matrix (PureTangentIndex d) (PureTangentIndex d) Real
  pfsicFisher_continuous : forall i j,
    ContinuousAt (fun c => pfsicFisher c i j) truth
  pfsicFisher_truth : pfsicFisher truth = pfsicInformation d
  explorationFisher : Nat ->
    Matrix (PureTangentIndex d) (PureTangentIndex d) Real
  explorationDeviationBound :
    PureTangentIndex d -> PureTangentIndex d -> Real
  explorationDeviationBound_nonnegative : forall i j,
    0 <= explorationDeviationBound i j
  explorationFisher_bounded : forall n i j,
    |explorationFisher n i j - pfsicInformation d i j| <=
      explorationDeviationBound i j

/-- One-batch predictable Fisher matrix of the adaptive exploration/PFSIC
mixture. -/
def SequentialBatchPFSICControllerData.stageInformation
    {d : Nat} {Controller : Type*} [TopologicalSpace Controller]
    (data : SequentialBatchPFSICControllerData d Controller) :
    Nat -> Matrix (PureTangentIndex d) (PureTangentIndex d) Real :=
  sequentialPredictableFisher data.budget.explorationFraction
    (fun n => data.pfsicFisher (data.controller n))
    data.explorationFisher

/-- Per-observation predictable Fisher information through the first `n`
batches. -/
def SequentialBatchPFSICControllerData.batchInformation
    {d : Nat} {Controller : Type*} [TopologicalSpace Controller]
    (data : SequentialBatchPFSICControllerData d Controller) :
    Nat -> Matrix (PureTangentIndex d) (PureTangentIndex d) Real :=
  batchWeightedMatrixAverage data.budget.batchSize data.stageInformation

/-- Main arbitrary-batch information theorem.  Projected-controller
consistency, continuity of the transported PFSIC Fisher matrix, vanishing
exploration, and bounded exploration information imply both stagewise and
per-observation information convergence to half the pure-state QFI. -/
theorem SequentialBatchPFSICControllerData.information_tendsto
    {d : Nat} {Controller : Type*} [TopologicalSpace Controller]
    (data : SequentialBatchPFSICControllerData d Controller) :
    BatchMatrixEntrywiseTendsto data.stageInformation (pfsicInformation d) ∧
      BatchMatrixEntrywiseTendsto data.batchInformation (pfsicInformation d) := by
  have hexploitation : BatchMatrixEntrywiseTendsto
      (fun n => data.pfsicFisher (data.controller n))
      (pfsicInformation d) := by
    intro i j
    have h := (data.pfsicFisher_continuous i j).tendsto.comp
      data.controller_tendsto
    change Tendsto (fun n => data.pfsicFisher (data.controller n) i j)
      atTop (nhds (data.pfsicFisher data.truth i j)) at h
    rw [data.pfsicFisher_truth] at h
    exact h
  have hstage : BatchMatrixEntrywiseTendsto data.stageInformation
      (pfsicInformation d) :=
    sequentialPredictableFisher_tendsto_of_vanishing_exploration
      data.budget.explorationFraction
      (fun n => data.pfsicFisher (data.controller n))
      data.explorationFisher (pfsicInformation d)
      data.explorationDeviationBound
      data.explorationDeviationBound_nonnegative
      data.budget.explorationFraction_tendsto_zero
      hexploitation data.explorationFisher_bounded
  refine ⟨hstage, ?_⟩
  have htotal : Tendsto
      (fun n => ∑ i ∈ Finset.range n, (data.budget.batchSize i : Real))
      atTop atTop := by
    simpa [cumulativeCount] using data.budget.totalSamples_tendsto_atTop
  exact batchWeightedMatrixAverage_tendsto
    data.budget.batchSize data.stageInformation (pfsicInformation d)
    htotal hstage

/-! ## LAN and concrete safeguarded one-step minimax endpoint -/

/-- Fully sequential source-relative endpoint.

The policy may update after every batch and all observations enter the final
score.  `hCovariance` identifies the conditional covariance of the flattened
shotwise score array with the batch-information limit proved above.
`hRemainder`, `hCapped`, and `hFourth` are the remaining finite-likelihood and
uniform-risk obligations for the concrete model. -/
theorem sequentialAdaptivePFSIC_LAN_lowerBound_and_safeguardedAttainment
    {d : Nat} {Controller : Type*} [TopologicalSpace Controller]
    (design : SequentialBatchPFSICControllerData d Controller)
    {Omega : Type} [MeasurableSpace Omega]
    (P : Nat -> LANParameter (PureTangentIndex d) -> Measure Omega)
    (hP : forall n h, IsProbabilityMeasure (P n h))
    (mu : Measure Omega) [hmu : IsProbabilityMeasure mu]
    (hbase : forall n, P n 0 = mu)
    (filtration : Nat -> Filtration Nat
      (inferInstance : MeasurableSpace Omega))
    (increment : Nat -> Nat -> Omega ->
      MartingaleScoreSpace (PureTangentIndex d))
    (hMDS : MartingaleCLTProblem.IsSquareIntegrableMartingaleDifferenceArray
      (fixedSampleMartingaleProblem (D := PureTangentIndex d)
        mu hmu filtration increment))
    (hLindeberg : MartingaleCLTProblem.HasConditionalLindeberg
      (fixedSampleMartingaleProblem (D := PureTangentIndex d)
        mu hmu filtration increment))
    (hCovariance : MartingaleCLTProblem.ConditionalCovarianceConverges
      (fixedSampleMartingaleProblem (D := PureTangentIndex d)
        mu hmu filtration increment) (pfsicInformation d))
    (hTerminalMeasurable : forall n,
      AEMeasurable
        ((fixedSampleMartingaleProblem (D := PureTangentIndex d)
          mu hmu filtration increment).terminalSum n) mu)
    (hDomination : forall n h, P n h ≪ P n 0)
    (hRemainder : LANRemainderConvergesInProbability
      (fixedSampleExperiment (D := PureTangentIndex d) P hP)
      (pfsicInformation d)
      (fixedSampleMartingaleProblem (D := PureTangentIndex d)
        mu hmu filtration increment).terminalSum)
    (estimator : ConcreteSafeguardedRegularizedOneStepStatisticData
      (PureTangentIndex d)
      (fixedSampleExperiment (D := PureTangentIndex d) P hP))
    (hCapped : forall I : Finset (LANParameter (PureTangentIndex d)),
      I.Nonempty -> CappedFiniteLocalRisksConvergeToCenteredGaussian
        (pfsicInformation d)
        (fixedSampleExperiment (D := PureTangentIndex d) P hP)
        estimator.toStatistic I)
    (hFourth : forall I : Finset (LANParameter (PureTangentIndex d)),
      I.Nonempty -> exists C : ENNReal, C ≠ ⊤ ∧
        HasUniformFiniteLocalFourthMomentBound
          (fixedSampleExperiment (D := PureTangentIndex d) P hP)
          estimator.toStatistic I C) :
    BatchMatrixEntrywiseTendsto design.batchInformation (pfsicInformation d) ∧
      IsLANSequence
        (fixedSampleExperiment (D := PureTangentIndex d) P hP)
        (pfsicInformation d)
        (fixedSampleMartingaleProblem (D := PureTangentIndex d)
          mu hmu filtration increment).terminalSum ∧
      (forall T : (n : Nat) -> Statistic
          (fixedSampleExperiment (D := PureTangentIndex d) P hP n)
          (LANParameter (PureTangentIndex d)),
        ENNReal.ofReal (4 * (d : Real)) <=
          asymptoticFiniteLocalQuadraticRisk
            (fixedSampleExperiment (D := PureTangentIndex d) P hP) T) ∧
      AttainsGaussianLocalAsymptoticMinimaxBound
        (pfsicInformation d)
        (fixedSampleExperiment (D := PureTangentIndex d) P hP)
        estimator.toStatistic := by
  have hInformation := design.information_tendsto
  have hLAN := adaptiveLANSequence_of_martingale_conditions
    P hP mu hmu hbase filtration increment
    (pfsicInformation d) (pfsicInformation_posDef d)
    hMDS hLindeberg hCovariance hTerminalMeasurable
    hDomination hRemainder
  have hExperiment :=
    adaptiveExperimentsConverge_gaussianScore_of_martingale_conditions
      P hP mu hmu hbase filtration increment
      (pfsicInformation d) (pfsicInformation_posDef d)
      hMDS hLindeberg hCovariance hTerminalMeasurable
      hDomination hRemainder
  have hLower : forall T : (n : Nat) -> Statistic
      (fixedSampleExperiment (D := PureTangentIndex d) P hP n)
      (LANParameter (PureTangentIndex d)),
      ENNReal.ofReal (4 * (d : Real)) <=
        asymptoticFiniteLocalQuadraticRisk
          (fixedSampleExperiment (D := PureTangentIndex d) P hP) T := by
    intro T
    exact pfsic_allEstimator_coordinateLocalMinimax_lowerBound
      (fixedSampleExperiment (D := PureTangentIndex d) P hP)
      hExperiment T
  have hAttains :=
    concreteSafeguardedRegularizedOneStep_attains_localAsymptoticMinimax
      (pfsicInformation d) (pfsicInformation_posDef d)
      (fixedSampleExperiment (D := PureTangentIndex d) P hP)
      estimator hExperiment hCapped hFourth
  exact ⟨hInformation.2, hLAN, hLower, hAttains⟩

end

end PureMultilevelSequentialBatchAdaptive
end QubitOracle.Paper
