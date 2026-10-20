import QubitOracle.Paper.PureMultilevelSequentialBatchAdaptive
import QubitOracle.Paper.MixedRadialTangentStage
import QubitOracle.Paper.CanonicalMinimaxConstants
import QubitOracle.Paper.CyclicPauliOneQubitStateLossMinimax

/-!
# Predetermined-batch adaptive mixed-qubit headline theorem

This file formalizes the deterministic-batch layer requested in the paper.
The batch sizes are fixed before data are observed, the controller may be
updated after every completed batch, and exploration occurs at the global
three-halves schedule.  The mathematically relevant sparsity condition is the
vanishing *cumulative* exploration fraction; no false per-batch convergence
condition is imposed.

The file proves, without a new scientific axiom:

* weighted information convergence for arbitrary positive batch sizes;
* convergence to both the Bures and Frobenius/trace mixed-qubit targets;
* sharp Bures, Frobenius, and squared-trace allocation inequalities;
* the exact qubit identity relating squared trace distance and Frobenius loss;
* the transfer from explicit Hall--Heyde martingale hypotheses through LAN to
  the all-estimator lower bound and the implemented safeguarded one-step
  estimator's attainment.

The last theorem deliberately keeps the likelihood remainder, conditional
covariance, capped-risk, fourth-moment, and physical-loss coordinate transfer
as hypotheses.  They are protocol facts, not additional axioms hidden in this
module.
-/

namespace QubitOracle.Paper
namespace OneQubitPredeterminedBatchHeadline

open Filter MeasureTheory
open scoped BigOperators Topology ENNReal

noncomputable section

open PureMultilevelSequentialBatchAdaptive

/-! ## Predetermined batches and the global sparse schedule -/

/-- The requested deterministic global exploration locations
`tau_l = ceil (l^(3/2))`, written as `ceil (l * sqrt l)`. -/
noncomputable def threeHalvesExplorationPosition (ell : Nat) : Nat :=
  ⌈(ell : Real) * Real.sqrt (ell : Real)⌉₊

/-- Number of three-halves exploration labels whose global location is before
`N`.  The range restriction is harmless for the intended increasing schedule
and gives a finite computational definition. -/
def threeHalvesExplorationCountBefore (N : Nat) : Nat :=
  ((Finset.range N).filter
    (fun ell => threeHalvesExplorationPosition ell < N)).card

/-- Largest one of the first `K` predetermined batches. -/
def largestBatchBefore (batchSize : Nat -> Nat) (K : Nat) : Nat :=
  (Finset.range K).sup batchSize

/-- Exact deterministic schedule assumptions used by the headline theorem.

`largestBatchFraction_tendsto_zero` is retained because it is the paper's
regularity condition.  The information proof below is stronger: once the
controller converges batchwise, positive arbitrary batch weights already
preserve its limit, so this field is not needed in that subproof.
-/
structure PredeterminedThreeHalvesBatchBudget where
  batchSize : Nat -> Nat
  explorationSize : Nat -> Nat
  batchSize_pos : forall k, 0 < batchSize k
  exploration_le_batch : forall k, explorationSize k <= batchSize k
  totalSamples_tendsto_atTop :
    Tendsto
      (fun K => (cumulativeCount batchSize K : Real)) atTop atTop
  exactThreeHalvesCount : forall K,
    cumulativeCount explorationSize K =
      threeHalvesExplorationCountBefore (cumulativeCount batchSize K)
  cumulativeExplorationFraction_tendsto_zero :
    Tendsto
      (fun K =>
        (cumulativeCount batchSize K : Real)⁻¹ *
          (cumulativeCount explorationSize K : Real))
      atTop (nhds 0)
  largestBatchFraction_tendsto_zero :
    Tendsto
      (fun K =>
        (largestBatchBefore batchSize K : Real) /
          (cumulativeCount batchSize K : Real))
      atTop (nhds 0)
  quarterRateExploration :
    Tendsto
      (fun K =>
        Real.sqrt (cumulativeCount batchSize K : Real) *
            Real.log ((cumulativeCount batchSize K : Real) + 2) /
          (cumulativeCount explorationSize K : Real))
      atTop (nhds 0)

theorem PredeterminedThreeHalvesBatchBudget.batchWeights_nonnegative
    (budget : PredeterminedThreeHalvesBatchBudget) (k : Nat) :
    0 <= (budget.batchSize k : Real) :=
  Nat.cast_nonneg _

theorem PredeterminedThreeHalvesBatchBudget.explorationWeights_nonnegative
    (budget : PredeterminedThreeHalvesBatchBudget) (k : Nat) :
    0 <= (budget.explorationSize k : Real) :=
  Nat.cast_nonneg _

/-! ## Weighted batching with cumulative sparse exploration -/

/-- The perturbation caused by exploration through completed batch `K`.
The denominator is the total number of observations, not the number of
batches. -/
def batchedExplorationError
    (batchSize explorationSize : Nat -> Nat)
    (exploitation exploration : Nat -> Real) (K : Nat) : Real :=
  (∑ k ∈ Finset.range K, (batchSize k : Real))⁻¹ *
    ∑ k ∈ Finset.range K,
      (explorationSize k : Real) * (exploration k - exploitation k)

/-- Completed-batch predictable average.  Its summand is exactly
`(m_k-e_k) A_k + e_k B_k`, written as `m_k A_k + e_k(B_k-A_k)` to avoid
natural-number subtraction in the convergence proof. -/
def batchedPredictableScalarAverage
    (batchSize explorationSize : Nat -> Nat)
    (exploitation exploration : Nat -> Real) (K : Nat) : Real :=
  (∑ k ∈ Finset.range K, (batchSize k : Real))⁻¹ *
    ∑ k ∈ Finset.range K,
      ((batchSize k : Real) * exploitation k +
        (explorationSize k : Real) * (exploration k - exploitation k))

theorem batchAllocation_identity
    (m e : Nat) (x y : Real) (he : e <= m) :
    (m : Real) * x + (e : Real) * (y - x) =
      ((m - e : Nat) : Real) * x + (e : Real) * y := by
  rw [Nat.cast_sub he]
  ring

theorem batchedExplorationError_norm_le
    (batchSize explorationSize : Nat -> Nat)
    (exploitation exploration : Nat -> Real) (C : Real)
    (hC : 0 <= C)
    (hdifference : forall k, ‖exploration k - exploitation k‖ <= C)
    (K : Nat) :
    ‖batchedExplorationError batchSize explorationSize
        exploitation exploration K‖ <=
      C * ((∑ k ∈ Finset.range K, (batchSize k : Real))⁻¹ *
        ∑ k ∈ Finset.range K, (explorationSize k : Real)) := by
  have hden : 0 <=
      (∑ k ∈ Finset.range K, (batchSize k : Real))⁻¹ :=
    inv_nonneg.mpr (Finset.sum_nonneg fun k _ => Nat.cast_nonneg _)
  unfold batchedExplorationError
  calc
    ‖(∑ k ∈ Finset.range K, (batchSize k : Real))⁻¹ *
        ∑ k ∈ Finset.range K,
          (explorationSize k : Real) *
            (exploration k - exploitation k)‖ =
        (∑ k ∈ Finset.range K, (batchSize k : Real))⁻¹ *
          ‖∑ k ∈ Finset.range K,
            (explorationSize k : Real) *
              (exploration k - exploitation k)‖ := by
          rw [norm_mul, Real.norm_of_nonneg hden]
    _ <= (∑ k ∈ Finset.range K, (batchSize k : Real))⁻¹ *
        ∑ k ∈ Finset.range K,
          ‖(explorationSize k : Real) *
            (exploration k - exploitation k)‖ :=
      mul_le_mul_of_nonneg_left
        (norm_sum_le (Finset.range K)
          (fun k => (explorationSize k : Real) *
            (exploration k - exploitation k))) hden
    _ = (∑ k ∈ Finset.range K, (batchSize k : Real))⁻¹ *
        ∑ k ∈ Finset.range K,
          (explorationSize k : Real) *
            ‖exploration k - exploitation k‖ := by
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [norm_mul, Real.norm_of_nonneg (Nat.cast_nonneg _)]
    _ <= (∑ k ∈ Finset.range K, (batchSize k : Real))⁻¹ *
        ∑ k ∈ Finset.range K, (explorationSize k : Real) * C := by
      apply mul_le_mul_of_nonneg_left _ hden
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left
        (hdifference k) (Nat.cast_nonneg _)
    _ = C * ((∑ k ∈ Finset.range K, (batchSize k : Real))⁻¹ *
        ∑ k ∈ Finset.range K, (explorationSize k : Real)) := by
      rw [← Finset.sum_mul]
      ring

theorem batchedExplorationError_tendsto_zero
    (batchSize explorationSize : Nat -> Nat)
    (exploitation exploration : Nat -> Real) (C : Real)
    (hC : 0 <= C)
    (hdifference : forall k, ‖exploration k - exploitation k‖ <= C)
    (hsparse : Tendsto
      (fun K =>
        (∑ k ∈ Finset.range K, (batchSize k : Real))⁻¹ *
          ∑ k ∈ Finset.range K, (explorationSize k : Real))
      atTop (nhds 0)) :
    Tendsto
      (batchedExplorationError batchSize explorationSize
        exploitation exploration) atTop (nhds 0) := by
  have hupper : Tendsto
      (fun K => C *
        ((∑ k ∈ Finset.range K, (batchSize k : Real))⁻¹ *
          ∑ k ∈ Finset.range K, (explorationSize k : Real)))
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hsparse)
  have hnorm : Tendsto
      (fun K => ‖batchedExplorationError batchSize explorationSize
        exploitation exploration K‖) atTop (nhds 0) :=
    squeeze_zero'
      (Eventually.of_forall fun K => norm_nonneg _)
      (Eventually.of_forall fun K =>
        batchedExplorationError_norm_le batchSize explorationSize
          exploitation exploration C hC hdifference K)
      hupper
  apply (tendsto_iff_norm_sub_tendsto_zero).2
  simpa only [sub_zero] using hnorm

theorem batchedPredictableScalarAverage_decompose
    (batchSize explorationSize : Nat -> Nat)
    (exploitation exploration : Nat -> Real) (K : Nat) :
    batchedPredictableScalarAverage batchSize explorationSize
        exploitation exploration K =
      weightedScalarAverage (fun k => (batchSize k : Real)) exploitation K +
        batchedExplorationError batchSize explorationSize
          exploitation exploration K := by
  unfold batchedPredictableScalarAverage weightedScalarAverage
    batchedExplorationError
  rw [← mul_add, ← Finset.sum_add_distrib]

/-- Scalar Toeplitz convergence with a cumulative, rather than stagewise,
exploration condition. -/
theorem batchedPredictableScalarAverage_tendsto
    (batchSize explorationSize : Nat -> Nat)
    (exploitation exploration : Nat -> Real) (target C : Real)
    (htotal : Tendsto
      (fun K => ∑ k ∈ Finset.range K, (batchSize k : Real)) atTop atTop)
    (hexploitation : Tendsto exploitation atTop (nhds target))
    (hC : 0 <= C)
    (hdifference : forall k, ‖exploration k - exploitation k‖ <= C)
    (hsparse : Tendsto
      (fun K =>
        (∑ k ∈ Finset.range K, (batchSize k : Real))⁻¹ *
          ∑ k ∈ Finset.range K, (explorationSize k : Real))
      atTop (nhds 0)) :
    Tendsto
      (batchedPredictableScalarAverage batchSize explorationSize
        exploitation exploration) atTop (nhds target) := by
  have hmain := weightedScalarAverage_tendsto
    (fun k => (batchSize k : Real)) exploitation target
      (fun _ => Nat.cast_nonneg _) htotal hexploitation
  have herror := batchedExplorationError_tendsto_zero
    batchSize explorationSize exploitation exploration C hC hdifference hsparse
  have hdecompose :
      batchedPredictableScalarAverage batchSize explorationSize
          exploitation exploration =
        fun K => weightedScalarAverage
          (fun k => (batchSize k : Real)) exploitation K +
            batchedExplorationError batchSize explorationSize
              exploitation exploration K := by
    funext K
    exact batchedPredictableScalarAverage_decompose
      batchSize explorationSize exploitation exploration K
  rw [hdecompose]
  simpa using hmain.add herror

/-- Entrywise completed-batch Fisher average. -/
def batchedPredictableMatrixAverage {D : Type*}
    (batchSize explorationSize : Nat -> Nat)
    (exploitation exploration : Nat -> Matrix D D Real) :
    Nat -> Matrix D D Real :=
  fun K i j => batchedPredictableScalarAverage batchSize explorationSize
    (fun k => exploitation k i j) (fun k => exploration k i j) K

theorem batchedPredictableMatrixAverage_tendsto
    {D : Type*}
    (batchSize explorationSize : Nat -> Nat)
    (exploitation exploration : Nat -> Matrix D D Real)
    (target : Matrix D D Real) (bound : D -> D -> Real)
    (htotal : Tendsto
      (fun K => ∑ k ∈ Finset.range K, (batchSize k : Real)) atTop atTop)
    (hexploitation : BatchMatrixEntrywiseTendsto exploitation target)
    (hbound : forall i j, 0 <= bound i j)
    (hdifference : forall k i j,
      ‖exploration k i j - exploitation k i j‖ <= bound i j)
    (hsparse : Tendsto
      (fun K =>
        (∑ k ∈ Finset.range K, (batchSize k : Real))⁻¹ *
          ∑ k ∈ Finset.range K, (explorationSize k : Real))
      atTop (nhds 0)) :
    BatchMatrixEntrywiseTendsto
      (batchedPredictableMatrixAverage batchSize explorationSize
        exploitation exploration) target := by
  intro i j
  exact batchedPredictableScalarAverage_tendsto
    batchSize explorationSize (fun k => exploitation k i j)
      (fun k => exploration k i j) (target i j) (bound i j)
      htotal (hexploitation i j) (hbound i j)
      (fun k => hdifference k i j) hsparse

/-! ## Concrete mixed-qubit loss-specific stages -/

def buresExploitationInformation
    (theta : Fin 3 -> Real) (controller : Nat -> Fin 3 -> Real)
    (frame : forall k, MixedRadialTangentFrame (controller k)) :
    Nat -> OracleMatrix :=
  fun k => mixedStageInformation theta
    (radialTangentMass (1 / 3 : Real) (1 / 3 : Real))
    (radialTangentAxes (frame k).tangentFirst
      (frame k).tangentSecond (frame k).radial)

def frobeniusTraceExploitationInformation
    (theta : Fin 3 -> Real) (controller : Nat -> Fin 3 -> Real)
    (frame : forall k, MixedRadialTangentFrame (controller k)) :
    Nat -> OracleMatrix :=
  fun k => mixedStageInformation theta
    (radialTangentMass
      (mixedCoherenceAllocation (controller k))
      (mixedRadialAllocation (controller k)))
    (radialTangentAxes (frame k).tangentFirst
      (frame k).tangentSecond (frame k).radial)

/-- Concrete data for the mixed-qubit controller.  `controller_tendsto` is the
exact interface supplied by the projected-RLS theorem; deterministic
tie-breaking is represented by the total function `frame`. -/
structure PredeterminedBatchMixedQubitDesign where
  budget : PredeterminedThreeHalvesBatchBudget
  theta : Fin 3 -> Real
  thetaInterior : blochNormSq theta < 1
  controller : Nat -> Fin 3 -> Real
  controller_tendsto : Tendsto controller atTop (nhds theta)
  controllerInterior : forall k, blochNormSq (controller k) < 1
  frame : forall k, MixedRadialTangentFrame (controller k)
  explorationInformation : Nat -> OracleMatrix
  buresDeviationBound : Fin 3 -> Fin 3 -> Real
  buresDeviationBound_nonnegative : forall i j,
    0 <= buresDeviationBound i j
  buresExplorationDifference_bounded : forall k i j,
    ‖explorationInformation k i j -
      buresExploitationInformation theta controller frame k i j‖ <=
        buresDeviationBound i j
  frobeniusDeviationBound : Fin 3 -> Fin 3 -> Real
  frobeniusDeviationBound_nonnegative : forall i j,
    0 <= frobeniusDeviationBound i j
  frobeniusExplorationDifference_bounded : forall k i j,
    ‖explorationInformation k i j -
      frobeniusTraceExploitationInformation theta controller frame k i j‖ <=
        frobeniusDeviationBound i j

def PredeterminedBatchMixedQubitDesign.buresBatchInformation
    (data : PredeterminedBatchMixedQubitDesign) : Nat -> OracleMatrix :=
  batchedPredictableMatrixAverage data.budget.batchSize
    data.budget.explorationSize
    (buresExploitationInformation data.theta data.controller data.frame)
    data.explorationInformation

def PredeterminedBatchMixedQubitDesign.frobeniusTraceBatchInformation
    (data : PredeterminedBatchMixedQubitDesign) : Nat -> OracleMatrix :=
  batchedPredictableMatrixAverage data.budget.batchSize
    data.budget.explorationSize
    (frobeniusTraceExploitationInformation
      data.theta data.controller data.frame)
    data.explorationInformation

theorem PredeterminedBatchMixedQubitDesign.buresInformation_tendsto
    (data : PredeterminedBatchMixedQubitDesign) :
    BatchMatrixEntrywiseTendsto data.buresBatchInformation
      (mixedBuresTarget data.theta) := by
  have hexploitMatrix := mixedBuresStage_tendsto data.theta
    data.thetaInterior data.controller data.controller_tendsto
      data.controllerInterior data.frame
  have hexploit : BatchMatrixEntrywiseTendsto
      (buresExploitationInformation data.theta data.controller data.frame)
      (mixedBuresTarget data.theta) := by
    intro i j
    exact tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hexploitMatrix i) j
  have htotal : Tendsto
      (fun K => ∑ k ∈ Finset.range K, (data.budget.batchSize k : Real))
      atTop atTop := by
    simpa [cumulativeCount] using data.budget.totalSamples_tendsto_atTop
  exact batchedPredictableMatrixAverage_tendsto
    data.budget.batchSize data.budget.explorationSize
      (buresExploitationInformation data.theta data.controller data.frame)
      data.explorationInformation (mixedBuresTarget data.theta)
      data.buresDeviationBound htotal hexploit
      data.buresDeviationBound_nonnegative
      data.buresExplorationDifference_bounded
      (by simpa [cumulativeCount] using
        data.budget.cumulativeExplorationFraction_tendsto_zero)

theorem PredeterminedBatchMixedQubitDesign.frobeniusTraceInformation_tendsto
    (data : PredeterminedBatchMixedQubitDesign) :
    BatchMatrixEntrywiseTendsto data.frobeniusTraceBatchInformation
      (mixedFrobeniusTraceTarget data.theta) := by
  have hexploitMatrix := mixedFrobeniusTraceStage_tendsto data.theta
    data.thetaInterior data.controller data.controller_tendsto
      data.controllerInterior data.frame
  have hexploit : BatchMatrixEntrywiseTendsto
      (frobeniusTraceExploitationInformation
        data.theta data.controller data.frame)
      (mixedFrobeniusTraceTarget data.theta) := by
    intro i j
    exact tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hexploitMatrix i) j
  have htotal : Tendsto
      (fun K => ∑ k ∈ Finset.range K, (data.budget.batchSize k : Real))
      atTop atTop := by
    simpa [cumulativeCount] using data.budget.totalSamples_tendsto_atTop
  exact batchedPredictableMatrixAverage_tendsto
    data.budget.batchSize data.budget.explorationSize
      (frobeniusTraceExploitationInformation
        data.theta data.controller data.frame)
      data.explorationInformation (mixedFrobeniusTraceTarget data.theta)
      data.frobeniusDeviationBound htotal hexploit
      data.frobeniusDeviationBound_nonnegative
      data.frobeniusExplorationDifference_bounded
      (by simpa [cumulativeCount] using
        data.budget.cumulativeExplorationFraction_tendsto_zero)

/-! ## Sharp loss-specific allocation constants -/

def mixedBuresAllocationRisk (a b : Real) : Real :=
  (1 / 4 : Real) * (2 / a + 1 / b)

def mixedFrobeniusAllocationRisk (q a b : Real) : Real :=
  (1 / 2 : Real) * (2 / a + q ^ 2 / b)

def mixedSquaredTraceAllocationRisk (q a b : Real) : Real :=
  (1 / 4 : Real) * (2 / a + q ^ 2 / b)

theorem mixedBuresAllocationRisk_lower_bound
    {a b : Real} (ha : 0 < a) (hb : 0 < b)
    (hbudget : 2 * a + b <= 1) :
    (9 / 4 : Real) <= mixedBuresAllocationRisk a b := by
  have h := mixed_threeCoordinate_information_budget_lower_bound
    ha ha hb (by linarith)
  unfold threeCoordinateReciprocalRisk at h
  unfold mixedBuresAllocationRisk
  simp only [div_eq_mul_inv]
  nlinarith

theorem mixedBuresEqualAllocation_attains :
    mixedBuresAllocationRisk (1 / 3 : Real) (1 / 3 : Real) = 9 / 4 := by
  norm_num [mixedBuresAllocationRisk]

theorem mixedFrobeniusAllocationRisk_lower_bound
    {q a b : Real} (ha : 0 < a) (hb : 0 < b)
    (hbudget : 2 * a + b <= 1) :
    (1 / 2 : Real) * (2 + q) ^ 2 <=
      mixedFrobeniusAllocationRisk q a b := by
  have hid :
      (2 * a + b) * (2 / a + q ^ 2 / b) - (2 + q) ^ 2 =
        2 * (b - a * q) ^ 2 / (a * b) := by
    field_simp [ha.ne', hb.ne']
    ring
  have hgap : 0 <=
      (2 * a + b) * (2 / a + q ^ 2 / b) - (2 + q) ^ 2 := by
    rw [hid]
    positivity
  have hrisk : 0 <= 2 / a + q ^ 2 / b := by
    positivity
  have hbudgetRisk :
      (2 * a + b) * (2 / a + q ^ 2 / b) <=
        2 / a + q ^ 2 / b := by
    simpa using mul_le_mul_of_nonneg_right hbudget hrisk
  unfold mixedFrobeniusAllocationRisk
  nlinarith

theorem mixedFrobeniusAllocation_attains
    {q : Real} (hq : 0 < q) :
    mixedFrobeniusAllocationRisk q
        (2 + q)⁻¹ (q / (2 + q)) =
      (1 / 2 : Real) * (2 + q) ^ 2 := by
  have hden : 2 + q ≠ 0 := by positivity
  unfold mixedFrobeniusAllocationRisk
  field_simp [hq.ne', hden]

theorem mixedSquaredTraceAllocationRisk_eq_half_frobenius
    (q a b : Real) :
    mixedSquaredTraceAllocationRisk q a b =
      (1 / 2 : Real) * mixedFrobeniusAllocationRisk q a b := by
  unfold mixedSquaredTraceAllocationRisk mixedFrobeniusAllocationRisk
  ring

theorem mixedSquaredTraceAllocation_attains
    {q : Real} (hq : 0 < q) :
    mixedSquaredTraceAllocationRisk q
        (2 + q)⁻¹ (q / (2 + q)) =
      (1 / 4 : Real) * (2 + q) ^ 2 := by
  rw [mixedSquaredTraceAllocationRisk_eq_half_frobenius,
    mixedFrobeniusAllocation_attains hq]
  ring

/-- For all qubit states, the Bloch formulas give squared trace distance equal
to one half of squared Frobenius distance. -/
def qubitBlochSquaredTraceDistance
    (theta sigma : RLSVector 3) : Real :=
  (1 / 4 : Real) * cyclicPauliNormSq (fun j => sigma j - theta j)

theorem qubit_squaredTraceDistance_eq_half_frobenius
    (theta sigma : RLSVector 3) :
    qubitBlochSquaredTraceDistance theta sigma =
      (1 / 2 : Real) * qubitBlochFrobeniusSq theta sigma := by
  unfold qubitBlochSquaredTraceDistance qubitBlochFrobeniusSq
  ring

/-! ## Martingale LAN and implemented safeguarded minimax endpoint -/

inductive MixedLossBranch
  | bures
  | frobeniusTrace
  deriving DecidableEq

def PredeterminedBatchMixedQubitDesign.branchTarget
    (data : PredeterminedBatchMixedQubitDesign) :
    MixedLossBranch -> OracleMatrix
  | .bures => mixedBuresTarget data.theta
  | .frobeniusTrace => mixedFrobeniusTraceTarget data.theta

def PredeterminedBatchMixedQubitDesign.branchBatchInformation
    (data : PredeterminedBatchMixedQubitDesign) :
    MixedLossBranch -> Nat -> OracleMatrix
  | .bures => data.buresBatchInformation
  | .frobeniusTrace => data.frobeniusTraceBatchInformation

theorem PredeterminedBatchMixedQubitDesign.branchInformation_tendsto
    (data : PredeterminedBatchMixedQubitDesign) (branch : MixedLossBranch) :
    BatchMatrixEntrywiseTendsto
      (data.branchBatchInformation branch) (data.branchTarget branch) := by
  cases branch with
  | bures => exact data.buresInformation_tendsto
  | frobeniusTrace => exact data.frobeniusTraceInformation_tendsto

/-- Headline adaptive theorem for either loss-specific design.

The information convergence in the first conclusion is proved from the
predetermined batches above.  LAN and minimax are then proved from the exact
martingale, covariance, likelihood-remainder, and uniform-risk conditions.
The estimator in the conclusion is definitionally the concrete safeguarded,
regularized one-step update.
-/
theorem predeterminedBatchMixedQubit_headline_LAN_and_minimax
    (design : PredeterminedBatchMixedQubitDesign)
    (branch : MixedLossBranch)
    {Omega : Type} [MeasurableSpace Omega]
    (P : Nat -> LANParameter (Fin 3) -> Measure Omega)
    (hP : forall n h, IsProbabilityMeasure (P n h))
    (mu : Measure Omega) [hmu : IsProbabilityMeasure mu]
    (hbase : forall n, P n 0 = mu)
    (filtration : Nat -> Filtration Nat
      (inferInstance : MeasurableSpace Omega))
    (increment : Nat -> Nat -> Omega -> MartingaleScoreSpace (Fin 3))
    (hTargetPosDef : (design.branchTarget branch).PosDef)
    (hMDS : MartingaleCLTProblem.IsSquareIntegrableMartingaleDifferenceArray
      (fixedSampleMartingaleProblem (D := Fin 3)
        mu hmu filtration increment))
    (hLindeberg : MartingaleCLTProblem.HasConditionalLindeberg
      (fixedSampleMartingaleProblem (D := Fin 3)
        mu hmu filtration increment))
    (hCovariance : MartingaleCLTProblem.ConditionalCovarianceConverges
      (fixedSampleMartingaleProblem (D := Fin 3)
        mu hmu filtration increment) (design.branchTarget branch))
    (hTerminalMeasurable : forall n,
      AEMeasurable
        ((fixedSampleMartingaleProblem (D := Fin 3)
          mu hmu filtration increment).terminalSum n) mu)
    (hDomination : forall n h, P n h ≪ P n 0)
    (hRemainder : LANRemainderConvergesInProbability
      (fixedSampleExperiment (D := Fin 3) P hP)
      (design.branchTarget branch)
      (fixedSampleMartingaleProblem (D := Fin 3)
        mu hmu filtration increment).terminalSum)
    (estimator : ConcreteSafeguardedRegularizedOneStepStatisticData
      (Fin 3) (fixedSampleExperiment (D := Fin 3) P hP))
    (hCapped : forall I : Finset (LANParameter (Fin 3)),
      I.Nonempty -> CappedFiniteLocalRisksConvergeToCenteredGaussian
        (design.branchTarget branch)
        (fixedSampleExperiment (D := Fin 3) P hP)
        estimator.toStatistic I)
    (hFourth : forall I : Finset (LANParameter (Fin 3)),
      I.Nonempty -> exists C : ENNReal, C ≠ ⊤ ∧
        HasUniformFiniteLocalFourthMomentBound
          (fixedSampleExperiment (D := Fin 3) P hP)
          estimator.toStatistic I C) :
    BatchMatrixEntrywiseTendsto
        (design.branchBatchInformation branch) (design.branchTarget branch) ∧
      IsLANSequence
        (fixedSampleExperiment (D := Fin 3) P hP)
        (design.branchTarget branch)
        (fixedSampleMartingaleProblem (D := Fin 3)
          mu hmu filtration increment).terminalSum ∧
      ExperimentsConverge
        (fixedSampleExperiment (D := Fin 3) P hP)
        (gaussianScoreExperiment (design.branchTarget branch)) ∧
      (forall T : (n : Nat) -> Statistic
          (fixedSampleExperiment (D := Fin 3) P hP n)
          (LANParameter (Fin 3)),
        ENNReal.ofReal (Matrix.trace (design.branchTarget branch)⁻¹) <=
          asymptoticFiniteLocalQuadraticRisk
            (fixedSampleExperiment (D := Fin 3) P hP) T) ∧
      AttainsGaussianLocalAsymptoticMinimaxBound
        (design.branchTarget branch)
        (fixedSampleExperiment (D := Fin 3) P hP)
        estimator.toStatistic := by
  have hInformation := design.branchInformation_tendsto branch
  have hLAN := adaptiveLANSequence_of_martingale_conditions
    P hP mu hmu hbase filtration increment
      (design.branchTarget branch) hTargetPosDef
      hMDS hLindeberg hCovariance hTerminalMeasurable
      hDomination hRemainder
  have hExperiment :=
    adaptiveExperimentsConverge_gaussianScore_of_martingale_conditions
      P hP mu hmu hbase filtration increment
        (design.branchTarget branch) hTargetPosDef
        hMDS hLindeberg hCovariance hTerminalMeasurable
        hDomination hRemainder
  have hLower : forall T : (n : Nat) -> Statistic
      (fixedSampleExperiment (D := Fin 3) P hP n)
      (LANParameter (Fin 3)),
      ENNReal.ofReal (Matrix.trace (design.branchTarget branch)⁻¹) <=
        asymptoticFiniteLocalQuadraticRisk
          (fixedSampleExperiment (D := Fin 3) P hP) T := by
    intro T
    exact gaussianScore_localAsymptoticMinimax_quadratic
      (design.branchTarget branch) hTargetPosDef
      (fixedSampleExperiment (D := Fin 3) P hP) hExperiment T
  have hAttains :=
    concreteSafeguardedRegularizedOneStep_attains_localAsymptoticMinimax
      (design.branchTarget branch) hTargetPosDef
      (fixedSampleExperiment (D := Fin 3) P hP)
      estimator hExperiment hCapped hFourth
  exact ⟨hInformation, hLAN, hExperiment, hLower, hAttains⟩

/-- Physical-loss form of the minimax equality.  The transfer hypothesis is
where a concrete Bures, infidelity, Frobenius, or trace loss is identified
with its chosen local quadratic coordinates. -/
theorem concreteSafeguarded_physicalLoss_minimax
    (J : OracleMatrix) (hJ : J.PosDef)
    (E : Nat -> StatisticalExperiment (LANParameter (Fin 3)))
    (hExperiment : ExperimentsConverge E (gaussianScoreExperiment J))
    (physicalRisk : LocalEstimatorSequence E -> ENNReal)
    (hLossTransfer : HasExactPhysicalLossTransfer E physicalRisk)
    (estimator : ConcreteSafeguardedRegularizedOneStepStatisticData (Fin 3) E)
    (hCapped : forall I : Finset (LANParameter (Fin 3)), I.Nonempty ->
      CappedFiniteLocalRisksConvergeToCenteredGaussian
        J E estimator.toStatistic I)
    (hFourth : forall I : Finset (LANParameter (Fin 3)), I.Nonempty ->
      exists C : ENNReal, C ≠ ⊤ ∧
        HasUniformFiniteLocalFourthMomentBound
          E estimator.toStatistic I C)
    (constant : Real) (hconstant : Matrix.trace J⁻¹ = constant) :
    (forall T, ENNReal.ofReal constant <= physicalRisk T) ∧
      physicalRisk estimator.toStatistic = ENNReal.ofReal constant ∧
      (⨅ T, physicalRisk T) = ENNReal.ofReal constant := by
  have hTails : forall I : Finset (LANParameter (Fin 3)), I.Nonempty ->
      HasUniformFiniteLocalQuadraticTails E estimator.toStatistic I := by
    intro I hI
    obtain ⟨C, hC, hMoment⟩ := hFourth I hI
    exact hasUniformFiniteLocalQuadraticTails_of_fourthMoment
      E estimator.toStatistic I C hC hMoment
  have h := physicalLocalMinimax_lower_attained_and_value
    J hJ E hExperiment physicalRisk hLossTransfer
      estimator.toStatistic hCapped hTails
  rw [hconstant] at h
  exact h

/-- Deterministic information-and-design part of the requested headline,
simultaneously for Bures, Frobenius, and squared trace distance. -/
theorem predeterminedBatchMixedQubit_headline_information_and_design
    (design : PredeterminedBatchMixedQubitDesign) :
    BatchMatrixEntrywiseTendsto design.buresBatchInformation
        (mixedBuresTarget design.theta) ∧
      BatchMatrixEntrywiseTendsto design.frobeniusTraceBatchInformation
        (mixedFrobeniusTraceTarget design.theta) ∧
      (forall a b : Real, 0 < a -> 0 < b -> 2 * a + b <= 1 ->
        (9 / 4 : Real) <= mixedBuresAllocationRisk a b) ∧
      mixedBuresAllocationRisk (1 / 3 : Real) (1 / 3 : Real) = 9 / 4 ∧
      mixedFrobeniusAllocationRisk (mixedRadialGap design.theta)
          (mixedCoherenceAllocation design.theta)
          (mixedRadialAllocation design.theta) =
        (1 / 2 : Real) * (2 + mixedRadialGap design.theta) ^ 2 ∧
      mixedSquaredTraceAllocationRisk (mixedRadialGap design.theta)
          (mixedCoherenceAllocation design.theta)
          (mixedRadialAllocation design.theta) =
        (1 / 4 : Real) * (2 + mixedRadialGap design.theta) ^ 2 := by
  have hq : 0 < mixedRadialGap design.theta :=
    mixedRadialGap_pos design.theta design.thetaInterior
  have ha : mixedCoherenceAllocation design.theta =
      (2 + mixedRadialGap design.theta)⁻¹ := rfl
  have hb : mixedRadialAllocation design.theta =
      mixedRadialGap design.theta / (2 + mixedRadialGap design.theta) := rfl
  refine ⟨design.buresInformation_tendsto,
    design.frobeniusTraceInformation_tendsto, ?_,
    mixedBuresEqualAllocation_attains, ?_, ?_⟩
  · intro a b ha' hb' hbudget
    exact mixedBuresAllocationRisk_lower_bound ha' hb' hbudget
  · rw [ha, hb]
    exact mixedFrobeniusAllocation_attains hq
  · rw [ha, hb]
    exact mixedSquaredTraceAllocation_attains hq

end

end OneQubitPredeterminedBatchHeadline
end QubitOracle.Paper
