import QubitOracle.Paper.OneQubitPrespecifiedBatchFiniteExperiment
import QubitOracle.Paper.OneQubitMixedTwoStageFiniteScore
import QubitOracle.Paper.ConcreteSafeguardedOneStep
import QubitOracle.Paper.ProtocolRegularity

/-!
# A data-computable safeguarded estimator for prespecified batches

For a fixed number `K` of completed exact batches, this module constructs an
estimator from the literal pilot and final outcomes in those batches.

* The pooled pilot is the pilot-block-weighted average of the empirical Pauli
  means from all completed batches.
* Every score and Fisher contribution uses the axis actually selected by that
  batch's own pilot.
* The Fisher-scoring update uses a positive deterministic ridge.
* The safeguard accepts only a positive-definite regularized information
  matrix and a raw update in the closed Bloch ball; otherwise it returns the
  fixed physical state `0`.

All definitions depend only on the observed finite prefix, the public fallback
direction `b`, and `K`.  `Real` arithmetic and matrix inversion make the Lean
definitions `noncomputable`, but no unknown statistical parameter occurs in
the estimator.  This file proves finite-space measurability and exact algebra;
it deliberately makes no asymptotic LAN, efficiency, or minimax assertion.
-/

namespace QubitOracle.Paper

open MeasureTheory Set
open scoped BigOperators

noncomputable section

attribute [local instance]
  pauliPilotBornPathMeasurableSpace
  mixedTwoStageFiniteRowMeasurableSpace
  mixedTwoStageFiniteRowMeasurableSingletonClass

/-- Put a finite real coordinate vector into Mathlib's Euclidean `L2` wrapper. -/
def prespecifiedBatchLANVector (x : Fin 3 -> Real) : LANParameter (Fin 3) :=
  WithLp.toLp 2 x

@[simp]
theorem prespecifiedBatchLANVector_apply (x : Fin 3 -> Real) (i : Fin 3) :
    prespecifiedBatchLANVector x i = x i :=
  rfl

/-- The observed data in the first `K` exact prespecified batches. -/
abbrev ExactConcretePredeterminedBatchPrefix (K : Nat) : Type :=
  (k : Fin K) -> ExactConcretePredeterminedBatchRow k

/-- Number of complete three-Pauli pilot blocks pooled through batch `K - 1`. -/
def prespecifiedBatchPooledPilotBlocks (K : Nat) : Nat :=
  ∑ k : Fin K, exactConcreteBatchPilotBlocks k

/-- The positive convention used in the pooled pilot denominator.  For
`K = 0` it is `1`; for nonempty prefixes it is the actual number of pilot
blocks. -/
def prespecifiedBatchPooledPilotDenominator (K : Nat) : Real :=
  (max 1 (prespecifiedBatchPooledPilotBlocks K) : Nat)

/-- Genuine pooled empirical pilot.  Batch means are weighted by their actual
numbers of complete Pauli blocks. -/
def prespecifiedBatchPooledPilot (K : Nat)
    (omega : ExactConcretePredeterminedBatchPrefix K) : RLSVector 3 :=
  fun j =>
    (prespecifiedBatchPooledPilotDenominator K)⁻¹ *
      ∑ k : Fin K,
        (exactConcreteBatchPilotBlocks k : Real) *
          pauliPilotEstimate (omega k).1 j

/-- Standard Pauli axis `j` in Bloch coordinates. -/
def prespecifiedBatchPauliAxis (j : Fin 3) : RLSVector 3 :=
  fun i => if i = j then 1 else 0

/-- Coordinate score of all pilot observations, evaluated at `x`. -/
def prespecifiedBatchPilotScoreCoordinate (K : Nat)
    (x : RLSVector 3) (omega : ExactConcretePredeterminedBatchPrefix K)
    (coordinate : Fin 3) : Real :=
  ∑ k : Fin K,
    ∑ r : Fin (exactConcreteBatchPilotBlocks k),
      ∑ j : Fin 3,
        mixedTwoStageAxisDirectionalScore x
          (prespecifiedBatchPauliAxis coordinate)
          (prespecifiedBatchPauliAxis j) ((omega k).1 r j)

/-- Coordinate score of all exploitation observations.  The axis is the
literal cyclic axis in the frame selected from the same row's pilot. -/
def prespecifiedBatchFinalScoreCoordinate (K : Nat) (b x : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K)
    (coordinate : Fin 3) : Real :=
  ∑ k : Fin K,
    mixedTwoStageFinalPathDirectionalScoreSum x
      (prespecifiedBatchPauliAxis coordinate)
      (exactConcreteBatchSelectedFrame k b) (omega k).1 (omega k).2

/-- Full three-coordinate score, evaluated at `x`, from the observed prefix. -/
def prespecifiedBatchScore (K : Nat) (b x : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K) : LANParameter (Fin 3) :=
  prespecifiedBatchLANVector fun coordinate =>
    prespecifiedBatchPilotScoreCoordinate K x omega coordinate +
      prespecifiedBatchFinalScoreCoordinate K b x omega coordinate

/-- One Fisher-information matrix entry for a binary qubit measurement. -/
def prespecifiedBatchAxisFisherEntry (x axis : RLSVector 3)
    (i j : Fin 3) : Real :=
  axis i * axis j / (1 - QubitOracle.blochDot x axis ^ 2)

/-- Observed-design Fisher information from all pilot axes. -/
def prespecifiedBatchPilotInformation (K : Nat) (x : RLSVector 3)
    (i j : Fin 3) : Real :=
  ∑ k : Fin K,
    ∑ _r : Fin (exactConcreteBatchPilotBlocks k),
      ∑ axis : Fin 3,
        prespecifiedBatchAxisFisherEntry x
          (prespecifiedBatchPauliAxis axis) i j

/-- Observed-design Fisher information from all exploitation axes.  Although
this Fisher term does not use the binary outcomes, it uses the frame selected
from each batch's observed pilot and is therefore a statistic of the data. -/
def prespecifiedBatchFinalInformation (K : Nat) (b x : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K) (i j : Fin 3) : Real :=
  ∑ k : Fin K,
    ∑ t : Fin (3 * exactConcreteBatchFinalBlocks k),
      prespecifiedBatchAxisFisherEntry x
        (mixedTwoStageFinalAxis
          (exactConcreteBatchSelectedFrame k b) (omega k).1 t) i j

/-- Total observed-design Fisher information evaluated at `x`. -/
def prespecifiedBatchInformation (K : Nat) (b x : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K) : Matrix (Fin 3) (Fin 3) Real :=
  fun i j =>
    prespecifiedBatchPilotInformation K x i j +
      prespecifiedBatchFinalInformation K b x omega i j

/-- The square-root total-sample scale. -/
def prespecifiedBatchSampleScale (K : Nat) : Real :=
  Real.sqrt (prespecifiedBatchTotalObservations K : Real)

/-- A deterministic positive ridge. -/
def prespecifiedBatchRidge (K : Nat) : Real :=
  (((K + 1 : Nat) : Real) ^ 2)⁻¹

theorem prespecifiedBatchRidge_pos (K : Nat) :
    0 < prespecifiedBatchRidge K := by
  unfold prespecifiedBatchRidge
  positivity

theorem prespecifiedBatchRidge_le_one (K : Nat) :
    prespecifiedBatchRidge K <= 1 := by
  unfold prespecifiedBatchRidge
  apply inv_le_one_of_one_le₀
  have h : (1 : Real) <= (((K + 1 : Nat) : Real)) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le K)
  nlinarith [sq_nonneg ((((K + 1 : Nat) : Real)) - 1)]

/-- Radial retraction onto the closed Bloch ball. -/
def oneQubitBlochBallRadialClip (x : RLSVector 3) : RLSVector 3 :=
  if QubitOracle.blochNormSq x <= 1 then x
  else fun i => x i / Real.sqrt (QubitOracle.blochNormSq x)

/-- Strictly interior evaluation point used by every score and Fisher
contribution.  The raw update remains centered at the unmodified pooled pilot. -/
def prespecifiedBatchSafeEvaluationPilot (K : Nat)
    (omega : ExactConcretePredeterminedBatchPrefix K) : RLSVector 3 :=
  fun i => (1 - prespecifiedBatchRidge K ^ 2) *
    oneQubitBlochBallRadialClip (prespecifiedBatchPooledPilot K omega) i

/-- Normalized score at the pooled pilot. -/
def prespecifiedBatchNormalizedScore (K : Nat) (b : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K) : LANParameter (Fin 3) :=
  prespecifiedBatchLANVector fun i =>
    (prespecifiedBatchSampleScale K)⁻¹ *
      prespecifiedBatchScore K b
        (prespecifiedBatchSafeEvaluationPilot K omega) omega i

/-- Normalized observed-design Fisher information at the pooled pilot. -/
def prespecifiedBatchNormalizedInformation (K : Nat) (b : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K) :
    Matrix (Fin 3) (Fin 3) Real :=
  fun i j =>
    (prespecifiedBatchTotalObservations K : Real)⁻¹ *
      prespecifiedBatchInformation K b
        (prespecifiedBatchSafeEvaluationPilot K omega) omega i j

/-- Raw regularized Fisher-scoring update.  It contains no true parameter. -/
def prespecifiedBatchRawOneStepEstimator (K : Nat) (b : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K) : RLSVector 3 :=
  let pilot := prespecifiedBatchPooledPilot K omega
  let A := regularizedNormalizedInformation
    (prespecifiedBatchNormalizedInformation K b omega)
    (prespecifiedBatchRidge K)
  let step := lanMatrixAction A⁻¹ (prespecifiedBatchNormalizedScore K b omega)
  fun i => pilot i + (prespecifiedBatchSampleScale K)⁻¹ * step i

/-! ## Radially projected terminal estimator -/

theorem oneQubitBlochBallRadialClip_measurable :
    Measurable oneQubitBlochBallRadialClip := by
  classical
  unfold oneQubitBlochBallRadialClip
  have hnorm : Measurable (fun x : RLSVector 3 =>
      QubitOracle.blochNormSq x) := by
    unfold QubitOracle.blochNormSq
    fun_prop
  exact Measurable.ite (measurableSet_le hnorm measurable_const)
    measurable_id (by fun_prop)

theorem oneQubitBlochBallRadialClip_eq_self
    (x : RLSVector 3) (hx : QubitOracle.blochNormSq x <= 1) :
    oneQubitBlochBallRadialClip x = x := by
  simp [oneQubitBlochBallRadialClip, hx]

private theorem blochNormSq_radialNormalize
    (x : RLSVector 3) (hx : 0 < QubitOracle.blochNormSq x) :
    QubitOracle.blochNormSq
      (fun i => x i / Real.sqrt (QubitOracle.blochNormSq x)) = 1 := by
  unfold QubitOracle.blochNormSq
  simp only [div_pow]
  rw [← Finset.sum_div]
  have hx' : 0 < ∑ i, x i ^ 2 := by
    simpa [QubitOracle.blochNormSq] using hx
  rw [Real.sq_sqrt (le_of_lt hx')]
  exact div_self (ne_of_gt hx')

theorem oneQubitBlochBallRadialClip_physical (x : RLSVector 3) :
    QubitOracle.blochNormSq (oneQubitBlochBallRadialClip x) <= 1 := by
  unfold oneQubitBlochBallRadialClip
  split_ifs with hx
  · exact hx
  · rw [blochNormSq_radialNormalize x
      (lt_trans zero_lt_one (lt_of_not_ge hx))]

private theorem blochNormSq_mul_vector (c : Real) (x : RLSVector 3) :
    QubitOracle.blochNormSq (fun i => c * x i) =
      c ^ 2 * QubitOracle.blochNormSq x := by
  unfold QubitOracle.blochNormSq
  simp_rw [mul_pow]
  rw [Finset.mul_sum]

theorem prespecifiedBatchSafeEvaluationPilot_strictInterior
    (K : Nat) (omega : ExactConcretePredeterminedBatchPrefix K) :
    QubitOracle.blochNormSq
      (prespecifiedBatchSafeEvaluationPilot K omega) < 1 := by
  rw [show prespecifiedBatchSafeEvaluationPilot K omega =
      fun i => (1 - prespecifiedBatchRidge K ^ 2) *
        oneQubitBlochBallRadialClip
          (prespecifiedBatchPooledPilot K omega) i by rfl,
    blochNormSq_mul_vector]
  have hridgePos := prespecifiedBatchRidge_pos K
  have hridgeLe := prespecifiedBatchRidge_le_one K
  have hridgeSqPos : 0 < prespecifiedBatchRidge K ^ 2 :=
    sq_pos_of_pos hridgePos
  have hridgeSqLe : prespecifiedBatchRidge K ^ 2 <= 1 := by
    nlinarith [sq_nonneg (prespecifiedBatchRidge K - 1)]
  have hfactor0 : 0 <= 1 - prespecifiedBatchRidge K ^ 2 := by linarith
  have hfactorSq : (1 - prespecifiedBatchRidge K ^ 2) ^ 2 < 1 := by
    nlinarith
  have hclip := oneQubitBlochBallRadialClip_physical
    (prespecifiedBatchPooledPilot K omega)
  calc
    (1 - prespecifiedBatchRidge K ^ 2) ^ 2 *
        QubitOracle.blochNormSq
          (oneQubitBlochBallRadialClip
            (prespecifiedBatchPooledPilot K omega)) <=
        (1 - prespecifiedBatchRidge K ^ 2) ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hclip (sq_nonneg _)
    _ < 1 := by simpa using hfactorSq

theorem prespecifiedBatchSafeEvaluationPilot_measurable (K : Nat) :
    Measurable (prespecifiedBatchSafeEvaluationPilot K) :=
  measurable_of_finite _

/-- Matrix form of one binary-axis Fisher contribution. -/
def prespecifiedBatchAxisFisherMatrix (x axis : RLSVector 3) :
    Matrix (Fin 3) (Fin 3) Real :=
  fun i j => prespecifiedBatchAxisFisherEntry x axis i j

theorem prespecifiedBatchEstimatorPauliAxis_unit (j : Fin 3) :
    QubitOracle.blochNormSq (prespecifiedBatchPauliAxis j) = 1 := by
  fin_cases j <;>
    simp [prespecifiedBatchPauliAxis, QubitOracle.blochNormSq,
      Fin.sum_univ_succ]

theorem prespecifiedBatchAxisFisherMatrix_posSemidef
    (x axis : RLSVector 3)
    (hx : QubitOracle.blochNormSq x < 1)
    (haxis : QubitOracle.blochNormSq axis <= 1) :
    (prespecifiedBatchAxisFisherMatrix x axis).PosSemidef := by
  have habs : |QubitOracle.blochDot x axis| < 1 :=
    lt_of_le_of_lt (abs_blochDot_le_blochNorm x axis haxis)
      (blochNorm_lt_one_of_normSq_lt_one x hx)
  have hden : 0 < 1 - QubitOracle.blochDot x axis ^ 2 := by
    have habs' := abs_lt.mp habs
    have hplus : 0 < 1 + QubitOracle.blochDot x axis := by linarith
    have hminus : 0 < 1 - QubitOracle.blochDot x axis := by linarith
    nlinarith [mul_pos hplus hminus]
  have houter : (Matrix.vecMulVec axis axis).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star axis
  have heq : prespecifiedBatchAxisFisherMatrix x axis =
      (1 - QubitOracle.blochDot x axis ^ 2)⁻¹ •
        Matrix.vecMulVec axis axis := by
    ext i j
    simp [prespecifiedBatchAxisFisherMatrix,
      prespecifiedBatchAxisFisherEntry, Matrix.vecMulVec, div_eq_mul_inv]
    ring
  rw [heq]
  exact houter.smul (le_of_lt (inv_pos.mpr hden))

theorem prespecifiedBatchPilotInformation_posSemidef
    (K : Nat) (x : RLSVector 3)
    (hx : QubitOracle.blochNormSq x < 1) :
    Matrix.PosSemidef ((fun i j => prespecifiedBatchPilotInformation K x i j) :
      Matrix (Fin 3) (Fin 3) Real) := by
  have heq : ((fun i j => prespecifiedBatchPilotInformation K x i j) :
      Matrix (Fin 3) (Fin 3) Real) =
      (∑ k : Fin K, ∑ _r : Fin (exactConcreteBatchPilotBlocks k),
      ∑ axis : Fin 3, prespecifiedBatchAxisFisherMatrix x
        (prespecifiedBatchPauliAxis axis)) := by
    ext i j
    simp only [prespecifiedBatchPilotInformation,
      prespecifiedBatchAxisFisherMatrix, Matrix.sum_apply]
  rw [heq]
  apply Matrix.posSemidef_sum Finset.univ
  intro k hk
  apply Matrix.posSemidef_sum Finset.univ
  intro r hr
  apply Matrix.posSemidef_sum Finset.univ
  intro axis haxis
  exact prespecifiedBatchAxisFisherMatrix_posSemidef x
    (prespecifiedBatchPauliAxis axis) hx
    (le_of_eq (prespecifiedBatchEstimatorPauliAxis_unit axis))

theorem prespecifiedBatchFinalInformation_posSemidef
    (K : Nat) (b x : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K)
    (hx : QubitOracle.blochNormSq x < 1) :
    Matrix.PosSemidef
      ((fun i j => prespecifiedBatchFinalInformation K b x omega i j) :
        Matrix (Fin 3) (Fin 3) Real) := by
  have heq :
      ((fun i j => prespecifiedBatchFinalInformation K b x omega i j) :
        Matrix (Fin 3) (Fin 3) Real) =
      (∑ k : Fin K, ∑ t : Fin (3 * exactConcreteBatchFinalBlocks k),
      prespecifiedBatchAxisFisherMatrix x
        (mixedTwoStageFinalAxis
          (exactConcreteBatchSelectedFrame k b) (omega k).1 t)) := by
    ext i j
    simp only [prespecifiedBatchFinalInformation,
      prespecifiedBatchAxisFisherMatrix, Matrix.sum_apply]
  rw [heq]
  apply Matrix.posSemidef_sum Finset.univ
  intro k hk
  apply Matrix.posSemidef_sum Finset.univ
  intro t ht
  exact prespecifiedBatchAxisFisherMatrix_posSemidef x _ hx
    (le_of_eq (mixedTwoStageFinalAxis_unit
      (exactConcreteBatchSelectedFrame k b) (omega k).1 t))

theorem prespecifiedBatchInformation_posSemidef
    (K : Nat) (b x : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K)
    (hx : QubitOracle.blochNormSq x < 1) :
    (prespecifiedBatchInformation K b x omega).PosSemidef :=
  (prespecifiedBatchPilotInformation_posSemidef K x hx).add
    (prespecifiedBatchFinalInformation_posSemidef K b x omega hx)

theorem prespecifiedBatchNormalizedInformation_posSemidef
    (K : Nat) (b : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K) :
    (prespecifiedBatchNormalizedInformation K b omega).PosSemidef := by
  have hinfo := prespecifiedBatchInformation_posSemidef K b
    (prespecifiedBatchSafeEvaluationPilot K omega) omega
    (prespecifiedBatchSafeEvaluationPilot_strictInterior K omega)
  change ((prespecifiedBatchTotalObservations K : Real)⁻¹ •
    prespecifiedBatchInformation K b
      (prespecifiedBatchSafeEvaluationPilot K omega) omega).PosSemidef
  exact hinfo.smul (by positivity)

theorem prespecifiedBatchRegularizedInformation_posDef
    (K : Nat) (b : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K) :
    (regularizedNormalizedInformation
      (prespecifiedBatchNormalizedInformation K b omega)
      (prespecifiedBatchRidge K)).PosDef := by
  unfold regularizedNormalizedInformation
  exact Matrix.PosDef.posSemidef_add
    (prespecifiedBatchNormalizedInformation_posSemidef K b omega)
    (Matrix.PosDef.one.smul (prespecifiedBatchRidge_pos K))

theorem prespecifiedBatchRegularizedInformation_isUnit
    (K : Nat) (b : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K) :
    IsUnit (regularizedNormalizedInformation
      (prespecifiedBatchNormalizedInformation K b omega)
      (prespecifiedBatchRidge K)) :=
  (prespecifiedBatchRegularizedInformation_posDef K b omega).isUnit

/-- Terminal estimator obtained by radially projecting the literal
ridge-regularized raw one-step update. -/
def prespecifiedBatchProjectedOneStepEstimator (K : Nat) (b : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K) : RLSVector 3 :=
  oneQubitBlochBallRadialClip
    (prespecifiedBatchRawOneStepEstimator K b omega)

/-- The event on which radial projection changes the exterior raw proposal. -/
def prespecifiedBatchRadialClippingEvent (K : Nat) (b : RLSVector 3) :
    Set (ExactConcretePredeterminedBatchPrefix K) :=
  fun omega => 1 < QubitOracle.blochNormSq
    (prespecifiedBatchRawOneStepEstimator K b omega)

theorem prespecifiedBatchProjectedOneStepEstimator_measurable
    (K : Nat) (b : RLSVector 3) :
    Measurable (prespecifiedBatchProjectedOneStepEstimator K b) :=
  measurable_of_finite _

theorem prespecifiedBatchProjectedOneStepEstimator_physical
    (K : Nat) (b : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K) :
    QubitOracle.blochNormSq
      (prespecifiedBatchProjectedOneStepEstimator K b omega) <= 1 :=
  oneQubitBlochBallRadialClip_physical _

theorem prespecifiedBatchProjectedOneStepEstimator_eq_raw_of_physical
    (K : Nat) (b : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K)
    (hphysical : QubitOracle.blochNormSq
      (prespecifiedBatchRawOneStepEstimator K b omega) <= 1) :
    prespecifiedBatchProjectedOneStepEstimator K b omega =
      prespecifiedBatchRawOneStepEstimator K b omega :=
  oneQubitBlochBallRadialClip_eq_self _ hphysical

theorem prespecifiedBatchRadialClippingEvent_measurableSet
    (K : Nat) (b : RLSVector 3) :
    MeasurableSet (prespecifiedBatchRadialClippingEvent K b) :=
  MeasurableSet.of_discrete

/-- At a fixed strict-interior truth, clipping can happen only after the raw
proposal incurs at least the fixed squared-radius gap. -/
theorem prespecifiedBatchRadialClippingEvent_implies_rawRadiusError
    (K : Nat) (b theta : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hclip : omega ∈ prespecifiedBatchRadialClippingEvent K b) :
    1 - QubitOracle.blochNormSq theta <
      abs (QubitOracle.blochNormSq
        (prespecifiedBatchRawOneStepEstimator K b omega) -
          QubitOracle.blochNormSq theta) := by
  have hraw : 1 < QubitOracle.blochNormSq
      (prespecifiedBatchRawOneStepEstimator K b omega) := by
    change (fun omega : ExactConcretePredeterminedBatchPrefix K =>
      1 < QubitOracle.blochNormSq
        (prespecifiedBatchRawOneStepEstimator K b omega)) omega at hclip
    exact hclip
  have hdiff : 0 < QubitOracle.blochNormSq
      (prespecifiedBatchRawOneStepEstimator K b omega) -
        QubitOracle.blochNormSq theta := by
    linarith
  rw [abs_of_pos hdiff]
  linarith

/-- Strong vector-error form of the clipping margin.  The numerical constant
`7` is a conservative finite-dimensional bound; importantly, the margin is
strictly positive and independent of `K` and the observed prefix. -/
theorem prespecifiedBatchRadialClippingEvent_implies_rawBlochError
    (K : Nat) (b theta : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hclip : omega ∈ prespecifiedBatchRadialClippingEvent K b) :
    ((1 - QubitOracle.blochNormSq theta) / 7) ^ 2 <
      QubitOracle.blochNormSq (fun i =>
        prespecifiedBatchRawOneStepEstimator K b omega i - theta i) := by
  let raw := prespecifiedBatchRawOneStepEstimator K b omega
  let gap := 1 - QubitOracle.blochNormSq theta
  let delta := gap / 7
  have hgap : 0 < gap := by
    dsimp [gap]
    linarith
  have hgap_le : gap <= 1 := by
    dsimp [gap]
    have hnorm_nonneg : 0 <= QubitOracle.blochNormSq theta := by
      unfold QubitOracle.blochNormSq
      positivity
    linarith
  have hraw : 1 < QubitOracle.blochNormSq raw := by
    have hclip' := hclip
    change (fun omega : ExactConcretePredeterminedBatchPrefix K =>
      1 < QubitOracle.blochNormSq
        (prespecifiedBatchRawOneStepEstimator K b omega)) omega at hclip'
    simpa [raw] using hclip'
  by_contra herror
  have herr : QubitOracle.blochNormSq (fun i => raw i - theta i) <=
      delta ^ 2 := by
    exact le_of_not_gt (by simpa [raw, gap, delta] using herror)
  have htheta_coord (i : Fin 3) :
      theta i ^ 2 <= QubitOracle.blochNormSq theta := by
    unfold QubitOracle.blochNormSq
    exact Finset.single_le_sum (fun j _ => sq_nonneg (theta j))
      (Finset.mem_univ i)
  have htheta0 := htheta_coord 0
  have htheta1 := htheta_coord 1
  have htheta2 := htheta_coord 2
  have hdelta : 0 <= delta := le_of_lt (div_pos hgap (by norm_num))
  have he0sq : (raw 0 - theta 0) ^ 2 <= delta ^ 2 := by
    have := herr
    simp [QubitOracle.blochNormSq, Fin.sum_univ_succ] at this
    nlinarith [sq_nonneg (raw 1 - theta 1), sq_nonneg (raw 2 - theta 2)]
  have he1sq : (raw 1 - theta 1) ^ 2 <= delta ^ 2 := by
    have := herr
    simp [QubitOracle.blochNormSq, Fin.sum_univ_succ] at this
    nlinarith [sq_nonneg (raw 0 - theta 0), sq_nonneg (raw 2 - theta 2)]
  have he2sq : (raw 2 - theta 2) ^ 2 <= delta ^ 2 := by
    have := herr
    simp [QubitOracle.blochNormSq, Fin.sum_univ_succ] at this
    nlinarith [sq_nonneg (raw 0 - theta 0), sq_nonneg (raw 1 - theta 1)]
  have hcoord0 : raw 0 ^ 2 <= theta 0 ^ 2 + 2 * delta + delta ^ 2 := by
    have htheta_sq : theta 0 ^ 2 < 1 := lt_of_le_of_lt htheta0 hInterior
    nlinarith
  have hcoord1 : raw 1 ^ 2 <= theta 1 ^ 2 + 2 * delta + delta ^ 2 := by
    have htheta_sq : theta 1 ^ 2 < 1 := lt_of_le_of_lt htheta1 hInterior
    nlinarith
  have hcoord2 : raw 2 ^ 2 <= theta 2 ^ 2 + 2 * delta + delta ^ 2 := by
    have htheta_sq : theta 2 ^ 2 < 1 := lt_of_le_of_lt htheta2 hInterior
    nlinarith
  have hraw_bound : QubitOracle.blochNormSq raw <=
      QubitOracle.blochNormSq theta + 6 * delta + 3 * delta ^ 2 := by
    simp [QubitOracle.blochNormSq, Fin.sum_univ_succ] at hcoord0 hcoord1 hcoord2 ⊢
    linarith
  have hdelta_bound : 6 * delta + 3 * delta ^ 2 < gap := by
    dsimp [delta]
    nlinarith [sq_nonneg gap]
  linarith

/-- Acceptance requires both the algebraic Hessian safeguard and physicality
of the proposed update. -/
def prespecifiedBatchAccept (K : Nat) (b : RLSVector 3) :
    Set (ExactConcretePredeterminedBatchPrefix K) :=
  {omega |
    (regularizedNormalizedInformation
      (prespecifiedBatchNormalizedInformation K b omega)
      (prespecifiedBatchRidge K)).PosDef /\
    QubitOracle.blochNormSq
      (prespecifiedBatchRawOneStepEstimator K b omega) <= 1}

/-- Implemented safeguarded estimator.  The rejected branch is the maximally
mixed state `0`, which is always physical. -/
def prespecifiedBatchSafeguardedEstimator (K : Nat) (b : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K) : RLSVector 3 := by
  classical
  exact if omega ∈ prespecifiedBatchAccept K b then
      prespecifiedBatchRawOneStepEstimator K b omega
    else
      0

/-! ## Finite-space measurability -/

theorem prespecifiedBatchPooledPilot_measurable (K : Nat) :
    Measurable (prespecifiedBatchPooledPilot K) :=
  measurable_of_finite _

theorem prespecifiedBatchScore_measurable (K : Nat) (b x : RLSVector 3) :
    Measurable (prespecifiedBatchScore K b x) :=
  measurable_of_finite _

theorem prespecifiedBatchNormalizedInformation_entry_measurable
    (K : Nat) (b : RLSVector 3) (i j : Fin 3) :
    Measurable (fun omega =>
      prespecifiedBatchNormalizedInformation K b omega i j) :=
  measurable_of_finite _

theorem prespecifiedBatchAccept_measurableSet (K : Nat) (b : RLSVector 3) :
    MeasurableSet (prespecifiedBatchAccept K b) :=
  MeasurableSet.of_discrete

theorem prespecifiedBatchSafeguardedEstimator_measurable
    (K : Nat) (b : RLSVector 3) :
    Measurable (prespecifiedBatchSafeguardedEstimator K b) :=
  measurable_of_finite _

/-! ## Deterministic safeguard identities -/

theorem prespecifiedBatchSafeguardedEstimator_eq_raw_of_accept
    (K : Nat) (b : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K)
    (haccept : omega ∈ prespecifiedBatchAccept K b) :
    prespecifiedBatchSafeguardedEstimator K b omega =
      prespecifiedBatchRawOneStepEstimator K b omega := by
  simp [prespecifiedBatchSafeguardedEstimator, haccept]

theorem prespecifiedBatchSafeguardedEstimator_eq_zero_of_reject
    (K : Nat) (b : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K)
    (hreject : omega ∉ prespecifiedBatchAccept K b) :
    prespecifiedBatchSafeguardedEstimator K b omega = 0 := by
  simp [prespecifiedBatchSafeguardedEstimator, hreject]

theorem prespecifiedBatchAccept_regularizedInformation_posDef
    (K : Nat) (b : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K)
    (haccept : omega ∈ prespecifiedBatchAccept K b) :
    (regularizedNormalizedInformation
      (prespecifiedBatchNormalizedInformation K b omega)
      (prespecifiedBatchRidge K)).PosDef :=
  haccept.1

theorem prespecifiedBatchSafeguardedEstimator_physical
    (K : Nat) (b : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K) :
    QubitOracle.blochNormSq
      (prespecifiedBatchSafeguardedEstimator K b omega) <= 1 := by
  by_cases haccept : omega ∈ prespecifiedBatchAccept K b
  · rw [prespecifiedBatchSafeguardedEstimator_eq_raw_of_accept K b omega haccept]
    exact haccept.2
  · rw [prespecifiedBatchSafeguardedEstimator_eq_zero_of_reject K b omega haccept]
    simp [QubitOracle.blochNormSq]

/-! ## Exact one-step/Newton algebra -/

/-- The raw normalized error written in the common one-step algebra API. -/
def prespecifiedBatchRawNormalizedError (K : Nat) (b theta : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K) : LANParameter (Fin 3) :=
  normalizedRegularizedOneStepError
    (prespecifiedBatchLANVector fun i => prespecifiedBatchSampleScale K *
      (prespecifiedBatchPooledPilot K omega i - theta i))
    (prespecifiedBatchNormalizedScore K b omega)
    (prespecifiedBatchNormalizedInformation K b omega)
    (prespecifiedBatchRidge K)

/-- The abstract normalized one-step error is exactly the scaled error of the
actual raw statistic whenever the completed prefix has nonzero sample scale. -/
theorem prespecifiedBatchRawOneStepEstimator_scaledError
    (K : Nat) (b theta : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K)
    (hscale : prespecifiedBatchSampleScale K ≠ 0) :
    prespecifiedBatchLANVector
        (fun i => prespecifiedBatchSampleScale K *
          (prespecifiedBatchRawOneStepEstimator K b omega i - theta i)) =
      prespecifiedBatchRawNormalizedError K b theta omega := by
  ext i
  simp only [prespecifiedBatchRawNormalizedError,
    normalizedRegularizedOneStepError, prespecifiedBatchLANVector_apply,
    PiLp.add_apply]
  dsimp [prespecifiedBatchRawOneStepEstimator]
  field_simp [hscale]
  ring

/-- Exact Newton cancellation for the concrete prefix statistics. -/
theorem prespecifiedBatchRawNormalizedError_exact
    (K : Nat) (b theta : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K)
    (centralScore : LANParameter (Fin 3))
    (hA :
      (regularizedNormalizedInformation
        (prespecifiedBatchNormalizedInformation K b omega)
        (prespecifiedBatchRidge K)).PosDef) :
    prespecifiedBatchRawNormalizedError K b theta omega -
        lanMatrixAction
          (regularizedNormalizedInformation
            (prespecifiedBatchNormalizedInformation K b omega)
            (prespecifiedBatchRidge K))⁻¹ centralScore =
      lanMatrixAction
        (regularizedNormalizedInformation
          (prespecifiedBatchNormalizedInformation K b omega)
          (prespecifiedBatchRidge K))⁻¹
        (normalizedNewtonDefect
          (prespecifiedBatchLANVector fun i => prespecifiedBatchSampleScale K *
            (prespecifiedBatchPooledPilot K omega i - theta i))
          (prespecifiedBatchNormalizedScore K b omega)
          centralScore
          (prespecifiedBatchNormalizedInformation K b omega)
          (prespecifiedBatchRidge K)) := by
  exact normalizedRegularizedOneStepError_exact
    (prespecifiedBatchLANVector fun i => prespecifiedBatchSampleScale K *
      (prespecifiedBatchPooledPilot K omega i - theta i))
    (prespecifiedBatchNormalizedScore K b omega)
    centralScore
    (prespecifiedBatchNormalizedInformation K b omega)
    (prespecifiedBatchRidge K) hA

/-- Exact Newton cancellation for every finite prefix, with no safeguard or
invertibility premise: positive ridge plus pathwise positive semidefiniteness
supplies positive definiteness unconditionally. -/
theorem prespecifiedBatchRawNormalizedError_exact_unconditional
    (K : Nat) (b theta : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K)
    (centralScore : LANParameter (Fin 3)) :
    prespecifiedBatchRawNormalizedError K b theta omega -
        lanMatrixAction
          (regularizedNormalizedInformation
            (prespecifiedBatchNormalizedInformation K b omega)
            (prespecifiedBatchRidge K))⁻¹ centralScore =
      lanMatrixAction
        (regularizedNormalizedInformation
          (prespecifiedBatchNormalizedInformation K b omega)
          (prespecifiedBatchRidge K))⁻¹
        (normalizedNewtonDefect
          (prespecifiedBatchLANVector fun i => prespecifiedBatchSampleScale K *
            (prespecifiedBatchPooledPilot K omega i - theta i))
          (prespecifiedBatchNormalizedScore K b omega)
          centralScore
          (prespecifiedBatchNormalizedInformation K b omega)
          (prespecifiedBatchRidge K)) :=
  prespecifiedBatchRawNormalizedError_exact K b theta omega centralScore
    (prespecifiedBatchRegularizedInformation_posDef K b omega)

/-- On an accepted prefix, the same exact cancellation is available with the
positive-definiteness proof supplied by the implemented safeguard. -/
theorem prespecifiedBatchRawNormalizedError_exact_of_accept
    (K : Nat) (b theta : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K)
    (centralScore : LANParameter (Fin 3))
    (haccept : omega ∈ prespecifiedBatchAccept K b) :
    prespecifiedBatchRawNormalizedError K b theta omega -
        lanMatrixAction
          (regularizedNormalizedInformation
            (prespecifiedBatchNormalizedInformation K b omega)
            (prespecifiedBatchRidge K))⁻¹ centralScore =
      lanMatrixAction
        (regularizedNormalizedInformation
          (prespecifiedBatchNormalizedInformation K b omega)
          (prespecifiedBatchRidge K))⁻¹
        (normalizedNewtonDefect
          (prespecifiedBatchLANVector fun i => prespecifiedBatchSampleScale K *
            (prespecifiedBatchPooledPilot K omega i - theta i))
          (prespecifiedBatchNormalizedScore K b omega)
          centralScore
          (prespecifiedBatchNormalizedInformation K b omega)
          (prespecifiedBatchRidge K)) :=
  prespecifiedBatchRawNormalizedError_exact K b theta omega centralScore
    (prespecifiedBatchAccept_regularizedInformation_posDef K b omega haccept)

end

end QubitOracle.Paper
