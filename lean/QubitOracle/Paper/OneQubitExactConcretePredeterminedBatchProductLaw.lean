import QubitOracle.Paper.OneQubitExactConcretePredeterminedBatchProtocol
import Mathlib.Probability.ProductMeasure

/-!
# Common product law for the exact predetermined-batch protocol

The finite protocol module proves the normalized Born law of each batch
separately.  This module puts every exact pilot-plus-exploitation batch on one
common probability space.  Batch coordinates are independent, while the final
measurements inside each coordinate retain their exact dependence on that
batch's completed pilot.

The controller below is the literal sample mean of the pilot contained in the
same finite Born row.  Its concentration is transferred through two
kernel-proved marginal identities and Mathlib's Hoeffding theorem.  No
protocol-specific convergence axiom is introduced.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section

attribute [local instance]
  pauliPilotBornPathMeasurableSpace
  mixedTwoStageFiniteRowMeasurableSpace
  mixedTwoStageFiniteRowMeasurableSingletonClass

/-- The complete data in batch `k`: its Pauli pilot and all final outcomes. -/
abbrev ExactConcretePredeterminedBatchRow (k : Nat) : Type :=
  MixedTwoStageFiniteRow
    (exactConcreteBatchPilotBlocks k)
    (3 * exactConcreteBatchFinalBlocks k)

/-- One common sample contains every predetermined batch. -/
abbrev ExactConcretePredeterminedBatchPath : Type :=
  (k : Nat) -> ExactConcretePredeterminedBatchRow k

/-- Exact normalized Born law of batch `k`. -/
def exactConcretePredeterminedBatchRowMeasure
    (theta b : RLSVector 3) (k : Nat) :
    Measure (ExactConcretePredeterminedBatchRow k) :=
  mixedTwoStageFiniteBornMeasure
    (T := 3 * exactConcreteBatchFinalBlocks k)
    theta (exactConcreteBatchSelectedFrame k b)

/-- Every physical truth normalizes every exact batch row. -/
theorem exactConcretePredeterminedBatchRowMeasure_isProbability
    (theta b : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (k : Nat) :
    IsProbabilityMeasure
      (exactConcretePredeterminedBatchRowMeasure theta b k) :=
  ⟨mixedTwoStageFiniteBornMeasure_univ
    theta (exactConcreteBatchSelectedFrame k b) hphysical⟩

/-- Infinite product of all exact batch-row Born laws. -/
def exactConcretePredeterminedBatchPathMeasure
    (theta b : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta) :
    Measure ExactConcretePredeterminedBatchPath := by
  letI : forall k : Nat,
      IsProbabilityMeasure
        (exactConcretePredeterminedBatchRowMeasure theta b k) :=
    fun k =>
      exactConcretePredeterminedBatchRowMeasure_isProbability
        theta b hphysical k
  exact Measure.infinitePi
    (fun k => exactConcretePredeterminedBatchRowMeasure theta b k)

/-- The common path law is a probability measure. -/
theorem exactConcretePredeterminedBatchPathMeasure_isProbability
    (theta b : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta) :
    IsProbabilityMeasure
      (exactConcretePredeterminedBatchPathMeasure theta b hphysical) := by
  letI : forall k : Nat,
      IsProbabilityMeasure
        (exactConcretePredeterminedBatchRowMeasure theta b k) :=
    fun k =>
      exactConcretePredeterminedBatchRowMeasure_isProbability
        theta b hphysical k
  change IsProbabilityMeasure
    (Measure.infinitePi
      (fun k => exactConcretePredeterminedBatchRowMeasure theta b k))
  infer_instance

/-- Evaluating the common path at batch `k` recovers its exact finite Born law. -/
theorem exactConcretePredeterminedBatchPathMeasure_map_eval
    (theta b : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (k : Nat) :
    (exactConcretePredeterminedBatchPathMeasure theta b hphysical).map
        (Function.eval k) =
      exactConcretePredeterminedBatchRowMeasure theta b k := by
  letI : forall t : Nat,
      IsProbabilityMeasure
        (exactConcretePredeterminedBatchRowMeasure theta b t) :=
    fun t =>
      exactConcretePredeterminedBatchRowMeasure_isProbability
        theta b hphysical t
  change
    (Measure.infinitePi
      (fun t => exactConcretePredeterminedBatchRowMeasure theta b t)).map
        (Function.eval k) =
      exactConcretePredeterminedBatchRowMeasure theta b k
  exact Measure.infinitePi_map_eval _ k

/-- The pilot marginal of one exact batch row is the original finite Pauli
Born product law. -/
theorem exactConcretePredeterminedBatchRowMeasure_map_pilot
    (theta b : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (k : Nat) :
    (exactConcretePredeterminedBatchRowMeasure theta b k).map
        (fun row => row.1) =
      pauliPilotBornProductMeasure
        (q := exactConcreteBatchPilotBlocks k) theta := by
  ext event hevent
  rw [Measure.map_apply (by fun_prop) hevent]
  exact mixedTwoStageFiniteBornMeasure_pilotMarginal
    theta (exactConcreteBatchSelectedFrame k b) hphysical event

/-- Consequently, the pilot extracted from batch `k` on the common path has
exactly the finite Born product law of its prescribed size. -/
theorem exactConcretePredeterminedBatchPathMeasure_map_batchPilot
    (theta b : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (k : Nat) :
    (exactConcretePredeterminedBatchPathMeasure theta b hphysical).map
        (fun omega => (omega k).1) =
      pauliPilotBornProductMeasure
        (q := exactConcreteBatchPilotBlocks k) theta := by
  calc
    (exactConcretePredeterminedBatchPathMeasure theta b hphysical).map
        (fun omega => (omega k).1) =
      ((exactConcretePredeterminedBatchPathMeasure theta b hphysical).map
        (Function.eval k)).map (fun row => row.1) := by
          rw [Measure.map_map]
          · rfl
          · fun_prop
          · fun_prop
    _ = pauliPilotBornProductMeasure
          (q := exactConcreteBatchPilotBlocks k) theta := by
      rw [exactConcretePredeterminedBatchPathMeasure_map_eval
          theta b hphysical k,
        exactConcretePredeterminedBatchRowMeasure_map_pilot
          theta b hphysical k]

/-- Restricting the common law to the first `K` coordinates gives the exact
finite dependent product of the first `K` Born row laws. -/
theorem exactConcretePredeterminedBatchPathMeasure_map_prefix
    (theta b : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (K : Nat) :
    (exactConcretePredeterminedBatchPathMeasure theta b hphysical).map
        (Finset.range K).restrict =
      Measure.pi (fun k : Finset.range K =>
        exactConcretePredeterminedBatchRowMeasure theta b k.1) := by
  letI : forall t : Nat,
      IsProbabilityMeasure
        (exactConcretePredeterminedBatchRowMeasure theta b t) :=
    fun t =>
      exactConcretePredeterminedBatchRowMeasure_isProbability
        theta b hphysical t
  change
    (Measure.infinitePi
      (fun t => exactConcretePredeterminedBatchRowMeasure theta b t)).map
        (Finset.range K).restrict =
      Measure.pi (fun k : Finset.range K =>
        exactConcretePredeterminedBatchRowMeasure theta b k.1)
  exact Measure.infinitePi_map_restrict
    (fun t => exactConcretePredeterminedBatchRowMeasure theta b t)

/-- Actual batch controller on the common Born path. -/
def exactConcretePredeterminedBatchPathController
    (k : Nat) (omega : ExactConcretePredeterminedBatchPath) :
    RLSVector 3 :=
  pauliPilotEstimate (omega k).1

/-- One coordinate of the actual common-path controller has the exact
Hoeffding envelope associated with that batch's pilot size. -/
theorem exactConcretePredeterminedBatchPathController_coordinate_tail
    (theta b : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (k : Nat) (j : Fin 3) (epsilon : Real) (hepsilon : 0 < epsilon) :
    exactConcretePredeterminedBatchPathMeasure theta b hphysical
        {omega |
          epsilon <=
            |exactConcretePredeterminedBatchPathController k omega j -
              theta j|} <=
      pauliPilotCoordinateHoeffdingEnvelope
        (exactConcreteBatchPilotIndex k) epsilon := by
  have hHoeffding :
      PauliPilotBornTwoSidedHoeffdingTheorem2Contract
        (exactConcreteBatchPilotBlocks_pos k) theta hphysical j :=
    ⟨hoeffding1963UniversalTheorem2_of_mathlib _ _ _ _,
      hoeffding1963UniversalTheorem2_of_mathlib _ _ _ _⟩
  have hfinite :=
    pauliPilotBorn_twoSidedTail_of_hoeffding2
      (exactConcreteBatchPilotBlocks_pos k) theta hphysical j
      hHoeffding epsilon hepsilon
  calc
    exactConcretePredeterminedBatchPathMeasure theta b hphysical
        {omega |
          epsilon <=
            |exactConcretePredeterminedBatchPathController k omega j -
              theta j|} =
      pauliPilotBornProductMeasure
          (q := exactConcreteBatchPilotBlocks k) theta
        {pilot | epsilon <= |pauliPilotEstimate pilot j - theta j|} := by
          rw [← exactConcretePredeterminedBatchPathMeasure_map_batchPilot
            theta b hphysical k]
          rw [Measure.map_apply (by fun_prop) MeasurableSet.of_discrete]
          rfl
    _ <= 2 * ENNReal.ofReal
        (Real.exp (-(exactConcreteBatchPilotBlocks k : Real) *
          epsilon ^ 2 / 2)) := hfinite
    _ = pauliPilotCoordinateHoeffdingEnvelope
        (exactConcreteBatchPilotIndex k) epsilon := by
      rw [← exactConcreteBatchPilotIndex_succ k]
      simp only [pauliPilotCoordinateHoeffdingEnvelope, Nat.cast_succ]
      congr 3 <;> ring

/-- Simultaneous three-coordinate concentration of the actual controller on
the common exact Born path. -/
theorem exactConcretePredeterminedBatchPathController_finite_tail
    (theta b : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (k : Nat) (epsilon : Real) (hepsilon : 0 < epsilon) :
    exactConcretePredeterminedBatchPathMeasure theta b hphysical
        (QubitOracle.coordinateDeltaBadEvent
          exactConcretePredeterminedBatchPathController theta k epsilon) <=
      pauliPilotFiniteHoeffdingEnvelope
        (exactConcreteBatchPilotIndex k) epsilon := by
  calc
    exactConcretePredeterminedBatchPathMeasure theta b hphysical
        (QubitOracle.coordinateDeltaBadEvent
          exactConcretePredeterminedBatchPathController theta k epsilon) <=
      ∑ j : Fin 3,
        exactConcretePredeterminedBatchPathMeasure theta b hphysical
          {omega |
            epsilon <=
              |exactConcretePredeterminedBatchPathController k omega j -
                theta j|} :=
      QubitOracle.measure_coordinateDeltaBadEvent_le_finset_sum
        (exactConcretePredeterminedBatchPathMeasure theta b hphysical)
        exactConcretePredeterminedBatchPathController theta k epsilon
    _ <= ∑ _j : Fin 3,
        pauliPilotCoordinateHoeffdingEnvelope
          (exactConcreteBatchPilotIndex k) epsilon := by
      exact Finset.sum_le_sum fun j _ =>
        exactConcretePredeterminedBatchPathController_coordinate_tail
          theta b hphysical k j epsilon hepsilon
    _ = pauliPilotFiniteHoeffdingEnvelope
        (exactConcreteBatchPilotIndex k) epsilon := by
      simp [pauliPilotFiniteHoeffdingEnvelope, Fin.sum_univ_succ]

/-- The literal controller read from the common Born path converges jointly in
all three coordinates in probability. -/
theorem exactConcretePredeterminedBatchPathController_convergesInProbability
    (theta b : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta) :
    forall epsilon : Real, 0 < epsilon ->
      Tendsto
        (fun k =>
          exactConcretePredeterminedBatchPathMeasure theta b hphysical
            (QubitOracle.coordinateDeltaBadEvent
              exactConcretePredeterminedBatchPathController theta k epsilon))
        atTop (nhds 0) := by
  intro epsilon hepsilon
  have hEnvelope :=
    (pauliPilotFiniteHoeffdingEnvelope_tendsto_zero epsilon hepsilon).comp
      exactConcreteBatchPilotIndex_tendsto_atTop
  exact Tendsto.squeeze tendsto_const_nhds hEnvelope
    (fun _ => bot_le)
    (fun k =>
      exactConcretePredeterminedBatchPathController_finite_tail
        theta b hphysical k epsilon hepsilon)

/-- Kernel-checked common-law closure: exact finite prefixes and actual
controller convergence now live on the same probability space. -/
theorem exactConcretePredeterminedBatch_commonBornProduct_closed
    (theta b : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta) :
    IsProbabilityMeasure
        (exactConcretePredeterminedBatchPathMeasure theta b hphysical) /\
      (forall K,
        (exactConcretePredeterminedBatchPathMeasure theta b hphysical).map
            (Finset.range K).restrict =
          Measure.pi (fun k : Finset.range K =>
            exactConcretePredeterminedBatchRowMeasure theta b k.1)) /\
      (forall epsilon : Real, 0 < epsilon ->
        Tendsto
          (fun k =>
            exactConcretePredeterminedBatchPathMeasure theta b hphysical
              (QubitOracle.coordinateDeltaBadEvent
                exactConcretePredeterminedBatchPathController theta k epsilon))
          atTop (nhds 0)) := by
  exact
    ⟨exactConcretePredeterminedBatchPathMeasure_isProbability
        theta b hphysical,
      exactConcretePredeterminedBatchPathMeasure_map_prefix
        theta b hphysical,
      exactConcretePredeterminedBatchPathController_convergesInProbability
        theta b hphysical⟩

end

end QubitOracle.Paper
