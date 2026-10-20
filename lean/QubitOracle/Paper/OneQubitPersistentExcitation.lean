import QubitOracle.Paper.OneQubitRLSConfidenceReduction
import QubitOracle.Paper.QubitFoundations

/-!
# Concrete persistent excitation from Pauli exploration blocks

This module specializes persistent excitation to a deterministic one-qubit
controller.  One forced-exploration block measures each of the three Pauli
axes exactly once.  After `blocks` complete blocks there are `3 * blocks`
forced rounds, every coordinate axis has count `blocks`, and the empirical
Gram matrix is exactly `blocks` times the identity.

The RLS conclusions are deterministic.  A self-normalized confidence bound is
an explicit premise; no probabilistic conclusion of
Abbasi-Yadkori--Pal--Szepesvari is claimed here.
-/

namespace QubitOracle.Paper

open Filter
open scoped BigOperators Topology

noncomputable section

/-! ## Deterministic Pauli controller -/

/-- The Pauli coordinate axis indexed by `slot : Fin 3`. -/
def pauliCoordinateAxis (slot : Fin 3) : Fin 3 -> Real :=
  fun coordinate => if coordinate = slot then 1 else 0

/-- A complete forced-exploration block uses the three Pauli axes in the
fixed order `0, 1, 2`.  The block index does not change the selected axis. -/
def pauliForcedExplorationAxis
    (_block : Nat) (slot : Fin 3) : Fin 3 -> Real :=
  pauliCoordinateAxis slot

/-- Every coordinate Pauli axis is a unit Bloch axis. -/
@[simp]
theorem pauliCoordinateAxis_unit (slot : Fin 3) :
    QubitOracle.blochNormSq (pauliCoordinateAxis slot) = 1 := by
  classical
  simp [QubitOracle.blochNormSq, pauliCoordinateAxis]

/-- Consequently every forced-exploration choice is a unit axis. -/
@[simp]
theorem pauliForcedExplorationAxis_unit
    (block : Nat) (slot : Fin 3) :
    QubitOracle.blochNormSq
      (pauliForcedExplorationAxis block slot) = 1 := by
  exact pauliCoordinateAxis_unit slot

/-- Number of chronological forced-exploration rounds in `blocks` complete
three-axis blocks. -/
def pauliForcedExplorationRoundCount (blocks : Nat) : Nat :=
  3 * blocks

/-- The excitation count `blocks` is exactly one third of the total number of
forced rounds, in real arithmetic. -/
theorem pauliBlocks_eq_roundCount_div_three (blocks : Nat) :
    (blocks : Real) =
      (pauliForcedExplorationRoundCount blocks : Real) / 3 := by
  simp [pauliForcedExplorationRoundCount]

/-! ## Explicit empirical Gram matrix -/

/-- Gram contribution of one complete Pauli exploration block. -/
def pauliForcedOneBlockGram : Matrix (Fin 3) (Fin 3) Real :=
  fun i j => ∑ slot : Fin 3,
    pauliCoordinateAxis slot i * pauliCoordinateAxis slot j

/-- One full Pauli block contributes the identity matrix. -/
theorem pauliForcedOneBlockGram_entry (i j : Fin 3) :
    pauliForcedOneBlockGram i j = if i = j then 1 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simp [pauliForcedOneBlockGram, pauliCoordinateAxis]
  · simp [pauliForcedOneBlockGram, pauliCoordinateAxis, hij]

/-- Empirical Gram matrix of all `3 * blocks` forced-exploration observations.
The outer sum is over blocks and the inner Gram contribution contains the
three Pauli axes. -/
def pauliForcedExplorationGram
    (blocks : Nat) : Matrix (Fin 3) (Fin 3) Real :=
  fun i j => ∑ _block : Fin blocks, pauliForcedOneBlockGram i j

/-- The definition is literally the sum of the rank-one axis contributions. -/
theorem pauliForcedExplorationGram_eq_axis_sum
    (blocks : Nat) (i j : Fin 3) :
    pauliForcedExplorationGram blocks i j =
      ∑ block : Fin blocks, ∑ slot : Fin 3,
        pauliForcedExplorationAxis block slot i *
          pauliForcedExplorationAxis block slot j := by
  rfl

/-- Exact diagonal/count formula: each Pauli coordinate appears `blocks`
times, and all off-diagonal entries vanish. -/
theorem pauliForcedExplorationGram_entry
    (blocks : Nat) (i j : Fin 3) :
    pauliForcedExplorationGram blocks i j =
      if i = j then (blocks : Real) else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simp [pauliForcedExplorationGram, pauliForcedOneBlockGram_entry]
  · simp [pauliForcedExplorationGram, pauliForcedOneBlockGram_entry, hij]

/-- Diagonal count form of the empirical Gram identity. -/
theorem pauliForcedExplorationGram_diagonal
    (blocks : Nat) (i : Fin 3) :
    pauliForcedExplorationGram blocks i i = (blocks : Real) := by
  simp [pauliForcedExplorationGram_entry]

/-- Distinct Pauli coordinates have zero empirical cross-count. -/
theorem pauliForcedExplorationGram_offDiagonal
    (blocks : Nat) (i j : Fin 3) (hij : i ≠ j) :
    pauliForcedExplorationGram blocks i j = 0 := by
  simp [pauliForcedExplorationGram_entry, hij]

/-- Exact quadratic-form identity: the empirical Gram energy is `blocks`
times squared Euclidean Bloch norm. -/
theorem oneQubitGramEnergy_pauliForcedExplorationGram
    (blocks : Nat) (x : Fin 3 -> Real) :
    oneQubitGramEnergy (pauliForcedExplorationGram blocks) x =
      (blocks : Real) * QubitOracle.blochNormSq x := by
  simp [oneQubitGramEnergy, QubitOracle.blochDot, Matrix.mulVec,
    dotProduct, pauliForcedExplorationGram_entry,
    QubitOracle.blochNormSq, Fin.sum_univ_succ]
  ring

/-- Euclidean coercivity with the exact lower bound `blocks`, equivalently one
third of the forced-round count. -/
theorem pauliForcedExplorationGram_euclidean_coercive
    (blocks : Nat) (x : Fin 3 -> Real) :
    (blocks : Real) * QubitOracle.blochNormSq x <=
      oneQubitGramEnergy (pauliForcedExplorationGram blocks) x := by
  rw [oneQubitGramEnergy_pauliForcedExplorationGram]

/-- Concrete instantiation of the persistent-excitation contract for every
nonempty collection of complete Pauli blocks. -/
theorem pauliForcedExploration_persistentExcitation
    (blocks : Nat) (hblocks : 0 < blocks) :
    OneQubitPersistentExcitation
      (pauliForcedExplorationGram blocks) (blocks : Real) := by
  constructor
  · exact_mod_cast hblocks
  · intro x
    exact pauliForcedExplorationGram_euclidean_coercive blocks x

/-! ## Deterministic RLS rate -/

/-- A supplied self-normalized confidence ellipsoid for the concrete Pauli
Gram gives the exact squared Euclidean error bound `radius^2 / blocks`. -/
theorem pauliForcedExploration_RLSSquaredError_le
    (blocks : Nat) (hblocks : 0 < blocks)
    (estimate truth : Fin 3 -> Real) (radius : Real)
    (hConfidence : OneQubitSelfNormalizedConfidence
      (pauliForcedExplorationGram blocks) estimate truth radius) :
    QubitOracle.blochNormSq (oneQubitRLSError estimate truth) <=
      radius ^ 2 / (blocks : Real) := by
  exact oneQubitRLSSquaredEuclideanError_le
    (pauliForcedExplorationGram blocks) estimate truth radius (blocks : Real)
      hConfidence
      (pauliForcedExploration_persistentExcitation blocks hblocks)

/-- Euclidean form of the concrete confidence-to-error reduction. -/
theorem pauliForcedExploration_RLSEuclideanError_le
    (blocks : Nat) (hblocks : 0 < blocks)
    (estimate truth : Fin 3 -> Real) (radius : Real)
    (hConfidence : OneQubitSelfNormalizedConfidence
      (pauliForcedExplorationGram blocks) estimate truth radius) :
    PopularRLSConditions.finiteEuclideanNorm
        (oneQubitRLSError estimate truth) <=
      Real.sqrt (radius ^ 2 / (blocks : Real)) := by
  exact oneQubitRLSEuclideanError_le
    (pauliForcedExplorationGram blocks) estimate truth radius (blocks : Real)
      hConfidence
      (pauliForcedExploration_persistentExcitation blocks hblocks)

/-- Explicit logarithmic deterministic rate.  The premise
`radius^2 <= C^2 log(3 blocks + 1)` is the squared form of
`radius = O(sqrt(log n))` at complete-block endpoints `n = 3 blocks`. -/
theorem pauliForcedExploration_RLSSquaredError_logRate
    (blocks : Nat) (hblocks : 0 < blocks)
    (estimate truth : Fin 3 -> Real) (radius C : Real)
    (hConfidence : OneQubitSelfNormalizedConfidence
      (pauliForcedExplorationGram blocks) estimate truth radius)
    (hRadiusSq : radius ^ 2 <=
      C ^ 2 * Real.log
        ((pauliForcedExplorationRoundCount blocks : Real) + 1)) :
    QubitOracle.blochNormSq (oneQubitRLSError estimate truth) <=
      C ^ 2 * Real.log
        ((pauliForcedExplorationRoundCount blocks : Real) + 1) /
          (blocks : Real) := by
  have hblocksReal : 0 < (blocks : Real) := by exact_mod_cast hblocks
  calc
    QubitOracle.blochNormSq (oneQubitRLSError estimate truth) <=
        radius ^ 2 / (blocks : Real) :=
      pauliForcedExploration_RLSSquaredError_le
        blocks hblocks estimate truth radius hConfidence
    _ <= (C ^ 2 * Real.log
        ((pauliForcedExplorationRoundCount blocks : Real) + 1)) /
          (blocks : Real) :=
      (div_le_div_iff_of_pos_right hblocksReal).2 hRadiusSq

/-- Euclidean version of the explicit logarithmic rate. -/
theorem pauliForcedExploration_RLSEuclideanError_logRate
    (blocks : Nat) (hblocks : 0 < blocks)
    (estimate truth : Fin 3 -> Real) (radius C : Real)
    (hConfidence : OneQubitSelfNormalizedConfidence
      (pauliForcedExplorationGram blocks) estimate truth radius)
    (hRadiusSq : radius ^ 2 <=
      C ^ 2 * Real.log
        ((pauliForcedExplorationRoundCount blocks : Real) + 1)) :
    PopularRLSConditions.finiteEuclideanNorm
        (oneQubitRLSError estimate truth) <=
      Real.sqrt
        (C ^ 2 * Real.log
          ((pauliForcedExplorationRoundCount blocks : Real) + 1) /
            (blocks : Real)) := by
  have hsqrt := Real.sqrt_le_sqrt
    (pauliForcedExploration_RLSSquaredError_logRate
      blocks hblocks estimate truth radius C hConfidence hRadiusSq)
  simpa [PopularRLSConditions.finiteEuclideanNorm,
    QubitOracle.blochNormSq] using hsqrt

/-- Deterministic squared-error consistency along complete Pauli-block
endpoints.  The sole analytic premise is the scalar logarithmic rate tending
to zero; no probabilistic confidence conclusion is assumed here. -/
theorem pauliForcedExploration_RLSSquaredError_tendsto_zero
    (estimate : Nat -> Fin 3 -> Real) (truth : Fin 3 -> Real)
    (radius : Nat -> Real) (C : Real)
    (hConfidence : ∀ m, OneQubitSelfNormalizedConfidence
      (pauliForcedExplorationGram (m + 1)) (estimate m) truth (radius m))
    (hRadiusSq : ∀ m, radius m ^ 2 <=
      C ^ 2 * Real.log
        ((pauliForcedExplorationRoundCount (m + 1) : Real) + 1))
    (hScalarLogRate : Tendsto
      (fun m =>
        C ^ 2 * Real.log
          ((pauliForcedExplorationRoundCount (m + 1) : Real) + 1) /
            ((m + 1 : Nat) : Real)) atTop (nhds 0)) :
    Tendsto
      (fun m => QubitOracle.blochNormSq
        (oneQubitRLSError (estimate m) truth)) atTop (nhds 0) := by
  have hnonnegative : ∀ m,
      0 <= QubitOracle.blochNormSq
        (oneQubitRLSError (estimate m) truth) := by
    intro m
    unfold QubitOracle.blochNormSq
    exact Finset.sum_nonneg fun j _ => sq_nonneg
      (oneQubitRLSError (estimate m) truth j)
  have hupper : ∀ m,
      QubitOracle.blochNormSq
          (oneQubitRLSError (estimate m) truth) <=
        C ^ 2 * Real.log
          ((pauliForcedExplorationRoundCount (m + 1) : Real) + 1) /
            ((m + 1 : Nat) : Real) := by
    intro m
    exact pauliForcedExploration_RLSSquaredError_logRate
      (m + 1) (Nat.succ_pos m) (estimate m) truth (radius m) C
        (hConfidence m) (hRadiusSq m)
  exact squeeze_zero'
    (Filter.Eventually.of_forall hnonnegative)
    (Filter.Eventually.of_forall hupper) hScalarLogRate

/-- Euclidean RLS consistency along complete Pauli-block endpoints. -/
theorem pauliForcedExploration_RLSEuclideanError_tendsto_zero
    (estimate : Nat -> Fin 3 -> Real) (truth : Fin 3 -> Real)
    (radius : Nat -> Real) (C : Real)
    (hConfidence : ∀ m, OneQubitSelfNormalizedConfidence
      (pauliForcedExplorationGram (m + 1)) (estimate m) truth (radius m))
    (hRadiusSq : ∀ m, radius m ^ 2 <=
      C ^ 2 * Real.log
        ((pauliForcedExplorationRoundCount (m + 1) : Real) + 1))
    (hScalarLogRate : Tendsto
      (fun m =>
        C ^ 2 * Real.log
          ((pauliForcedExplorationRoundCount (m + 1) : Real) + 1) /
            ((m + 1 : Nat) : Real)) atTop (nhds 0)) :
    Tendsto
      (fun m => PopularRLSConditions.finiteEuclideanNorm
        (oneQubitRLSError (estimate m) truth)) atTop (nhds 0) := by
  have hsquared :=
    pauliForcedExploration_RLSSquaredError_tendsto_zero
      estimate truth radius C hConfidence hRadiusSq hScalarLogRate
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsquared
  simpa only [Function.comp_def,
    PopularRLSConditions.finiteEuclideanNorm,
    QubitOracle.blochNormSq, Real.sqrt_zero] using hsqrt

end

end QubitOracle.Paper
