import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.MixedAxisFisher
import QubitOracle.Paper.OneQubitPureCoordinateCore
import QubitOracle.Paper.OneQubitRotationTransport
/-! Supporting definitions and proved lemmas used by the manuscript. -/

namespace QubitOracle.Paper

open Finset
open scoped BigOperators

noncomputable section

/-! ## Mixed branch: a complete three-Pauli block -/

/-- The `k`th Pauli coordinate axis in Bloch coordinates. -/
def qubitPauliCoordinateAxis (k : Fin 3) : Fin 3 → Real :=
  fun j => if j = k then 1 else 0

theorem qubitPauliCoordinateAxis_normSq (k : Fin 3) :
    blochNormSq (qubitPauliCoordinateAxis k) = 1 := by
  fin_cases k <;>
    simp [qubitPauliCoordinateAxis, blochNormSq, Fin.sum_univ_succ]

theorem blochDot_qubitPauliCoordinateAxis
    (theta : Fin 3 → Real) (k : Fin 3) :
    blochDot theta (qubitPauliCoordinateAxis k) = theta k := by
  fin_cases k <;>
    simp [qubitPauliCoordinateAxis, blochDot, Fin.sum_univ_succ]

theorem mixedPauliCoordinate_denominator_pos
    (theta : Fin 3 → Real) (k : Fin 3)
    (hInterior : blochNormSq theta < 1) :
    0 < 1 - theta k ^ 2 := by
  have h := QubitOracle.mixedAxisFisher_denominator_pos
    theta (qubitPauliCoordinateAxis k) hInterior
      (qubitPauliCoordinateAxis_normSq k)
  simpa [blochDot_qubitPauliCoordinateAxis] using h


theorem mixedPauliCoordinateAxisFisher_apply
    (theta : Fin 3 → Real) (k i j : Fin 3) :
    QubitOracle.mixedAxisFisher theta (qubitPauliCoordinateAxis k) i j =
      if i = k ∧ j = k then (1 - theta k ^ 2)⁻¹ else 0 := by
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [QubitOracle.mixedAxisFisher, qubitPauliCoordinateAxis,
      QubitOracle.blochDot, QubitOracle.blochOuter,
      Fin.sum_univ_succ, Matrix.smul_apply, smul_eq_mul]

/-- Conditional Fisher information accumulated in one complete Pauli block. -/
def mixedPauliCompleteBlockFisher
    (theta : Fin 3 → Real) : Matrix (Fin 3) (Fin 3) Real :=
  ∑ k : Fin 3,
    QubitOracle.mixedAxisFisher theta (qubitPauliCoordinateAxis k)

/-- One complete three-axis block is diagonal with the exact Bernoulli Fisher
entries `1 / (1 - theta_j^2)`. -/
theorem mixedPauliCompleteBlockFisher_apply
    (theta : Fin 3 → Real) (i j : Fin 3) :
    mixedPauliCompleteBlockFisher theta i j =
      if i = j then (1 - theta i ^ 2)⁻¹ else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [mixedPauliCompleteBlockFisher,
      mixedPauliCoordinateAxisFisher_apply, Fin.sum_univ_succ]

/-- Expected conditional information after `blocks` identical complete
three-axis blocks. -/
def mixedPauliExpectedInformationAtBlocks
    (blocks : Nat) (theta : Fin 3 → Real) :
    Matrix (Fin 3) (Fin 3) Real :=
  (blocks : Real) • mixedPauliCompleteBlockFisher theta

/-- Normalization by the number of complete blocks is exactly constant. -/
theorem mixedPauliExpectedInformation_normalized_by_blocks
    (blocks : Nat) (hBlocks : 0 < blocks)
    (theta : Fin 3 → Real) :
    (blocks : Real)⁻¹ •
        mixedPauliExpectedInformationAtBlocks blocks theta =
      mixedPauliCompleteBlockFisher theta := by
  have hBlocksReal : (blocks : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hBlocks)
  ext i j
  simp only [mixedPauliExpectedInformationAtBlocks,
    Matrix.smul_apply, smul_eq_mul]
  field_simp [hBlocksReal]

/-- Since a mixed block contains three observations, normalization by the
number of observations gives one third of the block matrix. -/
theorem mixedPauliExpectedInformation_normalized_by_observations
    (blocks : Nat) (hBlocks : 0 < blocks)
    (theta : Fin 3 → Real) :
    ((3 * blocks : Nat) : Real)⁻¹ •
        mixedPauliExpectedInformationAtBlocks blocks theta =
      (1 / 3 : Real) • mixedPauliCompleteBlockFisher theta := by
  have hBlocksReal : (blocks : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hBlocks)
  ext i j
  simp only [mixedPauliExpectedInformationAtBlocks,
    Matrix.smul_apply, smul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
  field_simp [hBlocksReal]

theorem mixedPauliPerObservationInformation_apply
    (theta : Fin 3 → Real) (i j : Fin 3) :
    ((1 / 3 : Real) • mixedPauliCompleteBlockFisher theta) i j =
      if i = j then (3 * (1 - theta i ^ 2))⁻¹ else 0 := by
  rw [Matrix.smul_apply, mixedPauliCompleteBlockFisher_apply]
  by_cases hij : i = j
  · subst j
    simp [smul_eq_mul]
    ring
  · simp [hij, smul_eq_mul]

/-! ## Pure branch: exact tangent-coordinate score information -/

/-- The two coordinate axes in the north-pole tangent plane. -/
def pureNorthTangentCoordinateAxis (k : Fin 2) : Fin 3 → Real :=
  if k = 0 then ![1, 0, 0] else ![0, 1, 0]

/-- Coordinate directions in the two-dimensional stereographic chart. -/
def pureLocalCoordinateDirection (k : Fin 2) : Fin 2 → Real :=
  fun j => if j = k then 1 else 0

theorem pureNorthTangentCoordinateAxis_normSq (k : Fin 2) :
    blochNormSq (pureNorthTangentCoordinateAxis k) = 1 := by
  fin_cases k <;>
    simp [pureNorthTangentCoordinateAxis, blochNormSq,
      Fin.sum_univ_succ]

theorem pureNorthTangentCoordinateAxis_coordinate_two (k : Fin 2) :
    pureNorthTangentCoordinateAxis k 2 = 0 := by
  fin_cases k <;> simp [pureNorthTangentCoordinateAxis]










/-- Finite-dimensional quadratic form used for the directional Fisher
information in the `Fin 2` chart. -/
def pureFinTwoQuadraticInformation
    (M : Matrix (Fin 2) (Fin 2) Real) (h : Fin 2 → Real) : Real :=
  ∑ i : Fin 2, ∑ j : Fin 2, h i * M i j * h j


/-! ## Householder transport to an arbitrary pure truth -/

/-- The original-coordinate measurement axis obtained by reflecting a
north-pole tangent coordinate axis back to the arbitrary truth. -/
def pureTruthTangentCoordinateAxis
    (r : Fin 3 → Real) (k : Fin 2) : Fin 3 → Real :=
  qubitHouseholderToNorth r (pureNorthTangentCoordinateAxis k)

theorem pureTruthTangentCoordinateAxis_toNorth
    (r : Fin 3 → Real) (k : Fin 2) :
    qubitHouseholderToNorth r (pureTruthTangentCoordinateAxis r k) =
      pureNorthTangentCoordinateAxis k := by
  exact qubitHouseholderToNorth_involutive r
    (pureNorthTangentCoordinateAxis k)

theorem pureTruthTangentCoordinateAxis_normSq
    (r : Fin 3 → Real) (k : Fin 2) :
    blochNormSq (pureTruthTangentCoordinateAxis r k) = 1 := by
  rw [pureTruthTangentCoordinateAxis,
    qubitHouseholderToNorth_normSq_preserved,
    pureNorthTangentCoordinateAxis_normSq]

theorem pureTruthTangentCoordinateAxis_tangent
    (r : Fin 3 → Real) (k : Fin 2)
    (hTruthUnit : blochNormSq r = 1) :
    blochDot (pureTruthTangentCoordinateAxis r k) r = 0 := by
  calc
    blochDot (pureTruthTangentCoordinateAxis r k) r =
        blochDot
          (qubitHouseholderToNorth r
            (pureTruthTangentCoordinateAxis r k))
          (qubitHouseholderToNorth r r) :=
      (qubitHouseholderToNorth_dot_preserved r
        (pureTruthTangentCoordinateAxis r k) r).symm
    _ = blochDot (pureNorthTangentCoordinateAxis k)
        directionalNorthPole := by
      rw [pureTruthTangentCoordinateAxis_toNorth,
        qubitHouseholderToNorth_maps_truth r hTruthUnit]
    _ = 0 := by
      fin_cases k <;>
        simp [pureNorthTangentCoordinateAxis, directionalNorthPole,
          blochDot, Fin.sum_univ_succ]











namespace Label

/-- Mixed-qubit complete-block reduction of predictable conditional Fisher
information.  This is an exact fixed-design identity, not a stochastic
information-convergence theorem. -/
theorem eq_SI_mixed_fixed_block_information_qubit_reduction
    (blocks : Nat) (hBlocks : 0 < blocks)
    (theta : Fin 3 → Real) (hInterior : blochNormSq theta < 1) :
    (∀ k : Fin 3, 0 < 1 - theta k ^ 2) ∧
      (∀ i j : Fin 3,
        mixedPauliCompleteBlockFisher theta i j =
          if i = j then (1 - theta i ^ 2)⁻¹ else 0) ∧
      ((3 * blocks : Nat) : Real)⁻¹ •
          mixedPauliExpectedInformationAtBlocks blocks theta =
        (1 / 3 : Real) • mixedPauliCompleteBlockFisher theta := by
  refine ⟨fun k => mixedPauliCoordinate_denominator_pos
      theta k hInterior, ?_,
    mixedPauliExpectedInformation_normalized_by_observations
      blocks hBlocks theta⟩
  intro i j
  exact mixedPauliCompleteBlockFisher_apply theta i j


end Label

end

end QubitOracle.Paper
