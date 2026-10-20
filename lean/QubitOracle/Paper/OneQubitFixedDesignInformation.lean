import QubitOracle.Paper.MixedScoreMoments
import QubitOracle.Paper.OneQubitRotationTransport

/-!
# Exact fixed-block information for one-qubit designs

This module replaces a stochastic information-convergence premise by an exact
calculation for complete deterministic measurement blocks.

* In the mixed branch, one block measures the three Pauli coordinate axes.
  Its conditional Fisher matrix is diagonal with entry
  `(1 - theta j ^ 2)⁻¹` in coordinate `j`.
* In the pure branch, one block measures the two tangent coordinate axes in
  the Householder frame of an arbitrary unit Bloch truth.  The stereographic
  coordinate score is `2 * outcomeSign * h k`, so the block Fisher matrix is
  exactly `4 I_2` and its per-observation normalization is `2 I_2`.

All statements concern predictable conditional Fisher information.  No
probabilistic concentration, persistent-excitation theorem, LAN remainder, or
external scientific axiom is imported or used.
-/

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

/-- The conditional score second moment for a coordinate measurement is its
coordinate-axis Fisher matrix. -/
theorem mixedPauliCoordinateScore_secondMoment_eq_fisher
    (theta : Fin 3 → Real) (k i j : Fin 3)
    (hInterior : blochNormSq theta < 1) :
    QubitOracle.binaryAxisPlusProbability (theta k) *
          mixedAxisPlusScoreVector theta (qubitPauliCoordinateAxis k) i *
          mixedAxisPlusScoreVector theta (qubitPauliCoordinateAxis k) j +
      QubitOracle.binaryAxisMinusProbability (theta k) *
          mixedAxisMinusScoreVector theta (qubitPauliCoordinateAxis k) i *
          mixedAxisMinusScoreVector theta (qubitPauliCoordinateAxis k) j =
        QubitOracle.mixedAxisFisher theta
          (qubitPauliCoordinateAxis k) i j := by
  have hRegular :
      blochDot theta (qubitPauliCoordinateAxis k) ^ 2 < 1 := by
    rw [blochDot_qubitPauliCoordinateAxis]
    exact sub_pos.mp (mixedPauliCoordinate_denominator_pos theta k hInterior)
  simpa [blochDot_qubitPauliCoordinateAxis] using
    mixedAxisScore_secondMoment_eq_fisher
      theta (qubitPauliCoordinateAxis k) hRegular i j

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

theorem pureNorthTangentCoordinateAxis_overlap
    (k : Fin 2) (h : Fin 2 → Real) :
    directionalTangentOverlap (pureNorthTangentCoordinateAxis k) h = h k := by
  fin_cases k <;>
    simp [pureNorthTangentCoordinateAxis, directionalTangentOverlap]

theorem pureCoordinateAxis_coordinateDirection_overlap
    (k i : Fin 2) :
    directionalTangentOverlap (pureNorthTangentCoordinateAxis k)
        (pureLocalCoordinateDirection i) =
      if i = k then 1 else 0 := by
  fin_cases k <;> fin_cases i <;>
    simp [pureNorthTangentCoordinateAxis, pureLocalCoordinateDirection,
      directionalTangentOverlap]

/-- At the north-pole truth every tangent-axis outcome has probability
`1 / 2`. -/
theorem pureNorthTangentBornProbability_eq_half
    (k : Fin 2) (y : QubitRLSOutcome) :
    qubitRLSBornProbability directionalNorthPole
        (pureNorthTangentCoordinateAxis k) y = (1 / 2 : Real) := by
  fin_cases k <;> cases y <;>
    simp [qubitRLSBornProbability, qubitBornTrace_eq, blochDot,
      directionalNorthPole, pureNorthTangentCoordinateAxis,
      qubitRLSOutcomeSign, Fin.sum_univ_succ]

/-- The exact first derivative at the truth.  The factor `2` is derived from
the stereographic chart and the Bernoulli probability `1 / 2`. -/
theorem directionalRationalLogLikelihoodD1_zero_of_tangent
    (axis : Fin 3 → Real) (h : Fin 2 → Real)
    (y : QubitRLSOutcome) (hTangent : axis 2 = 0) :
    directionalRationalLogLikelihoodD1 axis h y 0 =
      2 * qubitRLSOutcomeSign y * directionalTangentOverlap axis h := by
  simp [directionalRationalLogLikelihoodD1, directionalScalarScore,
    directionalBornNumerator, directionalBornNumeratorD1,
    directionalBornDenominator, directionalBornDenominatorD1,
    directionalLineDenominator, hTangent]

theorem pureNorthCoordinateScore_eq
    (k : Fin 2) (h : Fin 2 → Real) (y : QubitRLSOutcome) :
    directionalRationalLogLikelihoodD1
        (pureNorthTangentCoordinateAxis k) h y 0 =
      2 * qubitRLSOutcomeSign y * h k := by
  rw [directionalRationalLogLikelihoodD1_zero_of_tangent
    (pureNorthTangentCoordinateAxis k) h y
    (pureNorthTangentCoordinateAxis_coordinate_two k)]
  rw [pureNorthTangentCoordinateAxis_overlap]

/-- Conditional Fisher matrix of one north-pole tangent-coordinate
measurement, calculated from the two outcome probabilities and scores. -/
def pureNorthDirectionalAxisFisher
    (k : Fin 2) : Matrix (Fin 2) (Fin 2) Real :=
  fun i j =>
    ∑ y : QubitRLSOutcome,
      qubitRLSBornProbability directionalNorthPole
          (pureNorthTangentCoordinateAxis k) y *
        directionalRationalLogLikelihoodD1
          (pureNorthTangentCoordinateAxis k)
          (pureLocalCoordinateDirection i) y 0 *
        directionalRationalLogLikelihoodD1
          (pureNorthTangentCoordinateAxis k)
          (pureLocalCoordinateDirection j) y 0

/-- One tangent-coordinate measurement contributes `4 e_k e_k^T` in the
stereographic chart. -/
theorem pureNorthDirectionalAxisFisher_apply
    (k i j : Fin 2) :
    pureNorthDirectionalAxisFisher k i j =
      if i = k ∧ j = k then 4 else 0 := by
  have hProbability : ∀ y : QubitRLSOutcome,
      qubitRLSBornProbability directionalNorthPole
          (pureNorthTangentCoordinateAxis k) y = (1 / 2 : Real) :=
    fun y => pureNorthTangentBornProbability_eq_half k y
  have hScoreI : ∀ y : QubitRLSOutcome,
      directionalRationalLogLikelihoodD1
          (pureNorthTangentCoordinateAxis k)
          (pureLocalCoordinateDirection i) y 0 =
        2 * qubitRLSOutcomeSign y *
          directionalTangentOverlap (pureNorthTangentCoordinateAxis k)
            (pureLocalCoordinateDirection i) :=
    fun y => directionalRationalLogLikelihoodD1_zero_of_tangent
      (pureNorthTangentCoordinateAxis k) (pureLocalCoordinateDirection i) y
        (pureNorthTangentCoordinateAxis_coordinate_two k)
  have hScoreJ : ∀ y : QubitRLSOutcome,
      directionalRationalLogLikelihoodD1
          (pureNorthTangentCoordinateAxis k)
          (pureLocalCoordinateDirection j) y 0 =
        2 * qubitRLSOutcomeSign y *
          directionalTangentOverlap (pureNorthTangentCoordinateAxis k)
            (pureLocalCoordinateDirection j) :=
    fun y => directionalRationalLogLikelihoodD1_zero_of_tangent
      (pureNorthTangentCoordinateAxis k) (pureLocalCoordinateDirection j) y
        (pureNorthTangentCoordinateAxis_coordinate_two k)
  unfold pureNorthDirectionalAxisFisher
  simp_rw [hProbability, hScoreI, hScoreJ]
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [pureNorthTangentCoordinateAxis, pureLocalCoordinateDirection,
      directionalTangentOverlap, qubitRLSOutcomeSign] <;> ring

/-- Fisher matrix of the complete two-axis tangent block. -/
def pureNorthCompleteBlockFisher : Matrix (Fin 2) (Fin 2) Real :=
  ∑ k : Fin 2, pureNorthDirectionalAxisFisher k

/-- The complete tangent block is exactly `4 I_2`. -/
theorem pureNorthCompleteBlockFisher_apply (i j : Fin 2) :
    pureNorthCompleteBlockFisher i j = if i = j then 4 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [pureNorthCompleteBlockFisher,
      pureNorthDirectionalAxisFisher_apply, Fin.sum_univ_succ]

/-- Finite-dimensional quadratic form used for the directional Fisher
information in the `Fin 2` chart. -/
def pureFinTwoQuadraticInformation
    (M : Matrix (Fin 2) (Fin 2) Real) (h : Fin 2 → Real) : Real :=
  ∑ i : Fin 2, ∑ j : Fin 2, h i * M i j * h j

/-- The complete pure block has directional information `4 * ||h||^2`.
This is the block total; division by its two observations gives
`2 * ||h||^2`. -/
theorem pureNorthCompleteBlock_quadraticInformation
    (h : Fin 2 → Real) :
    pureFinTwoQuadraticInformation pureNorthCompleteBlockFisher h =
      4 * directionalQubitNormSq h := by
  simp [pureFinTwoQuadraticInformation,
    pureNorthCompleteBlockFisher_apply,
    directionalQubitNormSq, Fin.sum_univ_succ]
  ring

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

/-- Conditional local-coordinate Fisher matrix of one transported tangent
measurement at an arbitrary pure truth. -/
def pureTruthDirectionalAxisFisher
    (r : Fin 3 → Real) (k : Fin 2) : Matrix (Fin 2) (Fin 2) Real :=
  fun i j =>
    ∑ y : QubitRLSOutcome,
      qubitRLSBornProbability r (pureTruthTangentCoordinateAxis r k) y *
        qubitRotatedRationalLogLikelihoodD1 r
          (pureTruthTangentCoordinateAxis r k)
          (pureLocalCoordinateDirection i) y 0 *
        qubitRotatedRationalLogLikelihoodD1 r
          (pureTruthTangentCoordinateAxis r k)
          (pureLocalCoordinateDirection j) y 0

/-- Householder transport preserves the complete score-moment calculation. -/
theorem pureTruthDirectionalAxisFisher_eq_north
    (r : Fin 3 → Real) (k : Fin 2)
    (hTruthUnit : blochNormSq r = 1) :
    pureTruthDirectionalAxisFisher r k =
      pureNorthDirectionalAxisFisher k := by
  ext i j
  unfold pureTruthDirectionalAxisFisher pureNorthDirectionalAxisFisher
  apply Finset.sum_congr rfl
  intro y _hy
  have hProbability :=
    qubitHouseholder_truth_BornProbability_invariant r
      (pureTruthTangentCoordinateAxis r k) y hTruthUnit
  rw [hProbability]
  simp only [qubitRotatedRationalLogLikelihoodD1]
  rw [pureTruthTangentCoordinateAxis_toNorth]

def pureTruthCompleteBlockFisher
    (r : Fin 3 → Real) : Matrix (Fin 2) (Fin 2) Real :=
  ∑ k : Fin 2, pureTruthDirectionalAxisFisher r k

theorem pureTruthCompleteBlockFisher_eq_north
    (r : Fin 3 → Real) (hTruthUnit : blochNormSq r = 1) :
    pureTruthCompleteBlockFisher r = pureNorthCompleteBlockFisher := by
  unfold pureTruthCompleteBlockFisher pureNorthCompleteBlockFisher
  apply Finset.sum_congr rfl
  intro k _hk
  exact pureTruthDirectionalAxisFisher_eq_north r k hTruthUnit

theorem pureTruthCompleteBlockFisher_apply
    (r : Fin 3 → Real) (hTruthUnit : blochNormSq r = 1)
    (i j : Fin 2) :
    pureTruthCompleteBlockFisher r i j = if i = j then 4 else 0 := by
  rw [pureTruthCompleteBlockFisher_eq_north r hTruthUnit]
  exact pureNorthCompleteBlockFisher_apply i j

theorem pureTruthCompleteBlock_quadraticInformation
    (r : Fin 3 → Real) (hTruthUnit : blochNormSq r = 1)
    (h : Fin 2 → Real) :
    pureFinTwoQuadraticInformation (pureTruthCompleteBlockFisher r) h =
      4 * directionalQubitNormSq h := by
  rw [pureTruthCompleteBlockFisher_eq_north r hTruthUnit]
  exact pureNorthCompleteBlock_quadraticInformation h

def pureTruthExpectedInformationAtBlocks
    (blocks : Nat) (r : Fin 3 → Real) : Matrix (Fin 2) (Fin 2) Real :=
  (blocks : Real) • pureTruthCompleteBlockFisher r

theorem pureTruthExpectedInformation_normalized_by_blocks
    (blocks : Nat) (hBlocks : 0 < blocks)
    (r : Fin 3 → Real) :
    (blocks : Real)⁻¹ • pureTruthExpectedInformationAtBlocks blocks r =
      pureTruthCompleteBlockFisher r := by
  have hBlocksReal : (blocks : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hBlocks)
  ext i j
  simp only [pureTruthExpectedInformationAtBlocks,
    Matrix.smul_apply, smul_eq_mul]
  field_simp [hBlocksReal]

/-- A pure block has two observations, so its per-observation expected
information is one half of `4 I_2`, namely `2 I_2`. -/
theorem pureTruthExpectedInformation_normalized_by_observations
    (blocks : Nat) (hBlocks : 0 < blocks)
    (r : Fin 3 → Real) :
    ((2 * blocks : Nat) : Real)⁻¹ •
        pureTruthExpectedInformationAtBlocks blocks r =
      (1 / 2 : Real) • pureTruthCompleteBlockFisher r := by
  have hBlocksReal : (blocks : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hBlocks)
  ext i j
  simp only [pureTruthExpectedInformationAtBlocks,
    Matrix.smul_apply, smul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
  field_simp [hBlocksReal]

theorem pureTruthPerObservationInformation_apply
    (r : Fin 3 → Real) (hTruthUnit : blochNormSq r = 1)
    (i j : Fin 2) :
    ((1 / 2 : Real) • pureTruthCompleteBlockFisher r) i j =
      if i = j then 2 else 0 := by
  rw [Matrix.smul_apply,
    pureTruthCompleteBlockFisher_apply r hTruthUnit]
  by_cases hij : i = j
  · norm_num [hij, smul_eq_mul]
  · simp [hij, smul_eq_mul]

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

/-- Pure-qubit fixed tangent-block reduction at an arbitrary unit truth.
The block Fisher matrix is `4 I_2`; normalization by its two observations is
`2 I_2`.  No Gaussian limit is asserted. -/
theorem eq_SI_pure_fixed_tangent_block_information_qubit_reduction
    (blocks : Nat) (hBlocks : 0 < blocks)
    (r : Fin 3 → Real) (hTruthUnit : blochNormSq r = 1) :
    (∀ k : Fin 2,
      blochNormSq (pureTruthTangentCoordinateAxis r k) = 1 ∧
        blochDot (pureTruthTangentCoordinateAxis r k) r = 0) ∧
      (∀ i j : Fin 2,
        pureTruthCompleteBlockFisher r i j =
          if i = j then 4 else 0) ∧
      (∀ h : Fin 2 → Real,
        pureFinTwoQuadraticInformation (pureTruthCompleteBlockFisher r) h =
          4 * directionalQubitNormSq h) ∧
      ((2 * blocks : Nat) : Real)⁻¹ •
          pureTruthExpectedInformationAtBlocks blocks r =
        (1 / 2 : Real) • pureTruthCompleteBlockFisher r := by
  refine ⟨?_, ?_, ?_,
    pureTruthExpectedInformation_normalized_by_observations
      blocks hBlocks r⟩
  · intro k
    exact ⟨pureTruthTangentCoordinateAxis_normSq r k,
      pureTruthTangentCoordinateAxis_tangent r k hTruthUnit⟩
  · intro i j
    exact pureTruthCompleteBlockFisher_apply r hTruthUnit i j
  · intro h
    exact pureTruthCompleteBlock_quadraticInformation r hTruthUnit h

end Label

end

end QubitOracle.Paper
