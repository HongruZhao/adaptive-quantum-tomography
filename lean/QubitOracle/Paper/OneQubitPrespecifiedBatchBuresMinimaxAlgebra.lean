import QubitOracle.Paper.OneQubitPrespecifiedBatchCumulativeInformationClosure
import QubitOracle.Paper.GaussianQuadraticRisk

/-!
# Bures benchmark algebra for the prespecified-batch mixed-qubit protocol

This file contains only finite-dimensional coordinate and Gaussian covariance
algebra.  It imports no LAN-to-minimax transfer theorem and introduces no
scientific assumption.

The local frame is ordered tangent, tangent, radial.  In those coordinates,
the equal-cycle information and the Bures/ordinary-infidelity quadratic loss
have matching radial singular factors.  Their covariance contraction is
therefore exactly `9/4`.

Squared Frobenius loss is treated separately.  The equal-cycle Bures design
has a valid Frobenius benchmark, but away from the maximally mixed state it is
strictly worse than the feasible state-dependent Frobenius radial/tangent
allocation.  No joint-optimality claim is made.
-/

namespace QubitOracle.Paper

open Matrix
open scoped BigOperators Matrix

noncomputable section

set_option maxRecDepth 2000

/-! ## Orthogonal raw-Bloch to local radial/tangent coordinates -/

/-- Orthogonal coordinate matrix associated with the local continuous frame.
It sends a raw Bloch perturbation to its tangent, tangent, radial coordinates. -/
def localRadialTangentCoordinateMatrix
    (b theta : RLSVector 3) : Matrix (Fin 3) (Fin 3) Real :=
  (localContinuousQubitFrame b theta).transpose

/-- Coordinates of a raw Bloch perturbation in the local truth frame. -/
def localRadialTangentCoordinates
    (b theta h : RLSVector 3) : RLSVector 3 :=
  (localRadialTangentCoordinateMatrix b theta).mulVec h

/-- Congruence transform of a raw-Bloch quadratic-form matrix into local
radial/tangent coordinates. -/
def localRadialTangentTransform
    (b theta : RLSVector 3)
    (A : Matrix (Fin 3) (Fin 3) Real) : Matrix (Fin 3) (Fin 3) Real :=
  localRadialTangentCoordinateMatrix b theta * A *
    (localRadialTangentCoordinateMatrix b theta).transpose

theorem localRadialTangentCoordinateMatrix_orthogonal
    (theta b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    localRadialTangentCoordinateMatrix b theta *
        (localRadialTangentCoordinateMatrix b theta).transpose = 1 ∧
      (localRadialTangentCoordinateMatrix b theta).transpose *
        localRadialTangentCoordinateMatrix b theta = 1 := by
  constructor
  · simpa [localRadialTangentCoordinateMatrix] using
      localContinuousQubitFrame_transpose_mul_self
        (show LocalContinuousFrameDomain b theta from ⟨hTruth.1, hSeed⟩)
  · simpa [localRadialTangentCoordinateMatrix] using
      localContinuousQubitFrame_mul_transpose_self
        (show LocalContinuousFrameDomain b theta from ⟨hTruth.1, hSeed⟩)

theorem localRadialTangentCoordinates_apply
    (b theta h : RLSVector 3) (k : Fin 3) :
    localRadialTangentCoordinates b theta h k =
      QubitOracle.blochDot h
        (mixedTwoStageFrameAxis (localContinuousQubitFrame b theta) k) := by
  simp [localRadialTangentCoordinates, localRadialTangentCoordinateMatrix,
    Matrix.mulVec, QubitOracle.blochDot, mixedTwoStageFrameAxis,
    qubitFrameAxis, dotProduct, Fin.sum_univ_succ]
  ring

theorem localRadialTangentCoordinates_inverse
    (theta b h : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    (localRadialTangentCoordinateMatrix b theta).transpose.mulVec
        (localRadialTangentCoordinates b theta h) = h := by
  rw [localRadialTangentCoordinates, Matrix.mulVec_mulVec,
    (localRadialTangentCoordinateMatrix_orthogonal
      theta b hTruth hSeed).2, Matrix.one_mulVec]

theorem localRadialTangentCoordinates_truth_tangentFirst
    (theta b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    localRadialTangentCoordinates b theta theta 0 = 0 := by
  rw [localRadialTangentCoordinates_apply]
  change QubitOracle.blochDot theta (localFrameFirstTangent b theta) = 0
  have horth := localFrameFirstTangent_dot_radial
    (show LocalContinuousFrameDomain b theta from ⟨hTruth.1, hSeed⟩)
  simp [localNormalizedBlochDirection,
    QubitOracle.blochDot, Fin.sum_univ_succ] at horth ⊢
  have hsqrt : Real.sqrt (QubitOracle.blochNormSq theta) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hTruth.1)
  field_simp [hsqrt] at horth ⊢
  simpa [mul_comm] using horth

theorem localRadialTangentCoordinates_truth_tangentSecond
    (theta b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    localRadialTangentCoordinates b theta theta 1 = 0 := by
  rw [localRadialTangentCoordinates_apply]
  change QubitOracle.blochDot theta (localFrameSecondTangent b theta) = 0
  have horth := localFrameSecondTangent_dot_radial b theta
  simp [localNormalizedBlochDirection,
    QubitOracle.blochDot, Fin.sum_univ_succ] at horth ⊢
  have hsqrt : Real.sqrt (QubitOracle.blochNormSq theta) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hTruth.1)
  field_simp [hsqrt] at horth ⊢
  simpa [mul_comm] using horth

theorem localRadialTangentCoordinates_truth_radial_sq
    (theta b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    localRadialTangentCoordinates b theta theta 2 ^ 2 =
      QubitOracle.blochNormSq theta := by
  rw [localRadialTangentCoordinates_apply]
  change QubitOracle.blochDot theta
    (localNormalizedBlochDirection theta) ^ 2 = QubitOracle.blochNormSq theta
  simp [localNormalizedBlochDirection, QubitOracle.blochDot,
    QubitOracle.blochNormSq, Fin.sum_univ_succ]
  have hsqrt : Real.sqrt
      (theta 0 ^ 2 + (theta 1 ^ 2 + theta 2 ^ 2)) ≠ 0 := by
    simpa [QubitOracle.blochNormSq, Fin.sum_univ_succ] using
      ne_of_gt (Real.sqrt_pos.2 hTruth.1)
  field_simp [hsqrt]
  nlinarith [Real.sq_sqrt (show 0 <=
    theta 0 ^ 2 + (theta 1 ^ 2 + theta 2 ^ 2) by positivity)]

theorem localRadialTangentTransform_one
    (theta b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    localRadialTangentTransform b theta 1 = 1 := by
  unfold localRadialTangentTransform
  rw [Matrix.mul_one,
    (localRadialTangentCoordinateMatrix_orthogonal
      theta b hTruth hSeed).1]

theorem localRadialTangentTransform_blochOuter
    (b theta v : RLSVector 3) :
    localRadialTangentTransform b theta (QubitOracle.blochOuter v) =
      QubitOracle.blochOuter (localRadialTangentCoordinates b theta v) := by
  ext i j
  simp [localRadialTangentTransform, localRadialTangentCoordinateMatrix,
    localRadialTangentCoordinates, QubitOracle.blochOuter,
    Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-! ## Diagonal Bures information and loss -/

/-- Positive radial denominator `1 - ||theta||^2`. -/
def mixedInteriorBlochGap (theta : RLSVector 3) : Real :=
  1 - QubitOracle.blochNormSq theta

theorem mixedInteriorBlochGap_pos
    (theta : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta) :
    0 < mixedInteriorBlochGap theta := by
  unfold mixedInteriorBlochGap
  linarith [hTruth.2]

/-- Equal-cycle Bures information eigenvalues in tangent, tangent, radial
coordinates. -/
def mixedBuresCoordinateInformationEigenvalues
    (theta : RLSVector 3) : Fin 3 -> Real :=
  fun k => if k = 2 then (3 * mixedInteriorBlochGap theta)⁻¹ else 1 / 3

def mixedBuresCoordinateInformation
    (theta : RLSVector 3) : Matrix (Fin 3) (Fin 3) Real :=
  Matrix.diagonal (mixedBuresCoordinateInformationEigenvalues theta)

/-- Raw-Bloch Bures/ordinary-infidelity local quadratic weight. -/
def mixedRawBlochBuresInfidelityWeight
    (theta : RLSVector 3) : Matrix (Fin 3) (Fin 3) Real :=
  (1 / 4 : Real) • (1 : Matrix (Fin 3) (Fin 3) Real) +
    (4 * mixedInteriorBlochGap theta)⁻¹ • QubitOracle.blochOuter theta

/-- Bures/ordinary-infidelity loss eigenvalues in tangent, tangent, radial
coordinates. -/
def mixedBuresInfidelityCoordinateWeightEigenvalues
    (theta : RLSVector 3) : Fin 3 -> Real :=
  fun k => if k = 2 then (4 * mixedInteriorBlochGap theta)⁻¹ else 1 / 4

def mixedBuresInfidelityCoordinateWeight
    (theta : RLSVector 3) : Matrix (Fin 3) (Fin 3) Real :=
  Matrix.diagonal (mixedBuresInfidelityCoordinateWeightEigenvalues theta)

private theorem localRadialTangentTransform_add_smul_outer
    (theta b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (a c : Real) :
    localRadialTangentTransform b theta
        (a • (1 : Matrix (Fin 3) (Fin 3) Real) +
          c • QubitOracle.blochOuter theta) =
      a • (1 : Matrix (Fin 3) (Fin 3) Real) +
        c • QubitOracle.blochOuter
          (localRadialTangentCoordinates b theta theta) := by
  unfold localRadialTangentTransform
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul]
  rw [show localRadialTangentCoordinateMatrix b theta *
      (1 : Matrix (Fin 3) (Fin 3) Real) *
      (localRadialTangentCoordinateMatrix b theta).transpose = 1 by
        simpa [localRadialTangentTransform] using
          localRadialTangentTransform_one theta b hTruth hSeed]
  rw [show localRadialTangentCoordinateMatrix b theta *
      QubitOracle.blochOuter theta *
      (localRadialTangentCoordinateMatrix b theta).transpose =
        QubitOracle.blochOuter
          (localRadialTangentCoordinates b theta theta) by
        simpa [localRadialTangentTransform] using
          localRadialTangentTransform_blochOuter b theta theta]

/-- Rigorous raw-Bloch normalization: the transformed Bures information is
diagonal with entries `1/3, 1/3, 1/(3(1-||theta||^2))`. -/
theorem localRadialTangentTransform_mixedBuresTarget
    (theta b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    localRadialTangentTransform b theta (mixedBuresTarget theta) =
      mixedBuresCoordinateInformation theta := by
  rw [show mixedBuresTarget theta =
      (1 / 3 : Real) • (1 : Matrix (Fin 3) (Fin 3) Real) +
        (3 * mixedInteriorBlochGap theta)⁻¹ •
          QubitOracle.blochOuter theta by
    rfl]
  rw [localRadialTangentTransform_add_smul_outer
    theta b hTruth hSeed]
  have h0 := localRadialTangentCoordinates_truth_tangentFirst
    theta b hTruth hSeed
  have h1 := localRadialTangentCoordinates_truth_tangentSecond
    theta b hTruth hSeed
  have h2 := localRadialTangentCoordinates_truth_radial_sq
    theta b hTruth hSeed
  have hgap := mixedInteriorBlochGap_pos theta hTruth
  have hgap' : 1 - QubitOracle.blochNormSq theta ≠ 0 := by
    simpa [mixedInteriorBlochGap] using hgap.ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mixedBuresCoordinateInformation,
      mixedBuresCoordinateInformationEigenvalues, Matrix.diagonal_apply,
      QubitOracle.blochOuter, h0, h1, ← pow_two, h2,
      mixedInteriorBlochGap] <;>
    field_simp [hgap'] <;> ring

/-- The corresponding raw-Bloch Bures/ordinary-infidelity quadratic weight
becomes diagonal with entries `1/4, 1/4, 1/(4(1-||theta||^2))`. -/
theorem localRadialTangentTransform_mixedRawBlochBuresInfidelityWeight
    (theta b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    localRadialTangentTransform b theta
        (mixedRawBlochBuresInfidelityWeight theta) =
      mixedBuresInfidelityCoordinateWeight theta := by
  unfold mixedRawBlochBuresInfidelityWeight
  rw [localRadialTangentTransform_add_smul_outer
    theta b hTruth hSeed]
  have h0 := localRadialTangentCoordinates_truth_tangentFirst
    theta b hTruth hSeed
  have h1 := localRadialTangentCoordinates_truth_tangentSecond
    theta b hTruth hSeed
  have h2 := localRadialTangentCoordinates_truth_radial_sq
    theta b hTruth hSeed
  have hgap := mixedInteriorBlochGap_pos theta hTruth
  have hgap' : 1 - QubitOracle.blochNormSq theta ≠ 0 := by
    simpa [mixedInteriorBlochGap] using hgap.ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mixedBuresInfidelityCoordinateWeight,
      mixedBuresInfidelityCoordinateWeightEigenvalues,
      Matrix.diagonal_apply, QubitOracle.blochOuter, h0, h1,
      ← pow_two, h2, mixedInteriorBlochGap] <;>
    field_simp [hgap'] <;> ring

private theorem mixedBuresCoordinateInformation_inv
    (theta : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta) :
    (mixedBuresCoordinateInformation theta)⁻¹ =
      Matrix.diagonal ![3, 3, 3 * mixedInteriorBlochGap theta] := by
  have hgap := mixedInteriorBlochGap_pos theta hTruth
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mixedBuresCoordinateInformation,
      mixedBuresCoordinateInformationEigenvalues, Matrix.mul_apply,
      Fin.sum_univ_succ] <;>
    field_simp [hgap.ne'] <;> ring

/-- The Gaussian covariance benchmark `trace(G J^{-1})` is exactly `9/4`.
This is algebraic and does not itself invoke a LAN-to-minimax transfer. -/
theorem mixedBuresInfidelityGaussianBenchmark_eq_nine_fourths
    (theta : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta) :
    covarianceQuadraticRisk
        (mixedBuresInfidelityCoordinateWeight theta)
        (mixedBuresCoordinateInformation theta)⁻¹ = 9 / 4 := by
  have hgap := mixedInteriorBlochGap_pos theta hTruth
  rw [mixedBuresCoordinateInformation_inv theta hTruth]
  simp [covarianceQuadraticRisk, mixedBuresCoordinateInformationEigenvalues,
    mixedBuresInfidelityCoordinateWeight,
    mixedBuresInfidelityCoordinateWeightEigenvalues,
    Matrix.diagonal_apply, Fin.sum_univ_succ]
  field_simp [hgap.ne']
  ring

/-! ## Equal-cycle Frobenius benchmark and non-optimality -/

/-- Squared Frobenius loss has weight `1/2` in each orthogonal Bloch
coordinate. -/
def mixedFrobeniusCoordinateWeight : Matrix (Fin 3) (Fin 3) Real :=
  Matrix.diagonal ![1 / 2, 1 / 2, 1 / 2]

/-- Frobenius covariance benchmark for a radial/tangent allocation with each
tangent mass `a` and radial mass `c`. -/
def mixedRadialTangentFrobeniusBenchmark
    (theta : RLSVector 3) (a c : Real) : Real :=
  a⁻¹ + mixedInteriorBlochGap theta / (2 * c)

/-- The equal-cycle Bures design's squared-Frobenius benchmark. -/
def mixedEqualCycleFrobeniusBenchmark
    (theta : RLSVector 3) : Real :=
  covarianceQuadraticRisk mixedFrobeniusCoordinateWeight
    (mixedBuresCoordinateInformation theta)⁻¹

theorem mixedEqualCycleFrobeniusBenchmark_eq
    (theta : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta) :
    mixedEqualCycleFrobeniusBenchmark theta =
      3 + (3 / 2 : Real) * mixedInteriorBlochGap theta := by
  unfold mixedEqualCycleFrobeniusBenchmark
  rw [mixedBuresCoordinateInformation_inv theta hTruth]
  simp [covarianceQuadraticRisk, mixedBuresCoordinateInformationEigenvalues,
    mixedFrobeniusCoordinateWeight, Matrix.diagonal_apply,
    Fin.sum_univ_succ]
  ring

theorem mixedEqualCycleFrobeniusBenchmark_eq_allocation
    (theta : RLSVector 3) :
    mixedRadialTangentFrobeniusBenchmark theta (1 / 3) (1 / 3) =
      3 + (3 / 2 : Real) * mixedInteriorBlochGap theta := by
  unfold mixedRadialTangentFrobeniusBenchmark
  ring

/-- The feasible state-dependent Frobenius allocation has benchmark
`(2 + sqrt(1-||theta||^2))^2 / 2`. -/
theorem mixedFrobeniusOptimalAllocationBenchmark_eq
    (theta : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta) :
    mixedRadialTangentFrobeniusBenchmark theta
        (mixedCoherenceAllocation theta) (mixedRadialAllocation theta) =
      (2 + mixedRadialGap theta) ^ 2 / 2 := by
  have hs := mixedRadialGap_pos theta hTruth.2
  have hsne : mixedRadialGap theta ≠ 0 := hs.ne'
  have hden : 2 + mixedRadialGap theta ≠ 0 := by positivity
  have hsq : mixedRadialGap theta ^ 2 = mixedInteriorBlochGap theta := by
    unfold mixedRadialGap mixedInteriorBlochGap
    exact Real.sq_sqrt (sub_nonneg.mpr hTruth.2.le)
  unfold mixedRadialTangentFrobeniusBenchmark
    mixedCoherenceAllocation mixedRadialAllocation
  rw [← hsq]
  field_simp [hsne, hden] <;> ring

/-- Exact excess of the equal-cycle Frobenius benchmark over the feasible
state-dependent Frobenius allocation. -/
theorem mixedEqualCycleFrobenius_excess_eq
    (theta : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta) :
    mixedEqualCycleFrobeniusBenchmark theta -
        mixedRadialTangentFrobeniusBenchmark theta
          (mixedCoherenceAllocation theta) (mixedRadialAllocation theta) =
      (1 - mixedRadialGap theta) ^ 2 := by
  rw [mixedEqualCycleFrobeniusBenchmark_eq theta hTruth,
    mixedFrobeniusOptimalAllocationBenchmark_eq theta hTruth]
  have hsq : mixedRadialGap theta ^ 2 = mixedInteriorBlochGap theta := by
    unfold mixedRadialGap mixedInteriorBlochGap
    exact Real.sq_sqrt (sub_nonneg.mpr hTruth.2.le)
  rw [← hsq]
  ring

/-- Away from the maximally mixed state, the equal-cycle Bures design is
strictly suboptimal for squared Frobenius loss. -/
theorem mixedEqualCycleFrobenius_not_optimal_of_nonzero
    (theta : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta) :
    mixedRadialTangentFrobeniusBenchmark theta
        (mixedCoherenceAllocation theta) (mixedRadialAllocation theta) <
      mixedEqualCycleFrobeniusBenchmark theta := by
  have hsnonneg : 0 <= mixedRadialGap theta := Real.sqrt_nonneg _
  have hsq : mixedRadialGap theta ^ 2 = mixedInteriorBlochGap theta := by
    unfold mixedRadialGap mixedInteriorBlochGap
    exact Real.sq_sqrt (sub_nonneg.mpr hTruth.2.le)
  have hslt : mixedRadialGap theta < 1 := by
    have hnorm : 0 < QubitOracle.blochNormSq theta := hTruth.1
    unfold mixedInteriorBlochGap at hsq
    nlinarith
  have hexcess := mixedEqualCycleFrobenius_excess_eq theta hTruth
  nlinarith [sq_pos_of_pos (sub_pos.mpr hslt)]

#print axioms localRadialTangentCoordinateMatrix_orthogonal
#print axioms localRadialTangentTransform_mixedBuresTarget
#print axioms localRadialTangentTransform_mixedRawBlochBuresInfidelityWeight
#print axioms mixedBuresInfidelityGaussianBenchmark_eq_nine_fourths
#print axioms mixedEqualCycleFrobeniusBenchmark_eq
#print axioms mixedFrobeniusOptimalAllocationBenchmark_eq
#print axioms mixedEqualCycleFrobenius_excess_eq
#print axioms mixedEqualCycleFrobenius_not_optimal_of_nonzero

end

end QubitOracle.Paper
