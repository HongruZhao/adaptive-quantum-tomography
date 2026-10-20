import QubitOracle.Paper.PureMultilevelLossConstants
import QubitOracle.Paper.PureMultilevelDeterministicGeometryClosed
import QubitOracle.Paper.PureMultilevelProjectorGeometry
import QubitOracle.Paper.PureStateFoundations
import QubitOracle.Paper.QuantumDistances
/-!
# Physical trace distance for finite-dimensional pure states

This module proves the matrix trace-norm formula for two normalized rank-one
density matrices in every fixed finite dimension.  The proof is internal:
rank-one projector algebra gives a cubic identity, positivity and square-root
uniqueness evaluate Mathlib's continuous-functional-calculus square root, and
the resulting trace is computed exactly.  No literature theorem is assumed.
-/

namespace QubitOracle.Paper
namespace PureMultilevelMatrixTraceDistance

open scoped BigOperators ComplexOrder MatrixOrder
open PureMultilevelDeterministicGeometry

noncomputable section

variable {d : Type*} [Fintype d] [DecidableEq d]

private def rankOneCross (u v : d → ℂ) : Matrix d d ℂ :=
  fun i j => u i * star (v j)

private theorem rankOneCross_self (u : d → ℂ) :
    rankOneCross u u = rankOneDensity u := rfl

private theorem rankOneCross_mul (u v w z : d → ℂ) :
    rankOneCross u v * rankOneCross w z =
      basisBornAmplitude v w • rankOneCross u z := by
  ext i j
  change (∑ k, (u i * star (v k)) * (w k * star (z j))) =
    (∑ k, star (v k) * w k) * (u i * star (z j))
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

private theorem basisBornAmplitude_self (u : d → ℂ) :
    basisBornAmplitude u u = (pureStateNormSq u : ℂ) := by
  unfold basisBornAmplitude pureStateNormSq
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

private theorem basisBornAmplitude_swap (u v : d → ℂ) :
    basisBornAmplitude v u = star (basisBornAmplitude u v) := by
  unfold basisBornAmplitude
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp
  ring

private theorem rankOneDensity_mul_self (u : d → ℂ)
    (hu : pureStateNormSq u = 1) :
    rankOneDensity u * rankOneDensity u = rankOneDensity u := by
  rw [← rankOneCross_self, rankOneCross_mul, basisBornAmplitude_self, hu]
  simp

private theorem rankOneDensity_star (u : d → ℂ) :
    star (rankOneDensity u) = rankOneDensity u := by
  ext i j
  simp [Matrix.star_apply, rankOneDensity]
  ring

theorem rankOneDensity_sandwich_fidelity (u v : d → ℂ) :
    rankOneDensity u * rankOneDensity v * rankOneDensity u =
      (pureMultilevelFidelity u v : ℂ) • rankOneDensity u := by
  rw [← rankOneCross_self u, ← rankOneCross_self v]
  rw [rankOneCross_mul, Algebra.smul_mul_assoc]
  rw [rankOneCross_mul, smul_smul]
  rw [basisBornAmplitude_swap u v]
  unfold pureMultilevelFidelity basisBornProbability
  rw [Complex.normSq_eq_conj_mul_self]
  exact congrArg (fun c : ℂ => c • rankOneCross u u) (mul_comm _ _)

theorem pureDensityDifference_cube
    (psi phi : d → ℂ)
    (hPsi : pureStateNormSq psi = 1)
    (hPhi : pureStateNormSq phi = 1) :
    let A := rankOneDensity psi - rankOneDensity phi
    let s := pureMultilevelInfidelity psi phi
    A * A * A = s • A := by
  dsimp only
  let P := rankOneDensity psi
  let Q := rankOneDensity phi
  have hP2 : P * P = P := rankOneDensity_mul_self psi hPsi
  have hQ2 : Q * Q = Q := rankOneDensity_mul_self phi hPhi
  have hPQP : P * Q * P = (pureMultilevelFidelity psi phi : ℂ) • P :=
    rankOneDensity_sandwich_fidelity psi phi
  have hQPQ : Q * P * Q = (pureMultilevelFidelity phi psi : ℂ) • Q :=
    rankOneDensity_sandwich_fidelity phi psi
  have hFsym : pureMultilevelFidelity phi psi = pureMultilevelFidelity psi phi := by
    unfold pureMultilevelFidelity basisBornProbability
    rw [basisBornAmplitude_swap psi phi]
    simp
  rw [show (P - Q) * (P - Q) * (P - Q) =
      P * P * P - P * P * Q - P * Q * P + P * Q * Q -
        Q * P * P + Q * P * Q + Q * Q * P - Q * Q * Q by noncomm_ring]
  simp only [hP2, hQ2]
  rw [hPQP, hQPQ, hFsym]
  rw [mul_assoc P Q Q, hQ2, mul_assoc Q P P, hP2]
  unfold pureMultilevelInfidelity
  dsimp [P, Q]
  module

end
end PureMultilevelMatrixTraceDistance
end QubitOracle.Paper

namespace QubitOracle.Paper
namespace PureMultilevelMatrixTraceDistance

open scoped BigOperators ComplexOrder MatrixOrder
open PureMultilevelDeterministicGeometry PureMultilevelProjectorGeometry

noncomputable section

variable {d : Type*} [Fintype d] [DecidableEq d]

theorem trace_star_mul_self_re_eq_entrywise (A : Matrix d d ℂ) :
    (Matrix.trace (star A * A)).re =
      ∑ i, ∑ j, Complex.normSq (A i j) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply]
  simp_rw [Complex.re_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [Complex.normSq_apply]
  simp

end
end PureMultilevelMatrixTraceDistance
end QubitOracle.Paper

namespace QubitOracle.Paper
namespace PureMultilevelMatrixTraceDistance

open scoped BigOperators ComplexOrder MatrixOrder
open PureMultilevelDeterministicGeometry PureMultilevelProjectorGeometry

noncomputable section

variable {d : Type*} [Fintype d] [DecidableEq d]

def pureDensityDifference (psi phi : d → ℂ) : Matrix d d ℂ :=
  rankOneDensity psi - rankOneDensity phi

def pureDensityDifferenceSquare (psi phi : d → ℂ) : Matrix d d ℂ :=
  star (pureDensityDifference psi phi) * pureDensityDifference psi phi

private theorem pureDensityDifference_star (psi phi : d → ℂ) :
    star (pureDensityDifference psi phi) = pureDensityDifference psi phi := by
  simp [pureDensityDifference, rankOneDensity_star]

private theorem pureDensityDifferenceSquare_eq_mul_self (psi phi : d → ℂ) :
    pureDensityDifferenceSquare psi phi =
      pureDensityDifference psi phi * pureDensityDifference psi phi := by
  rw [pureDensityDifferenceSquare, pureDensityDifference_star]

private theorem pureDensityDifferenceSquare_nonneg (psi phi : d → ℂ) :
    0 ≤ pureDensityDifferenceSquare psi phi := by
  exact star_mul_self_nonneg _

private theorem pureDensityDifferenceSquare_sq
    (psi phi : d → ℂ)
    (hPsi : pureStateNormSq psi = 1)
    (hPhi : pureStateNormSq phi = 1) :
    pureDensityDifferenceSquare psi phi * pureDensityDifferenceSquare psi phi =
      pureMultilevelInfidelity psi phi • pureDensityDifferenceSquare psi phi := by
  have hcube :
      pureDensityDifference psi phi * pureDensityDifference psi phi *
          pureDensityDifference psi phi =
        pureMultilevelInfidelity psi phi • pureDensityDifference psi phi := by
    simpa [pureDensityDifference] using pureDensityDifference_cube psi phi hPsi hPhi
  rw [pureDensityDifferenceSquare_eq_mul_self]
  calc
    (pureDensityDifference psi phi * pureDensityDifference psi phi) *
        (pureDensityDifference psi phi * pureDensityDifference psi phi) =
      (pureDensityDifference psi phi * pureDensityDifference psi phi *
        pureDensityDifference psi phi) * pureDensityDifference psi phi := by
          noncomm_ring
    _ = (pureMultilevelInfidelity psi phi • pureDensityDifference psi phi) *
        pureDensityDifference psi phi := by
          rw [hcube]
    _ = pureMultilevelInfidelity psi phi •
        (pureDensityDifference psi phi * pureDensityDifference psi phi) := by
          rw [smul_mul_assoc]

private theorem matrix_eq_zero_of_entrywiseNormSq_sum_eq_zero
    (A : Matrix d d ℂ)
    (hA : (∑ i, ∑ j, Complex.normSq (A i j)) = 0) :
    A = 0 := by
  ext i j
  have hOuter := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i hi => Finset.sum_nonneg (fun j hj => Complex.normSq_nonneg (A i j)))).mp hA
  have hInner : (∑ j, Complex.normSq (A i j)) = 0 := hOuter i (Finset.mem_univ i)
  have hEntry := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j hj => Complex.normSq_nonneg (A i j))).mp hInner
  exact Complex.normSq_eq_zero.mp (hEntry j (Finset.mem_univ j))

private theorem pureDensityDifference_entrywiseNormSq_sum
    {n : ℕ} (psi phi : Fin (n + 1) → ℂ)
    (hPsi : pureStateNormSq psi = 1)
    (hPhi : pureStateNormSq phi = 1) :
    (∑ i, ∑ j, Complex.normSq (pureDensityDifference psi phi i j)) =
      2 * pureMultilevelInfidelity psi phi := by
  change pureRankOneDensityFrobeniusSq psi phi = _
  exact pureRankOneDensityFrobeniusSq_eq_two_infidelity psi phi hPsi hPhi

private theorem pureDensityDifference_eq_zero_of_infidelity_eq_zero
    {n : ℕ} (psi phi : Fin (n + 1) → ℂ)
    (hPsi : pureStateNormSq psi = 1)
    (hPhi : pureStateNormSq phi = 1)
    (hs : pureMultilevelInfidelity psi phi = 0) :
    pureDensityDifference psi phi = 0 := by
  apply matrix_eq_zero_of_entrywiseNormSq_sum_eq_zero
  rw [pureDensityDifference_entrywiseNormSq_sum psi phi hPsi hPhi, hs]
  ring

end
end PureMultilevelMatrixTraceDistance
end QubitOracle.Paper

namespace QubitOracle.Paper
namespace PureMultilevelMatrixTraceDistance

open scoped BigOperators ComplexOrder MatrixOrder
open PureMultilevelDeterministicGeometry PureMultilevelProjectorGeometry

noncomputable section

theorem pureDensityDifferenceSquare_sqrt_of_pos
    {n : ℕ} (psi phi : Fin (n + 1) → ℂ)
    (hPsi : pureStateNormSq psi = 1)
    (hPhi : pureStateNormSq phi = 1)
    (hs : 0 < pureMultilevelInfidelity psi phi) :
    CFC.sqrt (pureDensityDifferenceSquare psi phi) =
      (1 / Real.sqrt (pureMultilevelInfidelity psi phi)) •
        pureDensityDifferenceSquare psi phi := by
  let s := pureMultilevelInfidelity psi phi
  let B := pureDensityDifferenceSquare psi phi
  have hBsq : B * B = s • B :=
    pureDensityDifferenceSquare_sq psi phi hPsi hPhi
  have hBnonneg : 0 ≤ B := pureDensityDifferenceSquare_nonneg psi phi
  have hsqrtPos : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hsqrtSq : Real.sqrt s ^ 2 = s := Real.sq_sqrt (le_of_lt hs)
  have hcoefficient :
      (1 / Real.sqrt s) * (1 / Real.sqrt s) * s = 1 := by
    field_simp [ne_of_gt hsqrtPos]
    nlinarith
  apply CFC.sqrt_unique
  · calc
      ((1 / Real.sqrt s) • B) * ((1 / Real.sqrt s) • B) =
          ((1 / Real.sqrt s) * (1 / Real.sqrt s)) • (B * B) := by
            rw [smul_mul_smul]
      _ = ((1 / Real.sqrt s) * (1 / Real.sqrt s)) • (s • B) := by
            rw [hBsq]
      _ = (((1 / Real.sqrt s) * (1 / Real.sqrt s)) * s) • B := by
            rw [smul_smul]
      _ = B := by rw [hcoefficient]; simp
  · exact smul_nonneg (by positivity) hBnonneg

end
end PureMultilevelMatrixTraceDistance
end QubitOracle.Paper

namespace QubitOracle.Paper
namespace PureMultilevelMatrixTraceDistance

open scoped BigOperators ComplexOrder MatrixOrder
open PureMultilevelDeterministicGeometry PureMultilevelProjectorGeometry

noncomputable section

/-- Exact trace norm of the difference of two normalized pure-state
projectors in arbitrary fixed finite dimension. -/
theorem matrixTraceNorm_rankOneDensity_sub
    {n : ℕ} (psi phi : Fin (n + 1) → ℂ)
    (hPsi : pureStateNormSq psi = 1)
    (hPhi : pureStateNormSq phi = 1) :
    matrixTraceNorm (rankOneDensity psi - rankOneDensity phi) =
      2 * Real.sqrt (pureMultilevelInfidelity psi phi) := by
  let s := pureMultilevelInfidelity psi phi
  have hsNonneg : 0 ≤ s := by
    dsimp [s]
    unfold pureMultilevelInfidelity
    linarith [normalized_pureMultilevelFidelity_le_one psi phi hPsi hPhi]
  change (Matrix.trace (CFC.sqrt (pureDensityDifferenceSquare psi phi))).re =
    2 * Real.sqrt s
  by_cases hsZero : s = 0
  · have hAZero : pureDensityDifference psi phi = 0 :=
      pureDensityDifference_eq_zero_of_infidelity_eq_zero psi phi hPsi hPhi hsZero
    have hBZero : pureDensityDifferenceSquare psi phi = 0 := by
      simp [pureDensityDifferenceSquare, hAZero]
    rw [hBZero, CFC.sqrt_zero]
    simp [hsZero]
  · have hsPos : 0 < s := lt_of_le_of_ne hsNonneg (Ne.symm hsZero)
    rw [pureDensityDifferenceSquare_sqrt_of_pos psi phi hPsi hPhi hsPos]
    rw [Matrix.trace_smul, Complex.smul_re]
    have hTrace : (Matrix.trace (pureDensityDifferenceSquare psi phi)).re =
        2 * s := by
      rw [pureDensityDifferenceSquare, trace_star_mul_self_re_eq_entrywise,
        pureDensityDifference_entrywiseNormSq_sum psi phi hPsi hPhi]
    rw [hTrace]
    change (1 / Real.sqrt s) * (2 * s) = 2 * Real.sqrt s
    have hsqrtPos : 0 < Real.sqrt s := Real.sqrt_pos.2 hsPos
    have hsqrtSq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hsNonneg
    field_simp [ne_of_gt hsqrtPos]
    nlinarith

end
end PureMultilevelMatrixTraceDistance
end QubitOracle.Paper

namespace QubitOracle.Paper
namespace PureMultilevelMatrixTraceDistance

open scoped BigOperators ComplexOrder MatrixOrder
open PureMultilevelDeterministicGeometry PureMultilevelProjectorGeometry

noncomputable section

private def pureStateRow {n : ℕ} (psi : Fin (n + 1) → ℂ) :
    Matrix (Fin 1) (Fin (n + 1)) ℂ :=
  fun _ j => star (psi j)

private theorem pureStateRow_star_mul_self
    {n : ℕ} (psi : Fin (n + 1) → ℂ) :
    (pureStateRow psi).conjTranspose * pureStateRow psi = rankOneDensity psi := by
  ext i j
  simp [pureStateRow, Matrix.mul_apply, rankOneDensity, Matrix.star_apply]

/-- A normalized finite-dimensional vector, packaged as a physical density
matrix using a kernel-proved positivity witness. -/
noncomputable def normalizedPureDensityMatrix
    {n : ℕ} (psi : Fin (n + 1) → ℂ)
    (hPsi : pureStateNormSq psi = 1) :
    FiniteDensityMatrix (Fin (n + 1)) where
  val := rankOneDensity psi
  pos := by
    rw [← pureStateRow_star_mul_self psi]
    exact Matrix.posSemidef_conjTranspose_mul_self (pureStateRow psi)
  trace_one := rankOneDensity_trace_eq_one psi hPsi

/-- Physical trace distance of normalized pure states equals the square root
of infidelity in every fixed finite dimension. -/
theorem quantumTraceDistance_normalizedPureDensityMatrix
    {n : ℕ} (psi phi : Fin (n + 1) → ℂ)
    (hPsi : pureStateNormSq psi = 1)
    (hPhi : pureStateNormSq phi = 1) :
    quantumTraceDistance
        (normalizedPureDensityMatrix psi hPsi)
        (normalizedPureDensityMatrix phi hPhi) =
      Real.sqrt (pureMultilevelInfidelity psi phi) := by
  rw [quantumTraceDistance]
  change (1 / 2 : ℝ) *
      matrixTraceNorm (rankOneDensity psi - rankOneDensity phi) = _
  rw [matrixTraceNorm_rankOneDensity_sub psi phi hPsi hPhi]
  ring

/-- Squared physical trace distance of normalized pure states is exactly
infidelity. -/
theorem quantumTraceDistance_sq_normalizedPureDensityMatrix
    {n : ℕ} (psi phi : Fin (n + 1) → ℂ)
    (hPsi : pureStateNormSq psi = 1)
    (hPhi : pureStateNormSq phi = 1) :
    quantumTraceDistance
        (normalizedPureDensityMatrix psi hPsi)
        (normalizedPureDensityMatrix phi hPhi) ^ 2 =
      pureMultilevelInfidelity psi phi := by
  rw [quantumTraceDistance_normalizedPureDensityMatrix psi phi hPsi hPhi]
  apply Real.sq_sqrt
  unfold pureMultilevelInfidelity
  linarith [normalized_pureMultilevelFidelity_le_one psi phi hPsi hPhi]

/-- For any two pure states in finite dimension, squared trace distance is
one half of squared density-matrix Frobenius distance. -/
theorem pure_quantumTraceDistance_sq_eq_half_frobenius
    {n : ℕ} (psi phi : Fin (n + 1) → ℂ)
    (hPsi : pureStateNormSq psi = 1)
    (hPhi : pureStateNormSq phi = 1) :
    quantumTraceDistance
        (normalizedPureDensityMatrix psi hPsi)
        (normalizedPureDensityMatrix phi hPhi) ^ 2 =
      (1 / 2 : ℝ) * pureRankOneDensityFrobeniusSq psi phi := by
  rw [quantumTraceDistance_sq_normalizedPureDensityMatrix psi phi hPsi hPhi,
    pureRankOneDensityFrobeniusSq_eq_two_infidelity psi phi hPsi hPhi]
  ring

end
end PureMultilevelMatrixTraceDistance
end QubitOracle.Paper
