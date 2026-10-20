import QubitOracle.Paper.QubitFoundations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import QubitOracle.FiniteGillMassar
/-!
# Coordinate-free mixed-qubit oracle geometry

This module supplies the geometric bridge omitted by the earlier diagonal
optimizer.  A real `3 x 3` matrix `T` represents `J^{-1/2}`.  Axis information
is normalized by `||T u||^2`; congruence by `T` therefore produces the unit
rank-one projector associated with the paper's map `x(u)`.  An inverse square
root `S` realizes every unit rank-one projector, which is the physically
relevant (axis-sign invariant) surjectivity statement.
-/

namespace QubitOracle.Paper

open scoped BigOperators
open MeasureTheory

noncomputable section

abbrev OracleMatrix := Matrix (Fin 3) (Fin 3) ℝ

/-- Euclidean normalization of a Bloch vector. -/
def oracleNormalize (v : Fin 3 -> ℝ) : Fin 3 -> ℝ :=
  (Real.sqrt (blochNormSq v))⁻¹ • v

/-- The paper's normalized coordinate map with `T = J^{-1/2}`. -/
def oracleXMap (T : OracleMatrix) (u : Fin 3 -> ℝ) : Fin 3 -> ℝ :=
  oracleNormalize (T.mulVec u)

/-- Rank-one projector normalized by the squared Euclidean norm. -/
def oracleNormalizedOuter (v : Fin 3 -> ℝ) : OracleMatrix :=
  (blochNormSq v)⁻¹ • blochOuter v

/-- Axis information written in terms of `T = J^{-1/2}`. -/
def oracleAxisInformation (T : OracleMatrix) (u : Fin 3 -> ℝ) : OracleMatrix :=
  (blochNormSq (T.mulVec u))⁻¹ • blochOuter u

/-- The inverse axis map with `S = J^{1/2}`. -/
def oracleInverseXMap (S : OracleMatrix) (x : Fin 3 -> ℝ) : Fin 3 -> ℝ :=
  oracleNormalize (S.mulVec x)

/-- General measure-valued design information. -/
def mixedDesignInformation {U : Type*} [MeasurableSpace U]
    (axisInformation : U -> OracleMatrix) (xi : Measure U) : OracleMatrix :=
  fun i j => ∫ u, axisInformation u i j ∂xi

/-- The quadratic local-risk design criterion. -/
def mixedDesignCriterion (G M : OracleMatrix) : ℝ :=
  Matrix.trace (G * M⁻¹)

/-- Coordinate-free Gill--Massar relaxation represented by a normalized
information matrix `A`. -/
def GillMassarRelaxedRepresentation
    (S M : OracleMatrix) : Prop :=
  ∃ A : OracleMatrix,
    A.PosSemidef ∧ Matrix.trace A ≤ 1 ∧ M = S * A * S.transpose

theorem oracleNormalize_normSq_eq_one (v : Fin 3 -> ℝ)
    (hv : 0 < blochNormSq v) :
    blochNormSq (oracleNormalize v) = 1 := by
  calc
    blochNormSq (oracleNormalize v) =
        blochNormSq v / (Real.sqrt (blochNormSq v)) ^ 2 := by
      simp [oracleNormalize, blochNormSq, Fin.sum_univ_succ]
      ring
    _ = 1 := by
      rw [Real.sq_sqrt hv.le, div_self hv.ne']

theorem oracleXMap_normSq_eq_one (T : OracleMatrix) (u : Fin 3 -> ℝ)
    (hu : 0 < blochNormSq (T.mulVec u)) :
    blochNormSq (oracleXMap T u) = 1 :=
  oracleNormalize_normSq_eq_one (T.mulVec u) hu

theorem blochOuter_oracleNormalize_eq_normalizedOuter
    (v : Fin 3 -> ℝ) (hv : 0 < blochNormSq v) :
    blochOuter (oracleNormalize v) = oracleNormalizedOuter v := by
  have hs : Real.sqrt (blochNormSq v) ≠ 0 :=
    (Real.sqrt_pos.2 hv).ne'
  have hs2 : (Real.sqrt (blochNormSq v)) ^ 2 = blochNormSq v :=
    Real.sq_sqrt hv.le
  ext i j
  simp [oracleNormalize, oracleNormalizedOuter, blochOuter]
  field_simp [hs, hv.ne']
  rw [hs2]
  ring

/-- Congruence sends a rank-one outer product to the outer product of the
transformed vector. -/
theorem oracle_congruence_blochOuter (T : OracleMatrix) (u : Fin 3 -> ℝ) :
    T * blochOuter u * T.transpose = blochOuter (T.mulVec u) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blochOuter, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;> ring

/-- The norm in the `J^{-1/2}` coordinates is the quadratic form with
`J^{-1} = T^T T`. -/
theorem oracle_transform_normSq_eq_quadratic
    (T : OracleMatrix) (u : Fin 3 -> ℝ) :
    blochNormSq (T.mulVec u) =
      blochDot u ((T.transpose * T).mulVec u) := by
  simp [blochNormSq, blochDot, Matrix.mul_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ]
  ring

/-- The normalized axis map gives exactly the transformed rank-one Fisher
information in Eq. (SI-rank-one-map). -/
theorem oracle_rank_one_map (T : OracleMatrix) (u : Fin 3 -> ℝ)
    (hu : 0 < blochNormSq (T.mulVec u)) :
    T * oracleAxisInformation T u * T.transpose =
      blochOuter (oracleXMap T u) := by
  rw [oracleXMap,
    blochOuter_oracleNormalize_eq_normalizedOuter _ hu]
  unfold oracleAxisInformation oracleNormalizedOuter
  rw [← oracle_congruence_blochOuter T u]
  simp

/-- The same congruence identity before choosing a normalized vector
representative.  This form does not require a nonzero axis hypothesis. -/
theorem oracle_rank_one_map_normalized
    (T : OracleMatrix) (u : Fin 3 -> ℝ) :
    T * oracleAxisInformation T u * T.transpose =
      oracleNormalizedOuter (T.mulVec u) := by
  unfold oracleAxisInformation oracleNormalizedOuter
  rw [← oracle_congruence_blochOuter T u]
  simp

theorem oracleNormalizedOuter_of_normSq_one (x : Fin 3 -> ℝ)
    (hx : blochNormSq x = 1) :
    oracleNormalizedOuter x = blochOuter x := by
  simp [oracleNormalizedOuter, hx]

theorem oracleNormalizedOuter_smul (c : ℝ) (x : Fin 3 -> ℝ)
    (hc : c ≠ 0) (hx : 0 < blochNormSq x) :
    oracleNormalizedOuter (c • x) = oracleNormalizedOuter x := by
  ext i j
  simp [oracleNormalizedOuter, blochNormSq, blochOuter,
    Fin.sum_univ_succ]
  field_simp [hc, hx.ne'] <;> ring

/-- Matrix inverse roots act inversely on vectors. -/
theorem oracle_inverse_roots_mulVec (S T : OracleMatrix)
    (x : Fin 3 -> ℝ) (hTS : T * S = 1) :
    T.mulVec (S.mulVec x) = x := by
  rw [Matrix.mulVec_mulVec, hTS]
  simp

/-- The inverse map has unit norm whenever `S x` is nonzero. -/
theorem oracleInverseXMap_normSq_eq_one (S : OracleMatrix)
    (x : Fin 3 -> ℝ) (hSx : 0 < blochNormSq (S.mulVec x)) :
    blochNormSq (oracleInverseXMap S x) = 1 :=
  oracleNormalize_normSq_eq_one (S.mulVec x) hSx

/-- Projective surjectivity of the inverse axis map.  Equality of outer
products is the correct physical statement because `u` and `-u` define the
same binary projective measurement. -/
theorem oracleInverseXMap_realizes_projector
    (S T : OracleMatrix) (x : Fin 3 -> ℝ)
    (hTS : T * S = 1) (hx : blochNormSq x = 1)
    (hSx : 0 < blochNormSq (S.mulVec x)) :
    oracleNormalizedOuter (T.mulVec (oracleInverseXMap S x)) =
      blochOuter x := by
  have hs : Real.sqrt (blochNormSq (S.mulVec x)) ≠ 0 :=
    (Real.sqrt_pos.2 hSx).ne'
  have hmap : T.mulVec (S.mulVec x) = x :=
    oracle_inverse_roots_mulVec S T x hTS
  have hscaled :
      T.mulVec (oracleInverseXMap S x) =
        (Real.sqrt (blochNormSq (S.mulVec x)))⁻¹ • x := by
    rw [oracleInverseXMap, oracleNormalize, Matrix.mulVec_smul, hmap]
  rw [hscaled, oracleNormalizedOuter_smul _ x (inv_ne_zero hs)]
  · exact oracleNormalizedOuter_of_normSq_one x hx
  · simpa [hx]

end

end QubitOracle.Paper
