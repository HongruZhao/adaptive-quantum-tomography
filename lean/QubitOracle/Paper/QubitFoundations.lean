import QubitOracle.Paper.MixedAxisFisher
import Mathlib
import QubitOracle.FiniteGillMassar
/-!
# Mixed-qubit matrix, SLD, and QFI foundations

This module checks the explicit two-by-two matrix calculations used in the
main paper and Supplementary Note 1.  It does not invoke the general
Gill--Massar axiom.
-/

namespace QubitOracle.Paper

open scoped BigOperators

noncomputable section

/-- Complex two-by-two matrices used for qubit states and observables. -/
abbrev QubitMatrix := Matrix (Fin 2) (Fin 2) ℂ

/-- The Pauli-linear matrix `x^T sigma` in the `(x,y,z)` coordinate order. -/
def pauliLinear (x : Fin 3 -> ℝ) : QubitMatrix :=
  !![(x 2 : ℂ), (x 0 : ℂ) - Complex.I * (x 1 : ℂ);
     (x 0 : ℂ) + Complex.I * (x 1 : ℂ), -(x 2 : ℂ)]

/-- Three-dimensional cross product in the paper's Bloch coordinates. -/
def cross3 (x z : Fin 3 -> ℝ) : Fin 3 -> ℝ :=
  ![x 1 * z 2 - x 2 * z 1,
    x 2 * z 0 - x 0 * z 2,
    x 0 * z 1 - x 1 * z 0]

/-- The Pauli product identity
`(x^T sigma)(z^T sigma) = (x^T z) I + i (x cross z)^T sigma`. -/
theorem pauliLinear_mul (x z : Fin 3 -> ℝ) :
    pauliLinear x * pauliLinear z =
      (blochDot x z : ℂ) • (1 : QubitMatrix) +
        Complex.I • pauliLinear (cross3 x z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliLinear, cross3, blochDot, Matrix.mul_apply,
      Fin.sum_univ_succ] <;>
    ring_nf <;>
    simp [pow_two, Complex.I_mul_I, sub_eq_add_neg]

/-- Affine Pauli representation `a I + b^T sigma`. -/
def affinePauli (a : ℝ) (b : Fin 3 -> ℝ) : QubitMatrix :=
  (a : ℂ) • (1 : QubitMatrix) + pauliLinear b

/-- Mixed-qubit density-matrix parameterization. -/
def qubitDensityMatrix (theta : Fin 3 -> ℝ) : QubitMatrix :=
  (1 / 2 : ℂ) • ((1 : QubitMatrix) + pauliLinear theta)

/-- The Bloch parameterization has unit trace. -/
theorem qubitDensityMatrix_trace (theta : Fin 3 -> ℝ) :
    (qubitDensityMatrix theta).trace = 1 := by
  simp [qubitDensityMatrix, pauliLinear, Matrix.trace,
    Fin.sum_univ_succ]
  ring

/-- Entrywise Hermitian symmetry of the Bloch density matrix. -/
theorem qubitDensityMatrix_hermitian_symmetry
    (theta : Fin 3 -> ℝ) (i j : Fin 2) :
    qubitDensityMatrix theta i j =
      star (qubitDensityMatrix theta j i) := by
  fin_cases i <;> fin_cases j <;>
    simp [qubitDensityMatrix, pauliLinear, Matrix.one_apply] <;>
    norm_num <;> ring

/-- Axis projective effect `(I + y u^T sigma)/2`. -/
def axisProjectorMatrix (u : Fin 3 -> ℝ) (y : ℝ) : QubitMatrix :=
  (1 / 2 : ℂ) • ((1 : QubitMatrix) + (y : ℂ) • pauliLinear u)

/-- Every axis effect has unit trace. -/
theorem axisProjectorMatrix_trace (u : Fin 3 -> ℝ) (y : ℝ) :
    (axisProjectorMatrix u y).trace = 1 := by
  simp [axisProjectorMatrix, pauliLinear, Matrix.trace,
    Fin.sum_univ_succ]
  ring

/-- Entrywise Hermitian symmetry of an axis effect. -/
theorem axisProjectorMatrix_hermitian_symmetry
    (u : Fin 3 -> ℝ) (y : ℝ) (i j : Fin 2) :
    axisProjectorMatrix u y i j =
      star (axisProjectorMatrix u y j i) := by
  fin_cases i <;> fin_cases j <;>
    simp [axisProjectorMatrix, pauliLinear, Matrix.one_apply] <;>
    norm_num <;> ring <;> aesop

/-- Matrix Born probability for a Bloch state and axis effect. -/
def qubitBornTrace (theta u : Fin 3 -> ℝ) (y : ℝ) : ℝ :=
  (Matrix.trace (qubitDensityMatrix theta * axisProjectorMatrix u y)).re

/-- Direct matrix proof of the affine Bloch Born rule. -/
theorem qubitBornTrace_eq (theta u : Fin 3 -> ℝ) (y : ℝ) :
    qubitBornTrace theta u y =
      (1 + y * blochDot u theta) / 2 := by
  simp [qubitBornTrace, qubitDensityMatrix, axisProjectorMatrix,
    pauliLinear, Matrix.trace, Matrix.mul_apply, blochDot,
    Fin.sum_univ_succ]
  ring

/-- Standard coordinate vector in the three-dimensional Bloch chart. -/
def standardBasis3 (j : Fin 3) : Fin 3 -> ℝ :=
  fun k => if k = j then 1 else 0

/-- Derivative `partial rho / partial theta_j = sigma_j / 2`. -/
def qubitDensityDerivative (j : Fin 3) : QubitMatrix :=
  (1 / 2 : ℂ) • pauliLinear (standardBasis3 j)

/-- Scalar coefficient of the explicit symmetric logarithmic derivative. -/
def sldScalar (theta : Fin 3 -> ℝ) (j : Fin 3) : ℝ :=
  -theta j / (1 - blochNormSq theta)

/-- Pauli-vector coefficient of the explicit SLD. -/
def sldVector (theta : Fin 3 -> ℝ) (j : Fin 3) : Fin 3 -> ℝ :=
  fun k => standardBasis3 j k +
    theta j / (1 - blochNormSq theta) * theta k

/-- Explicit SLD matrix `a_j I + b_j^T sigma`. -/
def sldMatrix (theta : Fin 3 -> ℝ) (j : Fin 3) : QubitMatrix :=
  affinePauli (sldScalar theta j) (sldVector theta j)

/-- General anticommutator expansion used to solve the SLD equation. -/
theorem qubit_sld_expand (theta b : Fin 3 -> ℝ) (a : ℝ) :
    (1 / 2 : ℂ) •
        (qubitDensityMatrix theta * affinePauli a b +
          affinePauli a b * qubitDensityMatrix theta) =
      (1 / 2 : ℂ) • affinePauli
        (a + blochDot theta b) (fun k => b k + a * theta k) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qubitDensityMatrix, affinePauli, pauliLinear,
      Matrix.mul_apply, Matrix.one_apply, blochDot,
      Fin.sum_univ_succ] <;>
    norm_num <;>
    ring_nf <;>
    simp [pow_two, Complex.I_mul_I]

/-- The displayed scalar/vector coefficients solve the two SLD equations. -/
theorem sld_coefficients_solve (theta : Fin 3 -> ℝ) (j : Fin 3)
    (htheta : blochNormSq theta < 1) :
    sldScalar theta j + blochDot theta (sldVector theta j) = 0 ∧
      (fun k => sldVector theta j k + sldScalar theta j * theta k) =
        standardBasis3 j := by
  have hden : 1 - blochNormSq theta ≠ 0 := by linarith
  constructor
  · fin_cases j <;>
      simp [sldScalar, sldVector, standardBasis3, blochDot,
        Fin.sum_univ_succ] <;>
      field_simp [hden] <;>
      simp [blochNormSq, Fin.sum_univ_succ] <;>
      ring <;> aesop
  · funext k
    simp [sldScalar, sldVector]
    ring

/-- The explicit SLD satisfies its defining matrix equation. -/
theorem qubit_sld_equation (theta : Fin 3 -> ℝ) (j : Fin 3)
    (htheta : blochNormSq theta < 1) :
    qubitDensityDerivative j =
      (1 / 2 : ℂ) •
        (qubitDensityMatrix theta * sldMatrix theta j +
          sldMatrix theta j * qubitDensityMatrix theta) := by
  rw [sldMatrix, qubit_sld_expand]
  obtain ⟨ha, hb⟩ := sld_coefficients_solve theta j htheta
  rw [ha, hb]
  simp [qubitDensityDerivative, affinePauli]

/-- Half the anticommutator of two affine Pauli matrices. -/
theorem symmetric_affinePauli_product
    (a c : ℝ) (b d : Fin 3 -> ℝ) :
    (1 / 2 : ℂ) •
        (affinePauli a b * affinePauli c d +
          affinePauli c d * affinePauli a b) =
      affinePauli (a * c + blochDot b d)
        (fun k => a * d k + c * b k) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [affinePauli, pauliLinear, Matrix.mul_apply, blochDot,
      Matrix.one_apply, Fin.sum_univ_succ] <;>
    norm_num <;>
    ring_nf <;>
    simp [pow_two, Complex.I_mul_I]

/-- Expectation of an affine Pauli observable in a Bloch state. -/
theorem trace_qubitDensityMatrix_mul_affinePauli
    (theta b : Fin 3 -> ℝ) (a : ℝ) :
    Matrix.trace (qubitDensityMatrix theta * affinePauli a b) =
      (a + blochDot theta b : ℂ) := by
  simp [qubitDensityMatrix, affinePauli, pauliLinear, Matrix.trace,
    Matrix.mul_apply, blochDot, Fin.sum_univ_succ]
  ring_nf
  simp [pow_two, Complex.I_mul_I]

/-- Symmetrized product appearing in the SLD Fisher definition. -/
def symmetricSLDProduct (theta : Fin 3 -> ℝ) (j k : Fin 3) : QubitMatrix :=
  (1 / 2 : ℂ) •
    (sldMatrix theta j * sldMatrix theta k +
      sldMatrix theta k * sldMatrix theta j)

/-- QFI defined directly by the SLD trace formula. -/
def qubitSLDFisherFromSLD (theta : Fin 3 -> ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  fun j k =>
    (Matrix.trace
      (qubitDensityMatrix theta * symmetricSLDProduct theta j k)).re

/-- Closed-form QFI matrix in Bloch coordinates. -/
def qubitSLDFisher (theta : Fin 3 -> ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  fun j k => (if j = k then 1 else 0) +
    theta j * theta k / (1 - blochNormSq theta)

/-- The SLD trace definition gives the displayed closed-form QFI. -/
theorem qubitSLDFisherFromSLD_eq_formula (theta : Fin 3 -> ℝ)
    (htheta : blochNormSq theta < 1) :
    qubitSLDFisherFromSLD theta = qubitSLDFisher theta := by
  have hden : 1 - blochNormSq theta ≠ 0 := by linarith
  ext j k
  simp only [qubitSLDFisherFromSLD, symmetricSLDProduct, sldMatrix]
  rw [symmetric_affinePauli_product,
    trace_qubitDensityMatrix_mul_affinePauli]
  change
    (sldScalar theta j * sldScalar theta k +
        blochDot (sldVector theta j) (sldVector theta k)) +
      blochDot theta (fun l =>
        sldScalar theta j * sldVector theta k l +
          sldScalar theta k * sldVector theta j l) =
      qubitSLDFisher theta j k
  fin_cases j <;> fin_cases k <;>
    simp [qubitSLDFisher, sldScalar, sldVector, standardBasis3,
      blochDot, Fin.sum_univ_succ] <;>
    field_simp [hden] <;>
    simp [blochNormSq, Fin.sum_univ_succ] <;>
    ring <;> aesop

/-- The closed-form QFI times `I - theta theta^T` is the identity. -/
theorem qubitSLDFisher_mul_inv (theta : Fin 3 -> ℝ)
    (htheta : blochNormSq theta < 1) :
    qubitSLDFisher theta * qubitSLDFisherInv theta = 1 := by
  have hden : 1 - blochNormSq theta ≠ 0 := by linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qubitSLDFisher, qubitSLDFisherInv, Matrix.mul_apply,
      Fin.sum_univ_succ] <;>
    field_simp [hden] <;>
    simp [blochNormSq, Fin.sum_univ_succ] <;>
    ring <;> aesop

/-- `I - theta theta^T` times the closed-form QFI is the identity. -/
theorem qubitSLDFisherInv_mul (theta : Fin 3 -> ℝ)
    (htheta : blochNormSq theta < 1) :
    qubitSLDFisherInv theta * qubitSLDFisher theta = 1 := by
  have hden : 1 - blochNormSq theta ≠ 0 := by linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qubitSLDFisher, qubitSLDFisherInv, Matrix.mul_apply,
      Fin.sum_univ_succ] <;>
    field_simp [hden] <;>
    simp [blochNormSq, Fin.sum_univ_succ] <;>
    ring <;> aesop

/-- The displayed QFI is the inverse of `I - theta theta^T`. -/
theorem qubitSLDFisher_eq_inv (theta : Fin 3 -> ℝ)
    (htheta : blochNormSq theta < 1) :
    qubitSLDFisher theta = (qubitSLDFisherInv theta)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  exact qubitSLDFisherInv_mul theta htheta

end

end QubitOracle.Paper
