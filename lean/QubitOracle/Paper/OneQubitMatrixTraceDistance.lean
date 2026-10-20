import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.PureMultilevelMatrixTraceDistance
import QubitOracle.Paper.QuantumDistances
import QubitOracle.Paper.QubitFoundations
/-!
# Exact physical trace distance for Bloch qubits

This module connects the manuscript's Bloch-coordinate loss formula to the
matrix-defined trace norm from `QuantumDistances`.  The calculation is valid
for any pair of one-qubit density matrices, pure or mixed, once their Bloch
representations are supplied.  It uses Mathlib's continuous functional
calculus and no statistical or literature theorem.
-/

namespace QubitOracle.Paper

open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

private theorem blochNormSq_nonneg_traceDistance (x : Fin 3 → ℝ) :
    0 ≤ QubitOracle.blochNormSq x := by
  simp [QubitOracle.blochNormSq, Fin.sum_univ_succ]
  positivity

private def qubitDifferenceNN (theta eta : Fin 3 → ℝ) : NNReal :=
  ⟨(1 / 4 : ℝ) * QubitOracle.blochNormSq (theta - eta),
    mul_nonneg (by norm_num) (blochNormSq_nonneg_traceDistance _)⟩

private theorem star_pauliLinear (x : Fin 3 → ℝ) :
    star (pauliLinear x) = pauliLinear x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliLinear, Matrix.star_apply] <;> ring

private theorem cross3_self (x : Fin 3 → ℝ) : cross3 x x = 0 := by
  funext i
  fin_cases i <;> simp [cross3] <;> ring

private theorem blochDot_self (x : Fin 3 → ℝ) :
    QubitOracle.blochDot x x = QubitOracle.blochNormSq x := by
  simp [QubitOracle.blochDot, QubitOracle.blochNormSq, pow_two]

private theorem density_sub_eq_pauli (theta eta : Fin 3 → ℝ) :
    qubitDensityMatrix theta - qubitDensityMatrix eta =
      (1 / 2 : ℂ) • pauliLinear (theta - eta) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qubitDensityMatrix, pauliLinear] <;>
    norm_num <;> ring

private theorem algebraMap_qubitDifferenceNN (theta eta : Fin 3 → ℝ) :
    algebraMap NNReal QubitMatrix (qubitDifferenceNN theta eta) =
      (((1 / 4 : ℝ) * QubitOracle.blochNormSq (theta - eta) : ℝ) : ℂ) •
        (1 : QubitMatrix) := by
  let r := qubitDifferenceNN theta eta
  have hr : (algebraMap NNReal ℂ) r = ((r : ℝ) : ℂ) := rfl
  ext i j
  rw [Matrix.algebraMap_matrix_apply]
  split_ifs with h
  · subst j
    rw [hr]
    change (((1 / 4 : ℝ) * QubitOracle.blochNormSq (theta - eta) : ℝ) : ℂ) = _
    norm_num
  · simp [h]

private theorem qubitDensityMatrix_sub_star_mul_self_algebraMap
    (theta eta : Fin 3 → ℝ) :
    star (qubitDensityMatrix theta - qubitDensityMatrix eta) *
        (qubitDensityMatrix theta - qubitDensityMatrix eta) =
      algebraMap NNReal QubitMatrix (qubitDifferenceNN theta eta) := by
  rw [density_sub_eq_pauli]
  rw [star_smul, star_pauliLinear]
  rw [smul_mul_smul]
  rw [pauliLinear_mul, cross3_self, blochDot_self]
  rw [algebraMap_qubitDifferenceNN]
  simp [pauliLinear]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.one_apply]

/-- The positive square of a Bloch density-matrix difference is scalar. -/
theorem qubitDensityMatrix_sub_star_mul_self_scalar (theta eta : Fin 3 → ℝ) :
    star (qubitDensityMatrix theta - qubitDensityMatrix eta) *
        (qubitDensityMatrix theta - qubitDensityMatrix eta) =
      (((1 / 4 : ℝ) * QubitOracle.blochNormSq (theta - eta) : ℝ) : ℂ) •
        (1 : QubitMatrix) := by
  rw [qubitDensityMatrix_sub_star_mul_self_algebraMap,
    algebraMap_qubitDifferenceNN]

private theorem trace_algebraMap_nnreal_qubit (r : NNReal) :
    Matrix.trace ((algebraMap NNReal QubitMatrix) r) =
      2 * ((r : ℝ) : ℂ) := by
  have hr : (algebraMap NNReal ℂ) r = ((r : ℝ) : ℂ) := rfl
  simp only [Matrix.trace, Fin.sum_univ_two, Matrix.diag,
    Matrix.algebraMap_matrix_apply]
  rw [hr]
  simp
  ring

/-- Exact matrix trace norm of the difference of two Bloch qubit states. -/
theorem matrixTraceNorm_qubitDensityMatrix_sub (theta eta : Fin 3 → ℝ) :
    matrixTraceNorm (qubitDensityMatrix theta - qubitDensityMatrix eta) =
      Real.sqrt (QubitOracle.blochNormSq (theta - eta)) := by
  rw [matrixTraceNorm, qubitDensityMatrix_sub_star_mul_self_algebraMap,
    CFC.sqrt_algebraMap, trace_algebraMap_nnreal_qubit]
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Real.coe_sqrt]
  let x := QubitOracle.blochNormSq (theta - eta)
  have hx : 0 ≤ x := blochNormSq_nonneg_traceDistance _
  have hquarter : 0 ≤ (1 / 4 : ℝ) * x := mul_nonneg (by norm_num) hx
  have hsx : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx
  have hsq : (Real.sqrt ((1 / 4 : ℝ) * x)) ^ 2 = (1 / 4 : ℝ) * x :=
    Real.sq_sqrt hquarter
  have hsx0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsq0 : 0 ≤ Real.sqrt ((1 / 4 : ℝ) * x) := Real.sqrt_nonneg _
  change 2 * Real.sqrt ((1 / 4 : ℝ) * x) = Real.sqrt x
  nlinarith

/-- Physical trace distance in Bloch coordinates. -/
theorem quantumTraceDistance_bloch_representation
    (rho sigma : FiniteDensityMatrix (Fin 2))
    (theta eta : Fin 3 → ℝ)
    (hrho : rho.val = qubitDensityMatrix theta)
    (hsigma : sigma.val = qubitDensityMatrix eta) :
    quantumTraceDistance rho sigma =
      (1 / 2 : ℝ) * Real.sqrt (QubitOracle.blochNormSq (theta - eta)) := by
  rw [quantumTraceDistance, hrho, hsigma,
    matrixTraceNorm_qubitDensityMatrix_sub]

/-- Squared physical trace distance equals one quarter of Bloch squared error. -/
theorem quantumTraceDistance_sq_bloch_representation
    (rho sigma : FiniteDensityMatrix (Fin 2))
    (theta eta : Fin 3 → ℝ)
    (hrho : rho.val = qubitDensityMatrix theta)
    (hsigma : sigma.val = qubitDensityMatrix eta) :
    quantumTraceDistance rho sigma ^ 2 =
      (1 / 4 : ℝ) * QubitOracle.blochNormSq (theta - eta) := by
  rw [quantumTraceDistance_bloch_representation rho sigma theta eta hrho hsigma,
    mul_pow, Real.sq_sqrt (blochNormSq_nonneg_traceDistance _)]
  ring

/-- The matrix Hilbert--Schmidt square is half the Bloch squared error. -/
theorem qubitDensityMatrix_sub_hilbertSchmidtSq (theta eta : Fin 3 → ℝ) :
    (Matrix.trace
      (star (qubitDensityMatrix theta - qubitDensityMatrix eta) *
        (qubitDensityMatrix theta - qubitDensityMatrix eta))).re =
      (1 / 2 : ℝ) * QubitOracle.blochNormSq (theta - eta) := by
  rw [qubitDensityMatrix_sub_star_mul_self_algebraMap,
    trace_algebraMap_nnreal_qubit]
  have hcoe : ((qubitDifferenceNN theta eta : NNReal) : ℝ) =
      (1 / 4 : ℝ) * QubitOracle.blochNormSq (theta - eta) := rfl
  rw [hcoe]
  simp
  ring

/-- For all one-qubit states, squared trace distance is one half of squared
Hilbert--Schmidt (Frobenius) distance. -/
theorem quantumTraceDistance_sq_eq_half_hilbertSchmidtSq
    (rho sigma : FiniteDensityMatrix (Fin 2))
    (theta eta : Fin 3 → ℝ)
    (hrho : rho.val = qubitDensityMatrix theta)
    (hsigma : sigma.val = qubitDensityMatrix eta) :
    quantumTraceDistance rho sigma ^ 2 =
      (1 / 2 : ℝ) *
        (Matrix.trace
          (star (rho.val - sigma.val) * (rho.val - sigma.val))).re := by
  rw [quantumTraceDistance_sq_bloch_representation rho sigma theta eta hrho hsigma,
    hrho, hsigma, qubitDensityMatrix_sub_hilbertSchmidtSq]
  ring

end

end QubitOracle.Paper
