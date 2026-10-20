import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.OneQubitMatrixTraceDistance
import QubitOracle.Paper.QuantumDistances
import QubitOracle.Paper.QubitFoundations
/-!
# Bloch representation of every physical one-qubit density matrix

This module derives Bloch coordinates from an arbitrary `2 x 2` density
matrix and proves exact reconstruction.  It removes the supplied-coordinate
hypothesis from the physical trace-distance and trace--Frobenius identities.
-/

namespace QubitOracle.Paper

open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

/-- Bloch coordinates extracted from an arbitrary physical two-by-two density matrix. -/
def finiteDensityMatrixBlochCoordinates
    (rho : FiniteDensityMatrix (Fin 2)) : Fin 3 → ℝ :=
  ![2 * (rho.val 0 1).re,
    -2 * (rho.val 0 1).im,
    2 * (rho.val 0 0).re - 1]

/-- Every physical two-by-two density matrix is exactly its Bloch
parameterization. -/
theorem finiteDensityMatrix_eq_qubitDensityMatrix
    (rho : FiniteDensityMatrix (Fin 2)) :
    rho.val = qubitDensityMatrix (finiteDensityMatrixBlochCoordinates rho) := by
  have hHerm := rho.pos.isHermitian
  have h00 := hHerm.apply (0 : Fin 2) (0 : Fin 2)
  have h11 := hHerm.apply (1 : Fin 2) (1 : Fin 2)
  have h10 := hHerm.apply (1 : Fin 2) (0 : Fin 2)
  have h00im : (rho.val 0 0).im = 0 := by
    have him := congrArg Complex.im h00
    simp at him
    linarith
  have h11im : (rho.val 1 1).im = 0 := by
    have him := congrArg Complex.im h11
    simp at him
    linarith
  have h10re : (rho.val 1 0).re = (rho.val 0 1).re := by
    have hre := congrArg Complex.re h10
    simpa using hre.symm
  have h10im : (rho.val 1 0).im = -(rho.val 0 1).im := by
    have him := congrArg Complex.im h10
    simpa using him.symm
  have htrace := rho.trace_one
  simp only [Matrix.trace, Fin.sum_univ_two, Matrix.diag] at htrace
  have htraceRe : (rho.val 0 0).re + (rho.val 1 1).re = 1 := by
    have hre := congrArg Complex.re htrace
    simpa using hre
  ext i j
  fin_cases i <;> fin_cases j
  · apply Complex.ext
    · simp [qubitDensityMatrix, pauliLinear,
        finiteDensityMatrixBlochCoordinates]
    · simp [qubitDensityMatrix, pauliLinear,
        finiteDensityMatrixBlochCoordinates, h00im]
  · apply Complex.ext
    · simp [qubitDensityMatrix, pauliLinear,
        finiteDensityMatrixBlochCoordinates]
    · simp [qubitDensityMatrix, pauliLinear,
        finiteDensityMatrixBlochCoordinates]
  · apply Complex.ext
    · simp [qubitDensityMatrix, pauliLinear,
        finiteDensityMatrixBlochCoordinates, h10re]
    · simp [qubitDensityMatrix, pauliLinear,
        finiteDensityMatrixBlochCoordinates, h10im]
  · apply Complex.ext
    · simp [qubitDensityMatrix, pauliLinear,
        finiteDensityMatrixBlochCoordinates]
      linarith
    · simp [qubitDensityMatrix, pauliLinear,
        finiteDensityMatrixBlochCoordinates, h11im]

/-- Exact physical trace distance formula for every pair of one-qubit density
matrices, with no supplied-coordinate hypothesis. -/
theorem quantumTraceDistance_all_qubits
    (rho sigma : FiniteDensityMatrix (Fin 2)) :
    quantumTraceDistance rho sigma =
      (1 / 2 : ℝ) * Real.sqrt
        (QubitOracle.blochNormSq
          (finiteDensityMatrixBlochCoordinates rho -
            finiteDensityMatrixBlochCoordinates sigma)) := by
  exact quantumTraceDistance_bloch_representation rho sigma _ _
    (finiteDensityMatrix_eq_qubitDensityMatrix rho)
    (finiteDensityMatrix_eq_qubitDensityMatrix sigma)

/-- Squared trace distance is one quarter of squared Bloch error for every
pair of one-qubit density matrices. -/
theorem quantumTraceDistance_sq_all_qubits
    (rho sigma : FiniteDensityMatrix (Fin 2)) :
    quantumTraceDistance rho sigma ^ 2 =
      (1 / 4 : ℝ) * QubitOracle.blochNormSq
        (finiteDensityMatrixBlochCoordinates rho -
          finiteDensityMatrixBlochCoordinates sigma) := by
  exact quantumTraceDistance_sq_bloch_representation rho sigma _ _
    (finiteDensityMatrix_eq_qubitDensityMatrix rho)
    (finiteDensityMatrix_eq_qubitDensityMatrix sigma)

/-- For every pair of one-qubit states, including mixed states, squared trace
distance equals one half of squared Hilbert--Schmidt distance. -/
theorem quantumTraceDistance_sq_eq_half_hilbertSchmidtSq_all_qubits
    (rho sigma : FiniteDensityMatrix (Fin 2)) :
    quantumTraceDistance rho sigma ^ 2 =
      (1 / 2 : ℝ) *
        (Matrix.trace
          (star (rho.val - sigma.val) * (rho.val - sigma.val))).re := by
  exact quantumTraceDistance_sq_eq_half_hilbertSchmidtSq rho sigma _ _
    (finiteDensityMatrix_eq_qubitDensityMatrix rho)
    (finiteDensityMatrix_eq_qubitDensityMatrix sigma)

end

end QubitOracle.Paper
