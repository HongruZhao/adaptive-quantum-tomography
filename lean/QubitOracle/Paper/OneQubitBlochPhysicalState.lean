import QubitOracle.Paper.QuantumDistances
import QubitOracle.Paper.QubitFoundations

/-!
# Physical Bloch-ball states

This module proves directly that the Bloch formula defines a positive,
trace-one density matrix whenever the Bloch vector lies in the closed unit
ball.  The proof uses only the Pauli product identity and positivity of
`A^* A`; it introduces no statistical or literature assumption.
-/

namespace QubitOracle.Paper

open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

private theorem blochNormSq_nonneg_physical (theta : Fin 3 -> Real) :
    0 <= QubitOracle.blochNormSq theta := by
  simp [QubitOracle.blochNormSq, Fin.sum_univ_succ]
  positivity

private theorem blochNormSq_eq_zero_iff_physical (theta : Fin 3 -> Real) :
    QubitOracle.blochNormSq theta = 0 <-> theta = 0 := by
  constructor
  · intro h
    funext i
    fin_cases i <;>
      simp [QubitOracle.blochNormSq, Fin.sum_univ_succ] at h ⊢ <;>
      nlinarith [sq_nonneg (theta 0), sq_nonneg (theta 1), sq_nonneg (theta 2)]
  · rintro rfl
    simp [QubitOracle.blochNormSq]

private theorem star_pauliLinear_physical (theta : Fin 3 -> Real) :
    star (pauliLinear theta) = pauliLinear theta := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliLinear, Matrix.star_apply] <;> ring

private theorem cross3_self_physical (theta : Fin 3 -> Real) :
    cross3 theta theta = 0 := by
  funext i
  fin_cases i <;> simp [cross3] <;> ring

private theorem blochDot_self_physical (theta : Fin 3 -> Real) :
    QubitOracle.blochDot theta theta = QubitOracle.blochNormSq theta := by
  simp [QubitOracle.blochDot, QubitOracle.blochNormSq, pow_two]

private theorem pauliLinear_mul_self_physical (theta : Fin 3 -> Real) :
    pauliLinear theta * pauliLinear theta =
      QubitOracle.blochNormSq theta • (1 : QubitMatrix) := by
  rw [pauliLinear_mul, cross3_self_physical, blochDot_self_physical]
  simp only [pauliLinear, smul_zero, add_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem qubitDensityMatrix_eq_real_smul (theta : Fin 3 -> Real) :
    qubitDensityMatrix theta =
      (1 / 2 : Real) • ((1 : QubitMatrix) + pauliLinear theta) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qubitDensityMatrix, pauliLinear, Matrix.one_apply] <;> ring

private theorem qubitDensityMatrix_zero :
    qubitDensityMatrix (0 : Fin 3 -> Real) =
      (1 / 2 : Real) • (1 : QubitMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qubitDensityMatrix, pauliLinear, Matrix.one_apply] <;> norm_num

/-- Every vector in the closed Bloch unit ball gives a positive-semidefinite
matrix under the Pauli density-matrix formula. -/
theorem qubitDensityMatrix_posSemidef_of_blochNormSq_le_one
    (theta : Fin 3 -> Real)
    (hball : QubitOracle.blochNormSq theta <= 1) :
    (qubitDensityMatrix theta).PosSemidef := by
  let r : Real := Real.sqrt (QubitOracle.blochNormSq theta)
  have hr0 : 0 <= r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = QubitOracle.blochNormSq theta :=
    Real.sq_sqrt (blochNormSq_nonneg_physical theta)
  have hr1 : r <= 1 := by nlinarith
  by_cases hr : r = 0
  · have hnorm : QubitOracle.blochNormSq theta = 0 := by nlinarith
    have htheta : theta = 0 :=
      (blochNormSq_eq_zero_iff_physical theta).1 hnorm
    apply Matrix.nonneg_iff_posSemidef.mp
    rw [htheta, qubitDensityMatrix_zero]
    exact smul_nonneg (by norm_num) (show (0 : QubitMatrix) <= 1 from zero_le_one)
  · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
    let U : QubitMatrix := (1 / r : Real) • pauliLinear theta
    have hUstar : star U = U := by
      simp [U, star_pauliLinear_physical]
    have hU2 : U * U = 1 := by
      dsimp [U]
      rw [smul_mul_smul, pauliLinear_mul_self_physical, smul_smul]
      have : (1 / r) * (1 / r) * QubitOracle.blochNormSq theta = 1 := by
        rw [← hr2]
        field_simp
      rw [this]
      simp
    have hplusSquare :
        star ((1 : QubitMatrix) + U) * ((1 : QubitMatrix) + U) =
          (2 : Real) • ((1 : QubitMatrix) + U) := by
      rw [star_add, star_one, hUstar]
      calc
        (1 + U) * (1 + U) = (1 + U) + (1 + U) := by
          noncomm_ring [hU2]
        _ = (2 : Real) • ((1 : QubitMatrix) + U) := by
          ext i j
          simp
          ring
    have hplusNonneg : (0 : QubitMatrix) <= 1 + U := by
      have hsquare :
          (0 : QubitMatrix) <=
            star ((1 : QubitMatrix) + U) * ((1 : QubitMatrix) + U) :=
        star_mul_self_nonneg _
      have hhalf := smul_nonneg (show (0 : Real) <= 1 / 2 by norm_num) hsquare
      rw [hplusSquare, smul_smul] at hhalf
      norm_num at hhalf
      exact hhalf
    have hdecomp :
        (1 : QubitMatrix) + pauliLinear theta =
          (1 - r : Real) • (1 : QubitMatrix) +
            r • ((1 : QubitMatrix) + U) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [U, Matrix.one_apply] <;>
        field_simp <;> ring
    apply Matrix.nonneg_iff_posSemidef.mp
    rw [qubitDensityMatrix_eq_real_smul, hdecomp]
    exact smul_nonneg (by norm_num)
      (add_nonneg
        (smul_nonneg (sub_nonneg.mpr hr1)
          (show (0 : QubitMatrix) <= 1 from zero_le_one))
        (smul_nonneg hr0 hplusNonneg))

/-- Canonical physical qubit state associated with a Bloch vector in the
closed unit ball. -/
def blochFiniteDensityMatrix
    (theta : Fin 3 -> Real)
    (hball : QubitOracle.blochNormSq theta <= 1) :
    FiniteDensityMatrix (Fin 2) where
  val := qubitDensityMatrix theta
  pos := qubitDensityMatrix_posSemidef_of_blochNormSq_le_one theta hball
  trace_one := qubitDensityMatrix_trace theta

@[simp] theorem blochFiniteDensityMatrix_val
    (theta : Fin 3 -> Real)
    (hball : QubitOracle.blochNormSq theta <= 1) :
    (blochFiniteDensityMatrix theta hball).val = qubitDensityMatrix theta := rfl

end

end QubitOracle.Paper
