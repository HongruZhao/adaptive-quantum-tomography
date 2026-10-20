import QubitOracle.TwoBasis

/-!
# Explicit four-dimensional endpoint

This file instantiates the general two-basis calculation with the real
four-dimensional Hadamard matrix.  In a two-qubit interpretation, the two
basis matrices and their adjoints are general global `4 × 4` unitaries; no
tensor-product factorization is asserted.
-/

namespace QubitOracle

noncomputable section

/-- A normalized real Hadamard matrix of order four. -/
def hadamard4 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(1 / 2 : ℝ),  1 / 2,  1 / 2,  1 / 2;
      1 / 2,        1 / 2, -1 / 2, -1 / 2;
      1 / 2,       -1 / 2,  1 / 2, -1 / 2;
      1 / 2,       -1 / 2, -1 / 2,  1 / 2]

/-- Kernel-checked orthogonality of the explicit Hadamard matrix. -/
theorem hadamard4_mem_orthogonal :
    hadamard4 ∈ Matrix.orthogonalGroup (Fin 4) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hadamard4, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

/-- The first row of `hadamard4` has the required uniform entries. -/
theorem hadamard4_uniform_first_row (k : Fin 4) :
    hadamard4 0 k = 1 / Real.sqrt (4 : ℝ) := by
  fin_cases k <;> norm_num [hadamard4]

/-- Assumption-free coefficient frame for the dimension-four construction. -/
def fourDimensionalFrame : OracleFrame 3 where
  W := hadamard4
  orthogonal := hadamard4_mem_orthogonal
  uniformFirstRow := by
    intro k
    fin_cases k <;> norm_num [hadamard4]

/-- The first explicit four-dimensional basis is unitary. -/
theorem fourDimensional_chiBasis_mem_unitary :
    chiBasis fourDimensionalFrame ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
  chiBasis_mem_unitary fourDimensionalFrame

/-- The second explicit four-dimensional basis is unitary. -/
theorem fourDimensional_tauBasis_mem_unitary :
    tauBasis fourDimensionalFrame ∈ Matrix.unitaryGroup (Fin 4) ℂ :=
  tauBasis_mem_unitary fourDimensionalFrame

/-- Assumption-free Fisher endpoint in six real tangent coordinates. -/
theorem fourDimensional_equalMixtureFisher :
    equalMixtureFisher fourDimensionalFrame =
      (1 / 2 : ℝ) • (1 : Matrix (TangentIndex 3) (TangentIndex 3) ℝ) :=
  equalMixtureFisher_eq_half_identity fourDimensionalFrame

/-- For any adapted laboratory frame, the transported first basis is a global
four-dimensional unitary. -/
theorem fourDimensional_transportedChiBasis_mem_unitary
    (E : Matrix (Fin 4) (Fin 4) ℂ)
    (hE : E ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    transportedChiBasis E fourDimensionalFrame ∈
      Matrix.unitaryGroup (Fin 4) ℂ :=
  transportedChiBasis_mem_unitary E hE fourDimensionalFrame

/-- For any adapted laboratory frame, the transported second basis is a global
four-dimensional unitary. -/
theorem fourDimensional_transportedTauBasis_mem_unitary
    (E : Matrix (Fin 4) (Fin 4) ℂ)
    (hE : E ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    transportedTauBasis E fourDimensionalFrame ∈
      Matrix.unitaryGroup (Fin 4) ℂ :=
  transportedTauBasis_mem_unitary E hE fourDimensionalFrame

/-- The first explicit pre-readout rotation is unitary in every adapted
laboratory frame. -/
theorem fourDimensional_chiPreReadout_mem_unitary
    (E : Matrix (Fin 4) (Fin 4) ℂ)
    (hE : E ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    preReadout (transportedChiBasis E fourDimensionalFrame) ∈
      Matrix.unitaryGroup (Fin 4) ℂ :=
  preReadout_mem_unitary _
    (fourDimensional_transportedChiBasis_mem_unitary E hE)

/-- The second explicit pre-readout rotation is unitary in every adapted
laboratory frame. -/
theorem fourDimensional_tauPreReadout_mem_unitary
    (E : Matrix (Fin 4) (Fin 4) ℂ)
    (hE : E ∈ Matrix.unitaryGroup (Fin 4) ℂ) :
    preReadout (transportedTauBasis E fourDimensionalFrame) ∈
      Matrix.unitaryGroup (Fin 4) ℂ :=
  preReadout_mem_unitary _
    (fourDimensional_transportedTauBasis_mem_unitary E hE)

end

end QubitOracle
