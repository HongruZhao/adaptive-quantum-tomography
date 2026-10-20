import Mathlib

/-! The computational basis and dimension of a q-qubit system.
The basis is indexed by all q-tuples of the two one-qubit basis labels.
-/
namespace QubitOracle.Paper.QubitTensorDimension
noncomputable section
abbrev ComputationalLabel (q : ℕ) := Fin q → Fin 2
abbrev QubitHilbert (q : ℕ) := ComputationalLabel q → ℂ
theorem computational_basis_count (q : ℕ) :
    Fintype.card (ComputationalLabel q) = 2^q := by
  simp [ComputationalLabel]
theorem qubit_hilbert_dimension (q : ℕ) :
    Module.finrank ℂ (QubitHilbert q) = 2^q := by
  simp [QubitHilbert,computational_basis_count]

/- The following count dense arrays and the three nested update indices
of a cubic arithmetic budget. They do not assert a runtime theorem for
floating-point software or a quantum circuit. -/
theorem dense_matrix_entries (m : ℕ) : Fintype.card (Fin m × Fin m) = m^2 := by
  simp [pow_two]
theorem dense_triple_indices (m : ℕ) : Fintype.card (Fin m × Fin m × Fin m) = m^3 := by
  simp
  ring
theorem ambient_storage_count (D : ℕ) :
    Fintype.card (Fin (D^2) × Fin (D^2)) = D^4 := by
  rw [dense_matrix_entries]
  ring
theorem ambient_cubic_budget (D : ℕ) :
    Fintype.card (Fin (D^2) × Fin (D^2) × Fin (D^2)) = D^6 := by
  rw [dense_triple_indices]
  ring
theorem tangent_storage_bound (D : ℕ) :
    Fintype.card (Fin (2*(D-1)) × Fin (2*(D-1))) ≤ 4*D^2 := by
  rw [dense_matrix_entries]
  have h : 2*(D-1) ≤ 2*D := Nat.mul_le_mul_left 2 (Nat.sub_le _ _)
  calc (2*(D-1))^2 ≤ (2*D)^2 := Nat.pow_le_pow_left h 2
       _ = 4*D^2 := by ring
theorem tangent_cubic_budget_bound (D : ℕ) :
    Fintype.card (Fin (2*(D-1)) × Fin (2*(D-1)) × Fin (2*(D-1))) ≤ 8*D^3 := by
  rw [dense_triple_indices]
  have h : 2*(D-1) ≤ 2*D := Nat.mul_le_mul_left 2 (Nat.sub_le _ _)
  calc (2*(D-1))^3 ≤ (2*D)^3 := Nat.pow_le_pow_left h 3
       _ = 8*D^3 := by ring
end
end QubitOracle.Paper.QubitTensorDimension
