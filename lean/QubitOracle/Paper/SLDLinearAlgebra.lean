import Mathlib

/-! SLD solution and uniqueness statements in Section 2.4.
The eigenbasis formula is proved entrywise. For a pure projector the
entire solution freedom is its kernel block, not merely one choice.
-/
namespace QubitOracle.Paper.SLDLinearAlgebra
open scoped BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def diagonalSLD (eig : ι → ℝ) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => 2 * A i j / (eig i + eig j : ℂ)

theorem diagonal_denominator_ne_zero (eig : ι → ℝ) (heig : ∀ i, 0 < eig i) (i j : ι) :
    (eig i + eig j : ℂ) ≠ 0 := by
  rw [← Complex.ofReal_add]
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (add_pos (heig i) (heig j)))

theorem diagonal_sld_equation (eig : ι → ℝ) (heig : ∀ i, 0 < eig i) (A : Matrix ι ι ℂ) :
    Matrix.diagonal (fun i => (eig i : ℂ)) * diagonalSLD eig A +
      diagonalSLD eig A * Matrix.diagonal (fun i => (eig i : ℂ)) = 2 • A := by
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, diagonalSLD,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have hn := diagonal_denominator_ne_zero eig heig i j
  field_simp
  ring

theorem diagonal_sld_unique (eig : ι → ℝ) (heig : ∀ i, 0 < eig i)
    (A L : Matrix ι ι ℂ)
    (hL : Matrix.diagonal (fun i => (eig i : ℂ)) * L +
      L * Matrix.diagonal (fun i => (eig i : ℂ)) = 2 • A) : L = diagonalSLD eig A := by
  ext i j
  have he := congrArg (fun M : Matrix ι ι ℂ => M i j) hL
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul] at he
  unfold diagonalSLD
  apply (eq_div_iff (diagonal_denominator_ne_zero eig heig i j)).mpr
  linear_combination he

theorem diagonal_sld_hermitian (eig : ι → ℝ) (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    (diagonalSLD eig A).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, diagonalSLD, star_div₀, star_mul,
    star_ofNat, star_add, Complex.star_def, Complex.conj_ofReal]
  have he := congrArg (fun M : Matrix ι ι ℂ => M i j) hA
  simp only [Matrix.conjTranspose_apply, Complex.star_def] at he
  rw [he]
  rw [add_comm (eig j : ℂ) (eig i : ℂ)]
  rw [mul_comm (A i j) 2]

theorem projector_kernel_iff (P K : Matrix ι ι ℂ) (hP : P * P = P) :
    P * K + K * P = 0 ↔ P * K = 0 ∧ K * P = 0 := by
  constructor
  · intro h
    have hs : P * K * P + P * K * P = 0 := by
      have hh := congrArg (fun M : Matrix ι ι ℂ => P * M * P) h
      simpa only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_zero,
        Matrix.zero_mul, Matrix.mul_assoc, ← Matrix.mul_assoc P P, hP] using hh
    have hz : P * K * P = 0 := by
      have hh : (2 : ℂ) • (P * K * P) = 0 := by simpa [two_smul] using hs
      exact (smul_eq_zero.mp hh).resolve_left (by norm_num)
    have hl := congrArg (fun M : Matrix ι ι ℂ => P * M) h
    have hr := congrArg (fun M : Matrix ι ι ℂ => M * P) h
    constructor
    · simpa only [Matrix.mul_add, ← Matrix.mul_assoc, hP, hz,
        add_zero, Matrix.mul_zero] using hl
    · simpa only [Matrix.add_mul, Matrix.mul_assoc, ← Matrix.mul_assoc P K,
        hP, hz, zero_add, Matrix.zero_mul] using hr
  · rintro ⟨hl, hr⟩
    simp [hl, hr]

theorem pure_sld_solution_iff (P A L : Matrix ι ι ℂ)
    (hP : P * P = P) (hA : P * A + A * P = A) :
    P * L + L * P = 2 • A ↔
      P * (L - 2 • A) = 0 ∧ (L - 2 • A) * P = 0 := by
  rw [← projector_kernel_iff P (L - 2 • A) hP]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  have he : P * L - 2 • (P * A) + (L * P - 2 • (A * P)) =
      (P * L + L * P) - 2 • A := by
    calc
      _ = (P * L + L * P) - (2 • (P * A) + 2 • (A * P)) := by abel
      _ = (P * L + L * P) - 2 • (P * A + A * P) := by rw [smul_add]
      _ = _ := by rw [hA]
  rw [he, sub_eq_zero]

end
end QubitOracle.Paper.SLDLinearAlgebra
