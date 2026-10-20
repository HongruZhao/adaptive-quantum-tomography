import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import QubitOracle.Paper.MixedOracleGeometry
/-!
# Matrix inequalities for the mixed-state oracle

The supplement reduces `trace (G M^{-1})` by inverse square-root congruence and
then applies Hilbert--Schmidt Cauchy--Schwarz.  Both steps are proved here for
real `3 x 3` matrices from explicit algebraic hypotheses.  No spectral or
optimization assertion is postulated.
-/

namespace QubitOracle.Paper

open scoped BigOperators

noncomputable section

/-- Frobenius/Hilbert--Schmidt inner product on real Bloch matrices. -/
def frobeniusInner (X Y : OracleMatrix) : ℝ :=
  ∑ i, ∑ j, X i j * Y i j

/-- Squared Frobenius norm. -/
def frobeniusSq (X : OracleMatrix) : ℝ :=
  frobeniusInner X X

theorem frobeniusSq_nonneg (X : OracleMatrix) :
    0 ≤ frobeniusSq X := by
  unfold frobeniusSq frobeniusInner
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact mul_self_nonneg (X i j)

theorem frobeniusInner_sq_le (X Y : OracleMatrix) :
    frobeniusInner X Y ^ 2 ≤ frobeniusSq X * frobeniusSq Y := by
  let f : (Fin 3 × Fin 3) -> ℝ := fun p => X p.1 p.2
  let g : (Fin 3 × Fin 3) -> ℝ := fun p => Y p.1 p.2
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ) f g
  simpa [frobeniusInner, frobeniusSq, f, g,
    Fintype.sum_prod_type, pow_two] using h

theorem frobenius_cauchy_schwarz (X Y : OracleMatrix) :
    frobeniusInner X Y ≤
      Real.sqrt (frobeniusSq X) * Real.sqrt (frobeniusSq Y) := by
  have hX := frobeniusSq_nonneg X
  have hY := frobeniusSq_nonneg Y
  have hcs := frobeniusInner_sq_le X Y
  have hp :
      0 ≤ Real.sqrt (frobeniusSq X) * Real.sqrt (frobeniusSq Y) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hp2 :
      (Real.sqrt (frobeniusSq X) * Real.sqrt (frobeniusSq Y)) ^ 2 =
        frobeniusSq X * frobeniusSq Y := by
    rw [mul_pow, Real.sq_sqrt hX, Real.sq_sqrt hY]
  nlinarith

theorem trace_transpose_mul_eq_frobeniusInner (X Y : OracleMatrix) :
    Matrix.trace (X.transpose * Y) = frobeniusInner X Y := by
  simp [Matrix.trace, Matrix.mul_apply, frobeniusInner,
    Fin.sum_univ_succ]
  ring

/-- Hilbert--Schmidt Cauchy--Schwarz in the exact trace form used in the
supplement. -/
theorem matrix_trace_cauchy_schwarz (X Y : OracleMatrix) :
    Matrix.trace (X.transpose * Y) ≤
      Real.sqrt (Matrix.trace (X.transpose * X)) *
        Real.sqrt (Matrix.trace (Y.transpose * Y)) := by
  rw [trace_transpose_mul_eq_frobeniusInner,
    trace_transpose_mul_eq_frobeniusInner,
    trace_transpose_mul_eq_frobeniusInner]
  exact frobenius_cauchy_schwarz X Y

/-- Inverse-congruence reduction
`trace (G (S A S)^{-1}) = trace ((T G T) A^{-1})` for inverse roots `S,T`. -/
theorem mixedOracle_trace_reduction
    (G A Ainv S T : OracleMatrix)
    (hST : S * T = 1) (hTS : T * S = 1)
    (hAAinv : A * Ainv = 1) :
    Matrix.trace (G * (S * A * S)⁻¹) =
      Matrix.trace ((T * G * T) * Ainv) := by
  have hMinv : (S * A * S)⁻¹ = T * Ainv * T := by
    apply Matrix.inv_eq_right_inv
    calc
      (S * A * S) * (T * Ainv * T) =
          S * A * (S * T) * Ainv * T := by noncomm_ring
      _ = S * (A * Ainv) * T := by rw [hST]; simp [Matrix.mul_assoc]
      _ = 1 := by rw [hAAinv]; simpa [Matrix.mul_assoc] using hST
  rw [hMinv]
  simpa [Matrix.mul_assoc] using
    (Matrix.trace_mul_cycle (G * T) Ainv T)

/-- The specialized matrix Cauchy--Schwarz inequality from Supplementary
Eq. (SI-matrix-CS).  `H,K,R` represent `A^{1/2}`, `A^{-1/2}`, and
`C^{1/2}` respectively. -/
theorem mixedOracle_matrix_cauchy_schwarz
    (A Ainv C H K R : OracleMatrix)
    (hHK : H * K = 1)
    (hHsym : H.transpose = H)
    (hKsym : K.transpose = K)
    (hRsym : R.transpose = R)
    (hHsq : H * H = A)
    (hKsq : K * K = Ainv)
    (hRsq : R * R = C) :
    Matrix.trace R ≤
      Real.sqrt (Matrix.trace A) *
        Real.sqrt (Matrix.trace (C * Ainv)) := by
  have hcs := matrix_trace_cauchy_schwarz H (K * R)
  have hleft : Matrix.trace (H.transpose * (K * R)) = Matrix.trace R := by
    rw [hHsym, ← Matrix.mul_assoc, hHK, one_mul]
  have hfirst : Matrix.trace (H.transpose * H) = Matrix.trace A := by
    rw [hHsym, hHsq]
  have hsecond :
      Matrix.trace ((K * R).transpose * (K * R)) =
        Matrix.trace (C * Ainv) := by
    calc
      Matrix.trace ((K * R).transpose * (K * R)) =
          Matrix.trace (R * K * K * R) := by
            rw [Matrix.transpose_mul, hKsym, hRsym]
            congr 1
            noncomm_ring
      _ = Matrix.trace (R * Ainv * R) := by
            rw [show R * K * K * R = R * (K * K) * R by noncomm_ring,
              hKsq]
      _ = Matrix.trace (R * R * Ainv) :=
            Matrix.trace_mul_cycle R Ainv R
      _ = Matrix.trace (C * Ainv) := by rw [hRsq]
  rw [hleft, hfirst, hsecond] at hcs
  exact hcs

end

end QubitOracle.Paper
