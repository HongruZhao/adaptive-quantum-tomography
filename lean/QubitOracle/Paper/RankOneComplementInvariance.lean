import QubitOracle.TwoBasis

/-!
# Complement-frame invariance of the rank-one two-basis oracle
-/

namespace QubitOracle
namespace Paper

open scoped BigOperators ComplexConjugate

noncomputable section

/-- Tangent rows of the real oracle coefficient matrix, viewed over `C`. -/
def oracleTangentRows {n : Nat} (F : OracleFrame n) :
    Matrix (Fin n) (Fin (n + 1)) Complex :=
  fun a k => (F.W a.succ k : Complex)

/-- An arbitrary unitary rotation of the controller's complex complement. -/
def rotatedTangentRows {n : Nat} (F : OracleFrame n)
    (Q : Matrix (Fin n) (Fin n) Complex) :
    Matrix (Fin n) (Fin (n + 1)) Complex :=
  Q * oracleTangentRows F

/-- The unrotated tangent rows have orthonormal complex row Gram matrix. -/
theorem oracleTangentRows_mul_conjTranspose {n : Nat}
    (F : OracleFrame n) :
    oracleTangentRows F * (oracleTangentRows F).conjTranspose = 1 := by
  ext a b
  change (∑ k, (F.W a.succ k : Complex) *
    star (F.W b.succ k : Complex)) = _
  have h := F.row_gram a.succ b.succ
  have hc := congrArg Complex.ofReal h
  by_cases hab : a = b <;>
    simpa [Matrix.one_apply, hab] using hc

/-- A unitary complement rotation preserves the tangent row Gram matrix. -/
theorem rotatedTangentRows_mul_conjTranspose {n : Nat}
    (F : OracleFrame n) (Q : Matrix (Fin n) (Fin n) Complex)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) Complex) :
    rotatedTangentRows F Q * (rotatedTangentRows F Q).conjTranspose = 1 := by
  rw [rotatedTangentRows, Matrix.conjTranspose_mul,
    ← Matrix.mul_assoc, Matrix.mul_assoc Q,
    oracleTangentRows_mul_conjTranspose,
    Matrix.mul_one]
  exact (Matrix.mem_unitaryGroup_iff.mp hQ)

/-- Row-Gram identity in scalar sum form. -/
theorem rotatedTangentRows_rowGram {n : Nat}
    (F : OracleFrame n) (Q : Matrix (Fin n) (Fin n) Complex)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) Complex) (a b : Fin n) :
    (∑ k, rotatedTangentRows F Q a k *
      star (rotatedTangentRows F Q b k)) =
      if a = b then 1 else 0 := by
  have h := congrFun (congrFun
    (rotatedTangentRows_mul_conjTranspose F Q hQ) a) b
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

/-- Real part of a complex matrix row Gram value. -/
def matrixRowRealGram {A B : Type*} [Fintype B]
    (Z : Matrix A B Complex) (a b : A) : Real :=
  ∑ k, ((Z a k).re * (Z b k).re + (Z a k).im * (Z b k).im)

/-- Signed cross-quadrature part of a complex matrix row Gram value. -/
def matrixRowCrossGram {A B : Type*} [Fintype B]
    (Z : Matrix A B Complex) (a b : A) : Real :=
  ∑ k, ((Z a k).re * (Z b k).im - (Z a k).im * (Z b k).re)

/-- Real part of the complex row-Gram identity. -/
theorem rotatedTangentRows_realGram {n : Nat}
    (F : OracleFrame n) (Q : Matrix (Fin n) (Fin n) Complex)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) Complex) (a b : Fin n) :
    matrixRowRealGram (rotatedTangentRows F Q) a b =
      if a = b then 1 else 0 := by
  have h := congrArg Complex.re
    (rotatedTangentRows_rowGram F Q hQ a b)
  by_cases hab : a = b <;>
    simpa [matrixRowRealGram, map_sum, Complex.mul_re, hab] using h

/-- Imaginary part of the complex row-Gram identity. -/
theorem rotatedTangentRows_crossGram {n : Nat}
    (F : OracleFrame n) (Q : Matrix (Fin n) (Fin n) Complex)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) Complex) (a b : Fin n) :
    matrixRowCrossGram (rotatedTangentRows F Q) a b = 0 := by
  have h := congrArg Complex.im
    (rotatedTangentRows_rowGram F Q hQ a b)
  simp [Complex.mul_im] at h
  have him :
      (∑ k, (-((rotatedTangentRows F Q a k).re *
          (rotatedTangentRows F Q b k).im) +
        (rotatedTangentRows F Q a k).im *
          (rotatedTangentRows F Q b k).re)) = 0 := by
    by_cases hab : a = b <;> simpa [hab] using h
  unfold matrixRowCrossGram
  calc
    (∑ k, ((rotatedTangentRows F Q a k).re *
        (rotatedTangentRows F Q b k).im -
      (rotatedTangentRows F Q a k).im *
        (rotatedTangentRows F Q b k).re)) =
        -(∑ k, (-((rotatedTangentRows F Q a k).re *
            (rotatedTangentRows F Q b k).im) +
          (rotatedTangentRows F Q a k).im *
            (rotatedTangentRows F Q b k).re)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = 0 := by rw [him]; norm_num

/-- Probability gradient of the first basis after an arbitrary complex
rotation of the complement, expressed in the fixed true chart. -/
def rotatedChiGradient {n : Nat} (F : OracleFrame n)
    (Q : Matrix (Fin n) (Fin n) Complex) (k : Fin (n + 1)) :
    TangentIndex n -> Real
  | Sum.inl a => F.W 0 k * (rotatedTangentRows F Q a k).re
  | Sum.inr a => F.W 0 k * (rotatedTangentRows F Q a k).im

/-- The phase-shifted second basis exchanges the two real quadratures. -/
def rotatedTauGradient {n : Nat} (F : OracleFrame n)
    (Q : Matrix (Fin n) (Fin n) Complex) (k : Fin (n + 1)) :
    TangentIndex n -> Real
  | Sum.inl a => F.W 0 k * (-(rotatedTangentRows F Q a k).im)
  | Sum.inr a => F.W 0 k * (rotatedTangentRows F Q a k).re

/-- Fisher information of the rotated first basis in the fixed true chart. -/
def rotatedChiFisher {n : Nat} (F : OracleFrame n)
    (Q : Matrix (Fin n) (Fin n) Complex) :
    Matrix (TangentIndex n) (TangentIndex n) Real :=
  classicalFisher (baseProbability F) (rotatedChiGradient F Q)

/-- Fisher information of the rotated second basis in the fixed true chart. -/
def rotatedTauFisher {n : Nat} (F : OracleFrame n)
    (Q : Matrix (Fin n) (Fin n) Complex) :
    Matrix (TangentIndex n) (TangentIndex n) Real :=
  classicalFisher (baseProbability F) (rotatedTauGradient F Q)

/-- Equal mixture after an arbitrary unitary rotation of the complex
complement. -/
def rotatedEqualMixtureFisher {n : Nat} (F : OracleFrame n)
    (Q : Matrix (Fin n) (Fin n) Complex) :
    Matrix (TangentIndex n) (TangentIndex n) Real :=
  (1 / 2 : Real) • rotatedChiFisher F Q +
    (1 / 2 : Real) • rotatedTauFisher F Q

/-- The equal two-basis information is exactly isotropic in the fixed true
chart for every unitary complement rotation. -/
theorem rotatedEqualMixtureFisher_eq_half_identity {n : Nat}
    (F : OracleFrame n) (Q : Matrix (Fin n) (Fin n) Complex)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) Complex) :
    rotatedEqualMixtureFisher F Q =
      (1 / 2 : Real) •
        (1 : Matrix (TangentIndex n) (TangentIndex n) Real) := by
  ext x y
  rcases x with a | a <;> rcases y with b | b
  · change (1 / 2 : Real) *
        (∑ k, ((F.W 0 k * (rotatedTangentRows F Q a k).re) *
          (F.W 0 k * (rotatedTangentRows F Q b k).re) /
          (F.W 0 k) ^ 2)) +
      (1 / 2 : Real) *
        (∑ k, ((F.W 0 k * (-(rotatedTangentRows F Q a k).im)) *
          (F.W 0 k * (-(rotatedTangentRows F Q b k).im)) /
          (F.W 0 k) ^ 2)) = _
    simp_rw [cancel_probability _ _ _ (F.firstRow_ne_zero _)]
    have hsum :
        (∑ k, (rotatedTangentRows F Q a k).re *
          (rotatedTangentRows F Q b k).re) +
        (∑ k, (-(rotatedTangentRows F Q a k).im) *
          (-(rotatedTangentRows F Q b k).im)) =
          if a = b then 1 else 0 := by
      simpa [matrixRowRealGram, Finset.sum_add_distrib] using
        rotatedTangentRows_realGram F Q hQ a b
    rw [← mul_add, hsum]
    by_cases hab : a = b <;> simp [hab]
  · change (1 / 2 : Real) *
        (∑ k, ((F.W 0 k * (rotatedTangentRows F Q a k).re) *
          (F.W 0 k * (rotatedTangentRows F Q b k).im) /
          (F.W 0 k) ^ 2)) +
      (1 / 2 : Real) *
        (∑ k, ((F.W 0 k * (-(rotatedTangentRows F Q a k).im)) *
          (F.W 0 k * (rotatedTangentRows F Q b k).re) /
          (F.W 0 k) ^ 2)) = _
    simp_rw [cancel_probability _ _ _ (F.firstRow_ne_zero _)]
    have hcross := rotatedTangentRows_crossGram F Q hQ a b
    unfold matrixRowCrossGram at hcross
    rw [Finset.sum_sub_distrib] at hcross
    have hsum :
        (∑ k, (rotatedTangentRows F Q a k).re *
          (rotatedTangentRows F Q b k).im) +
        (∑ k, (-(rotatedTangentRows F Q a k).im) *
          (rotatedTangentRows F Q b k).re) = 0 := by
      simp_rw [neg_mul]
      rw [Finset.sum_neg_distrib]
      linarith
    rw [← mul_add, hsum]
    simp
  · change (1 / 2 : Real) *
        (∑ k, ((F.W 0 k * (rotatedTangentRows F Q a k).im) *
          (F.W 0 k * (rotatedTangentRows F Q b k).re) /
          (F.W 0 k) ^ 2)) +
      (1 / 2 : Real) *
        (∑ k, ((F.W 0 k * (rotatedTangentRows F Q a k).re) *
          (F.W 0 k * (-(rotatedTangentRows F Q b k).im)) /
          (F.W 0 k) ^ 2)) = _
    simp_rw [cancel_probability _ _ _ (F.firstRow_ne_zero _)]
    have hcross := rotatedTangentRows_crossGram F Q hQ a b
    unfold matrixRowCrossGram at hcross
    rw [Finset.sum_sub_distrib] at hcross
    have hsum :
        (∑ k, (rotatedTangentRows F Q a k).im *
          (rotatedTangentRows F Q b k).re) +
        (∑ k, (rotatedTangentRows F Q a k).re *
          (-(rotatedTangentRows F Q b k).im)) = 0 := by
      simp_rw [mul_neg]
      rw [Finset.sum_neg_distrib]
      linarith
    rw [← mul_add, hsum]
    simp
  · change (1 / 2 : Real) *
        (∑ k, ((F.W 0 k * (rotatedTangentRows F Q a k).im) *
          (F.W 0 k * (rotatedTangentRows F Q b k).im) /
          (F.W 0 k) ^ 2)) +
      (1 / 2 : Real) *
        (∑ k, ((F.W 0 k * (rotatedTangentRows F Q a k).re) *
          (F.W 0 k * (rotatedTangentRows F Q b k).re) /
          (F.W 0 k) ^ 2)) = _
    simp_rw [cancel_probability _ _ _ (F.firstRow_ne_zero _)]
    have hreal := rotatedTangentRows_realGram F Q hQ a b
    unfold matrixRowRealGram at hreal
    rw [Finset.sum_add_distrib] at hreal
    have hsum : (∑ k, (rotatedTangentRows F Q a k).im *
          (rotatedTangentRows F Q b k).im) +
        ∑ k, (rotatedTangentRows F Q a k).re *
          (rotatedTangentRows F Q b k).re =
        (if a = b then 1 else 0) := by
      rw [add_comm]
      exact hreal
    rw [← mul_add, hsum]
    by_cases hab : a = b <;> simp [hab]

end

end Paper
end QubitOracle
