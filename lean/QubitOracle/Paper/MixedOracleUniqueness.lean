import QubitOracle.Paper.MixedOracleFeasible

/-!
# Coordinate-free uniqueness of the mixed-state oracle

The lower bound in `MixedOracleCoordinateFree` is attained only by the
normalized square-root information matrix.  The equality case is reduced to
Mathlib's equality characterization for Cauchy--Schwarz in a finite Euclidean
space; no equality-case axiom is introduced.
-/

namespace QubitOracle.Paper

open scoped BigOperators RealInnerProductSpace

noncomputable section

/-- Flatten a real `3 x 3` matrix into the corresponding Euclidean vector. -/
private def oracleFrobeniusVector (X : OracleMatrix) :
    EuclideanSpace ℝ (Fin 3 × Fin 3) :=
  WithLp.toLp 2 (fun ij => X ij.1 ij.2)

private theorem oracleFrobeniusVector_inner (X Y : OracleMatrix) :
    inner ℝ (oracleFrobeniusVector X) (oracleFrobeniusVector Y) =
      frobeniusInner X Y := by
  rw [PiLp.inner_apply]
  change (∑ ij : Fin 3 × Fin 3, Y ij.1 ij.2 * X ij.1 ij.2) = _
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [frobeniusInner, mul_comm]

private theorem oracleFrobeniusVector_norm_sq (X : OracleMatrix) :
    ‖oracleFrobeniusVector X‖ ^ 2 = frobeniusSq X := by
  rw [← real_inner_self_eq_norm_sq]
  rw [oracleFrobeniusVector_inner]
  rfl

private theorem sqrt_trace_transpose_mul_self (X : OracleMatrix) :
    Real.sqrt (Matrix.trace (Matrix.transpose X * X)) =
      ‖oracleFrobeniusVector X‖ := by
  rw [trace_transpose_mul_eq_frobeniusInner]
  change Real.sqrt (frobeniusSq X) = _
  rw [← oracleFrobeniusVector_norm_sq]
  exact Real.sqrt_sq (norm_nonneg _)

/-- Exact equality criterion for the matrix Hilbert--Schmidt
Cauchy--Schwarz inequality. -/
theorem matrix_trace_cauchy_schwarz_eq_iff (X Y : OracleMatrix) :
    Matrix.trace (Matrix.transpose X * Y) =
        Real.sqrt (Matrix.trace (Matrix.transpose X * X)) *
          Real.sqrt (Matrix.trace (Matrix.transpose Y * Y)) ↔
      Real.sqrt (Matrix.trace (Matrix.transpose Y * Y)) • X =
        Real.sqrt (Matrix.trace (Matrix.transpose X * X)) • Y := by
  rw [trace_transpose_mul_eq_frobeniusInner,
    sqrt_trace_transpose_mul_self, sqrt_trace_transpose_mul_self]
  constructor
  · intro h
    have hv : ‖oracleFrobeniusVector Y‖ • oracleFrobeniusVector X =
        ‖oracleFrobeniusVector X‖ • oracleFrobeniusVector Y :=
      (inner_eq_norm_mul_iff_real).1 (by
        rw [oracleFrobeniusVector_inner]
        exact h)
    ext i j
    have hij := congrArg
      (fun z : EuclideanSpace ℝ (Fin 3 × Fin 3) => z (i, j)) hv
    simpa [oracleFrobeniusVector] using hij
  · intro h
    have hv : ‖oracleFrobeniusVector Y‖ • oracleFrobeniusVector X =
        ‖oracleFrobeniusVector X‖ • oracleFrobeniusVector Y := by
      ext ij
      rcases ij with ⟨i, j⟩
      have hij := congrArg (fun Z : OracleMatrix => Z i j) h
      simpa [oracleFrobeniusVector] using hij
    have hi := (inner_eq_norm_mul_iff_real).2 hv
    rwa [oracleFrobeniusVector_inner] at hi

/-- Equality in the coordinate-free oracle lower bound uniquely fixes the
normalized information matrix to `R / trace R`. -/
theorem mixedOracle_coordinate_free_unique
    (A Ainv C H K R : OracleMatrix) (tau : ℝ)
    (hHK : H * K = 1)
    (hHsym : Matrix.transpose H = H)
    (hKsym : Matrix.transpose K = K)
    (hRsym : Matrix.transpose R = R)
    (hHsq : H * H = A)
    (hKsq : K * K = Ainv)
    (hRsq : R * R = C)
    (htraceA0 : 0 ≤ Matrix.trace A)
    (hbudget : Matrix.trace A ≤ 1)
    (htau : Matrix.trace R = tau)
    (htau_pos : 0 < tau)
    (hriskEq : Matrix.trace (C * Ainv) = tau ^ 2) :
    A = oracleMatrixOptimizer R tau := by
  have hcs := mixedOracle_matrix_cauchy_schwarz A Ainv C H K R
    hHK hHsym hKsym hRsym hHsq hKsq hRsq
  have hcs' : tau ≤ Real.sqrt (Matrix.trace A) * tau := by
    simpa [htau, hriskEq, Real.sqrt_sq htau_pos.le] using hcs
  have htraceA : Matrix.trace A = 1 := by
    nlinarith [Real.sq_sqrt htraceA0,
      Real.sqrt_nonneg (Matrix.trace A)]
  have hleft :
      Matrix.trace (Matrix.transpose H * (K * R)) = Matrix.trace R := by
    rw [hHsym, ← Matrix.mul_assoc, hHK, one_mul]
  have hfirst :
      Matrix.trace (Matrix.transpose H * H) = Matrix.trace A := by
    rw [hHsym, hHsq]
  have hsecond :
      Matrix.trace (Matrix.transpose (K * R) * (K * R)) =
        Matrix.trace (C * Ainv) := by
    calc
      Matrix.trace (Matrix.transpose (K * R) * (K * R)) =
          Matrix.trace ((R * K) * (K * R)) := by
            rw [Matrix.transpose_mul, hRsym, hKsym]
      _ = Matrix.trace (R * (K * K) * R) := by
            congr 1
            simp only [Matrix.mul_assoc]
      _ = Matrix.trace (R * Ainv * R) := by rw [hKsq]
      _ = Matrix.trace (R * R * Ainv) := Matrix.trace_mul_cycle R Ainv R
      _ = Matrix.trace (C * Ainv) := by rw [hRsq]
  have hcsEq :
      Matrix.trace (Matrix.transpose H * (K * R)) =
        Real.sqrt (Matrix.trace (Matrix.transpose H * H)) *
          Real.sqrt (Matrix.trace (Matrix.transpose (K * R) * (K * R))) := by
    rw [hleft, hfirst, hsecond, htau, htraceA, hriskEq,
      Real.sqrt_one, Real.sqrt_sq htau_pos.le, one_mul]
  have hscale :=
    (matrix_trace_cauchy_schwarz_eq_iff H (K * R)).1 hcsEq
  have hscale' : tau • H = K * R := by
    rw [hfirst, hsecond, htraceA, hriskEq, Real.sqrt_one,
      Real.sqrt_sq htau_pos.le] at hscale
    simpa using hscale
  have htauA : tau • A = R := by
    calc
      tau • A = tau • (H * H) := by rw [hHsq]
      _ = H * (tau • H) := by rw [Matrix.mul_smul]
      _ = H * (K * R) := by rw [hscale']
      _ = R := by rw [← Matrix.mul_assoc, hHK, one_mul]
  rw [oracleMatrixOptimizer, ← htauA, smul_smul]
  simp [htau_pos.ne']

namespace Label

/-- `prop:SI:mixed-oracle`: lower bound, attainment, and uniqueness of the
coordinate-free mixed-state oracle. -/
theorem prop_SI_mixed_oracle
    (A Ainv C H K R Rinv : OracleMatrix) (tau : ℝ)
    (hHK : H * K = 1)
    (hHsym : Matrix.transpose H = H)
    (hKsym : Matrix.transpose K = K)
    (hRsym : Matrix.transpose R = R)
    (hHsq : H * H = A)
    (hKsq : K * K = Ainv)
    (hRsq : R * R = C)
    (htraceA0 : 0 ≤ Matrix.trace A)
    (hbudget : Matrix.trace A ≤ 1)
    (hrisk0 : 0 ≤ Matrix.trace (C * Ainv))
    (htraceR0 : 0 ≤ Matrix.trace R)
    (htau : Matrix.trace R = tau)
    (htau0 : tau ≠ 0)
    (hRinv : R * Rinv = 1) :
    tau ^ 2 ≤ Matrix.trace (C * Ainv) ∧
      Matrix.trace (C * (oracleMatrixOptimizer R tau)⁻¹) = tau ^ 2 ∧
        (Matrix.trace (C * Ainv) = tau ^ 2 →
          A = oracleMatrixOptimizer R tau) := by
  have hoptimal := mixedOracle_coordinate_free_optimality
    A Ainv C H K R Rinv tau hHK hHsym hKsym hRsym hHsq hKsq hRsq
      htraceA0 hbudget hrisk0 htraceR0 htau htau0 hRinv
  refine ⟨hoptimal.1, hoptimal.2, ?_⟩
  intro hriskEq
  have htau_nonneg : 0 ≤ tau := by
    rw [← htau]
    exact htraceR0
  have htau_pos : 0 < tau :=
    lt_of_le_of_ne htau_nonneg (Ne.symm htau0)
  exact mixedOracle_coordinate_free_unique A Ainv C H K R tau
    hHK hHsym hKsym hRsym hHsq hKsq hRsq htraceA0 hbudget htau
      htau_pos hriskEq

end Label

end

end QubitOracle.Paper
