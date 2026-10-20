import QubitOracle.Paper.MixedOracleMatrix

/-!
# Coordinate-free mixed-oracle lower bound and attainment

This module combines the matrix Cauchy--Schwarz bound with an explicit
normalized-square-root optimizer and its finite three-axis realization.
Uniqueness is intentionally not folded into the theorem: it requires the
separate equality characterization of Hilbert--Schmidt Cauchy--Schwarz.
-/

namespace QubitOracle.Paper

open scoped BigOperators

noncomputable section

/-- Matrix optimizer `C^{1/2} / trace(C^{1/2})`. -/
def oracleMatrixOptimizer (R : OracleMatrix) (tau : ℝ) : OracleMatrix :=
  tau⁻¹ • R

/-- Candidate inverse `tau C^{-1/2}`. -/
def oracleMatrixOptimizerInv (Rinv : OracleMatrix) (tau : ℝ) : OracleMatrix :=
  tau • Rinv

theorem oracleMatrixOptimizer_mul_inv
    (R Rinv : OracleMatrix) (tau : ℝ)
    (htau : tau ≠ 0) (hRinv : R * Rinv = 1) :
    oracleMatrixOptimizer R tau * oracleMatrixOptimizerInv Rinv tau = 1 := by
  unfold oracleMatrixOptimizer oracleMatrixOptimizerInv
  calc
    (tau⁻¹ • R) * (tau • Rinv) =
        (tau * tau⁻¹) • (R * Rinv) := by
          simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    _ = 1 := by simp [htau, hRinv]

theorem oracleMatrixOptimizer_inv
    (R Rinv : OracleMatrix) (tau : ℝ)
    (htau : tau ≠ 0) (hRinv : R * Rinv = 1) :
    (oracleMatrixOptimizer R tau)⁻¹ =
      oracleMatrixOptimizerInv Rinv tau := by
  apply Matrix.inv_eq_right_inv
  exact oracleMatrixOptimizer_mul_inv R Rinv tau htau hRinv

/-- The normalized square-root optimizer attains `tau^2`. -/
theorem oracleMatrixOptimizer_value
    (C R Rinv : OracleMatrix) (tau : ℝ)
    (htau : tau ≠ 0) (hRinv : R * Rinv = 1)
    (hCsq : R * R = C) (htrace : Matrix.trace R = tau) :
    Matrix.trace (C * (oracleMatrixOptimizer R tau)⁻¹) = tau ^ 2 := by
  rw [oracleMatrixOptimizer_inv R Rinv tau htau hRinv]
  unfold oracleMatrixOptimizerInv
  calc
    Matrix.trace (C * (tau • Rinv)) =
        tau * Matrix.trace (C * Rinv) := by simp
    _ = tau * Matrix.trace R := by
      rw [← hCsq]
      congr 1
      congr 1
      calc
        R * R * Rinv = R * (R * Rinv) := by noncomm_ring
        _ = R := by rw [hRinv, Matrix.mul_one]
    _ = tau ^ 2 := by rw [htrace]; ring

/-- Coordinate-free lower bound over the full trace-budget relaxation. -/
theorem mixedOracle_coordinate_free_lower_bound
    (A Ainv C H K R : OracleMatrix)
    (hHK : H * K = 1)
    (hHsym : H.transpose = H)
    (hKsym : K.transpose = K)
    (hRsym : R.transpose = R)
    (hHsq : H * H = A)
    (hKsq : K * K = Ainv)
    (hRsq : R * R = C)
    (htraceA0 : 0 ≤ Matrix.trace A)
    (hbudget : Matrix.trace A ≤ 1)
    (hrisk0 : 0 ≤ Matrix.trace (C * Ainv))
    (htraceR0 : 0 ≤ Matrix.trace R) :
    Matrix.trace R ^ 2 ≤ Matrix.trace (C * Ainv) := by
  have hcs := mixedOracle_matrix_cauchy_schwarz
    A Ainv C H K R hHK hHsym hKsym hRsym hHsq hKsq hRsq
  have hsA : Real.sqrt (Matrix.trace A) ^ 2 = Matrix.trace A :=
    Real.sq_sqrt htraceA0
  have hsRisk :
      Real.sqrt (Matrix.trace (C * Ainv)) ^ 2 =
        Matrix.trace (C * Ainv) := Real.sq_sqrt hrisk0
  have hp :
      0 ≤ Real.sqrt (Matrix.trace A) *
        Real.sqrt (Matrix.trace (C * Ainv)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsqTrace :
      Matrix.trace R ^ 2 ≤
        (Real.sqrt (Matrix.trace A) *
          Real.sqrt (Matrix.trace (C * Ainv))) ^ 2 := by
    have := mul_nonneg (sub_nonneg.mpr hcs)
      (add_nonneg hp htraceR0)
    nlinarith
  have hsqProduct :
      (Real.sqrt (Matrix.trace A) *
          Real.sqrt (Matrix.trace (C * Ainv))) ^ 2 ≤
        Matrix.trace (C * Ainv) := by
    rw [mul_pow, hsA, hsRisk]
    nlinarith
  exact hsqTrace.trans hsqProduct

/-- Lower bound plus attainment, the non-uniqueness part of the mixed oracle
proposition. -/
theorem mixedOracle_coordinate_free_optimality
    (A Ainv C H K R Rinv : OracleMatrix) (tau : ℝ)
    (hHK : H * K = 1)
    (hHsym : H.transpose = H)
    (hKsym : K.transpose = K)
    (hRsym : R.transpose = R)
    (hHsq : H * H = A)
    (hKsq : K * K = Ainv)
    (hRsq : R * R = C)
    (htraceA0 : 0 ≤ Matrix.trace A)
    (hbudget : Matrix.trace A ≤ 1)
    (hrisk0 : 0 ≤ Matrix.trace (C * Ainv))
    (htraceR0 : 0 ≤ Matrix.trace R)
    (htau : Matrix.trace R = tau) (htau0 : tau ≠ 0)
    (hRinv : R * Rinv = 1) :
    tau ^ 2 ≤ Matrix.trace (C * Ainv) ∧
      Matrix.trace (C * (oracleMatrixOptimizer R tau)⁻¹) = tau ^ 2 := by
  constructor
  · rw [← htau]
    exact mixedOracle_coordinate_free_lower_bound A Ainv C H K R
      hHK hHsym hKsym hRsym hHsq hKsq hRsq
      htraceA0 hbudget hrisk0 htraceR0
  · exact oracleMatrixOptimizer_value C R Rinv tau
      htau0 hRinv hRsq htau

/-- Spectral square root represented by eigenvalues and unit eigenvectors. -/
def oracleSpectralSqrt (r : Fin 3 -> ℝ)
    (x : Fin 3 -> Fin 3 -> ℝ) : OracleMatrix :=
  ∑ i, r i • blochOuter (x i)

def oracleThreeAxisWeight (r : Fin 3 -> ℝ) (i : Fin 3) : ℝ :=
  r i / mixedOracleSqrtTrace r

def oracleThreeAxis (S : OracleMatrix)
    (x : Fin 3 -> Fin 3 -> ℝ) (i : Fin 3) : Fin 3 -> ℝ :=
  oracleInverseXMap S (x i)

def oracleSpectralOptimizer (r : Fin 3 -> ℝ)
    (x : Fin 3 -> Fin 3 -> ℝ) : OracleMatrix :=
  ∑ i, oracleThreeAxisWeight r i • blochOuter (x i)

def oracleThreeAxisTransformedInformation
    (S T : OracleMatrix) (r : Fin 3 -> ℝ)
    (x : Fin 3 -> Fin 3 -> ℝ) : OracleMatrix :=
  ∑ i, oracleThreeAxisWeight r i •
    (T * oracleAxisInformation T (oracleThreeAxis S x i) * T.transpose)

theorem oracleSpectralOptimizer_eq_smul_sqrt
    (r : Fin 3 -> ℝ) (x : Fin 3 -> Fin 3 -> ℝ) :
    oracleSpectralOptimizer r x =
      (mixedOracleSqrtTrace r)⁻¹ • oracleSpectralSqrt r x := by
  unfold oracleSpectralOptimizer oracleSpectralSqrt oracleThreeAxisWeight
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [div_eq_mul_inv, smul_smul, mul_comm]

theorem oracleThreeAxis_realizes_optimizer
    (S T : OracleMatrix) (r : Fin 3 -> ℝ)
    (x : Fin 3 -> Fin 3 -> ℝ)
    (hTS : T * S = 1)
    (hx : ∀ i, blochNormSq (x i) = 1)
    (hSx : ∀ i, 0 < blochNormSq (S.mulVec (x i))) :
    oracleThreeAxisTransformedInformation S T r x =
      oracleSpectralOptimizer r x := by
  unfold oracleThreeAxisTransformedInformation oracleSpectralOptimizer
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [oracle_rank_one_map_normalized]
  exact oracleInverseXMap_realizes_projector S T (x i)
    hTS (hx i) (hSx i)

/-- The invariant radial-to-tangent square-root ratio from the supplement. -/
def invariantOracleH (s gt gr : ℝ) : ℝ :=
  Real.sqrt (((1 - s ^ 2) * gr) / gt)

/-- Two tangent square-root eigenvalues and one radial eigenvalue. -/
def invariantOracleSpectrum (s gt gr : ℝ) : Fin 3 -> ℝ :=
  ![Real.sqrt gt, Real.sqrt gt,
    Real.sqrt gt * invariantOracleH s gt gr]

theorem invariantOracleSqrtTrace (s gt gr : ℝ) :
    mixedOracleSqrtTrace (invariantOracleSpectrum s gt gr) =
      Real.sqrt gt * (2 + invariantOracleH s gt gr) := by
  simp [mixedOracleSqrtTrace, invariantOracleSpectrum,
    Fin.sum_univ_succ]
  ring

theorem invariantOracleWeights
    (s gt gr : ℝ) (hgt : 0 < gt) :
    oracleThreeAxisWeight (invariantOracleSpectrum s gt gr) 0 =
        1 / (2 + invariantOracleH s gt gr) ∧
      oracleThreeAxisWeight (invariantOracleSpectrum s gt gr) 1 =
        1 / (2 + invariantOracleH s gt gr) ∧
      oracleThreeAxisWeight (invariantOracleSpectrum s gt gr) 2 =
        invariantOracleH s gt gr /
          (2 + invariantOracleH s gt gr) := by
  have hsqrt : Real.sqrt gt ≠ 0 := (Real.sqrt_pos.2 hgt).ne'
  have hh : 0 ≤ invariantOracleH s gt gr := Real.sqrt_nonneg _
  have hden : 2 + invariantOracleH s gt gr ≠ 0 := by linarith
  rw [oracleThreeAxisWeight, oracleThreeAxisWeight,
    oracleThreeAxisWeight, invariantOracleSqrtTrace]
  simp [invariantOracleSpectrum]
  constructor <;> field_simp [hsqrt, hden] <;> ring

theorem invariantOracleRiskValue
    (s gt gr : ℝ) (hgt : 0 < gt) :
    mixedOracleSqrtTrace (invariantOracleSpectrum s gt gr) ^ 2 =
      gt * (2 + invariantOracleH s gt gr) ^ 2 := by
  rw [invariantOracleSqrtTrace, mul_pow, Real.sq_sqrt hgt.le]

end

end QubitOracle.Paper
