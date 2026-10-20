import QubitOracle.Paper.OneQubitAPSGramDetBound
import Mathlib.Analysis.Complex.ExponentialBounds

namespace QubitOracle.Paper

open MeasureTheory

noncomputable section

/-- Determinant/logarithm argument appearing in the lambda-one APS radius. -/
def oneQubitAPSRadiusLogArgument
    {Omega : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 -> Real} {axis : Nat -> Omega -> Fin 3 -> Real}
    {outcome : Nat -> Omega -> QubitRLSOutcome}
    (protocol : BinaryQubitRLSReducedProbabilityPremises Omega mu theta axis outcome)
    (hTheta : QubitOracle.blochNormSq theta <= 1)
    (n : Nat) (omega : Omega) : Real :=
  Real.sqrt ((PopularRLSConditions.aps2011Theorem2Gram
    (protocol.toSelfNormalizedMartingaleData hTheta) 1 n omega).det) /
    oneQubitPolynomialConfidenceLevel n

/-- For n at least two, the APS logarithm argument is bounded by n^10. -/
theorem oneQubitAPSRadiusLogArgument_le_pow_ten
    {Omega : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 -> Real} {axis : Nat -> Omega -> Fin 3 -> Real}
    {outcome : Nat -> Omega -> QubitRLSOutcome}
    (protocol : BinaryQubitRLSReducedProbabilityPremises Omega mu theta axis outcome)
    (hTheta : QubitOracle.blochNormSq theta <= 1)
    (n : Nat) (hn : 2 <= n) (omega : Omega) :
    oneQubitAPSRadiusLogArgument protocol hTheta n omega <= (n : Real) ^ 10 := by
  let N : Real := n
  let D : Real := (PopularRLSConditions.aps2011Theorem2Gram
    (protocol.toSelfNormalizedMartingaleData hTheta) 1 n omega).det
  have hN : (2 : Real) <= N := by
    dsimp [N]
    exact_mod_cast hn
  have hN0 : 0 <= N := le_trans (by norm_num) hN
  have hDet : D <= 6 * (N + 1) ^ 3 := by
    exact (le_abs_self D).trans
      (abs_oneQubitAPSGram_one_det_le protocol hTheta n omega)
  have hSqrtDet : Real.sqrt D <= 3 * (N + 1) ^ 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith [sq_nonneg (N + 1)]
  have hNp1 : N + 1 <= 2 * N := by linarith
  have hNp2 : N + 2 <= 2 * N := by linarith
  have hSq1 : (N + 1) ^ 2 <= (2 * N) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hNp1 2
  have hSq2 : (N + 2) ^ 2 <= (2 * N) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hNp2 2
  have hPoly : 3 * (N + 1) ^ 2 * (N + 2) ^ 2 <= 48 * N ^ 4 := by
    have hmul : (N + 1) ^ 2 * (N + 2) ^ 2 <=
        (2 * N) ^ 2 * (2 * N) ^ 2 :=
      mul_le_mul hSq1 hSq2 (sq_nonneg _) (sq_nonneg _)
    nlinarith
  have hN6 : (48 : Real) <= N ^ 6 := by
    have h64 : (64 : Real) <= N ^ 6 := by
      have hpow := pow_le_pow_left₀ (by norm_num : (0 : Real) <= 2) hN 6
      norm_num at hpow ⊢
      exact hpow
    linarith
  have h48 : 48 * N ^ 4 <= N ^ 10 := by
    have := mul_le_mul_of_nonneg_right hN6 (pow_nonneg hN0 4)
    nlinarith
  have hRewrite :
      oneQubitAPSRadiusLogArgument protocol hTheta n omega =
        Real.sqrt D * (N + 2) ^ 2 := by
    unfold oneQubitAPSRadiusLogArgument oneQubitPolynomialConfidenceLevel
    dsimp [D, N]
    field_simp
    norm_num
  rw [hRewrite]
  exact (mul_le_mul_of_nonneg_right hSqrtDet (sq_nonneg _)).trans
    (hPoly.trans h48)

/-- The APS logarithm is at most 10 log n. The zero-argument case is handled
separately because Lean's total real logarithm satisfies log 0 = 0. -/
theorem oneQubitAPSRadius_log_le_ten_log
    {Omega : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 -> Real} {axis : Nat -> Omega -> Fin 3 -> Real}
    {outcome : Nat -> Omega -> QubitRLSOutcome}
    (protocol : BinaryQubitRLSReducedProbabilityPremises Omega mu theta axis outcome)
    (hTheta : QubitOracle.blochNormSq theta <= 1)
    (n : Nat) (hn : 2 <= n) (omega : Omega) :
    Real.log (oneQubitAPSRadiusLogArgument protocol hTheta n omega) <=
      10 * Real.log (n : Real) := by
  have hN : (2 : Real) <= (n : Real) := by exact_mod_cast hn
  have hLogN : 0 <= Real.log (n : Real) :=
    Real.log_nonneg (by linarith)
  have hArgNonnegative : 0 <= oneQubitAPSRadiusLogArgument protocol hTheta n omega := by
    unfold oneQubitAPSRadiusLogArgument
    exact div_nonneg (Real.sqrt_nonneg _)
      (le_of_lt (oneQubitPolynomialConfidenceLevel_positive n))
  by_cases hzero : oneQubitAPSRadiusLogArgument protocol hTheta n omega = 0
  · simp [hzero, hLogN]
  · have hpositive : 0 < oneQubitAPSRadiusLogArgument protocol hTheta n omega :=
      lt_of_le_of_ne hArgNonnegative (Ne.symm hzero)
    calc
      Real.log (oneQubitAPSRadiusLogArgument protocol hTheta n omega) <=
          Real.log ((n : Real) ^ 10) :=
        Real.log_le_log hpositive
          (oneQubitAPSRadiusLogArgument_le_pow_ten
            protocol hTheta n hn omega)
      _ = 10 * Real.log (n : Real) := by rw [Real.log_pow]; norm_num

/-- At lambda=1 and parameter radius one, the exact APS radius has the
explicit uniform bound radius^2 <= 144 log n for all n >= 2. -/
theorem oneQubitAPSRadius_one_sq_le
    {Omega : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {theta : Fin 3 -> Real} {axis : Nat -> Omega -> Fin 3 -> Real}
    {outcome : Nat -> Omega -> QubitRLSOutcome}
    (protocol : BinaryQubitRLSReducedProbabilityPremises Omega mu theta axis outcome)
    (hTheta : QubitOracle.blochNormSq theta <= 1)
    (n : Nat) (hn : 2 <= n) (omega : Omega) :
    (PopularRLSConditions.aps2011Theorem2Radius
      (protocol.toSelfNormalizedMartingaleData hTheta)
      1 1 (oneQubitPolynomialConfidenceLevel n) n omega) ^ 2 <=
      144 * Real.log (n : Real) := by
  have hN : (2 : Real) <= (n : Real) := by exact_mod_cast hn
  have hLogN : 0 <= Real.log (n : Real) :=
    Real.log_nonneg (by linarith)
  have hLogTwo : (1 / 4 : Real) <= Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hLogTwoLe : Real.log 2 <= Real.log (n : Real) :=
    Real.log_le_log (by norm_num) hN
  have hHalfSqrt : (1 / 2 : Real) <= Real.sqrt (Real.log (n : Real)) := by
    apply (Real.le_sqrt (by norm_num) hLogN).2
    nlinarith
  have hLogArg := oneQubitAPSRadius_log_le_ten_log
    protocol hTheta n hn omega
  have hSqrt : Real.sqrt
      (2 * Real.log (oneQubitAPSRadiusLogArgument protocol hTheta n omega)) <=
      5 * Real.sqrt (Real.log (n : Real)) := by
    calc
      Real.sqrt
          (2 * Real.log (oneQubitAPSRadiusLogArgument protocol hTheta n omega)) <=
        Real.sqrt (20 * Real.log (n : Real)) := by
          apply Real.sqrt_le_sqrt
          nlinarith
      _ = Real.sqrt 20 * Real.sqrt (Real.log (n : Real)) := by
        rw [Real.sqrt_mul (by norm_num : (0 : Real) <= 20)]
      _ <= 5 * Real.sqrt (Real.log (n : Real)) := by
        gcongr
        norm_num [Real.sqrt_le_iff]
  have hRadiusFormula :
      PopularRLSConditions.aps2011Theorem2Radius
        (protocol.toSelfNormalizedMartingaleData hTheta)
        1 1 (oneQubitPolynomialConfidenceLevel n) n omega =
      2 * Real.sqrt
        (2 * Real.log (oneQubitAPSRadiusLogArgument protocol hTheta n omega)) + 1 := by
    simp [PopularRLSConditions.aps2011Theorem2Radius,
      PopularRLSConditions.aps2011Theorem2Regularizer,
      oneQubitAPSRadiusLogArgument]
  rw [hRadiusFormula]
  have hRadiusNonnegative : 0 <=
      2 * Real.sqrt
        (2 * Real.log (oneQubitAPSRadiusLogArgument protocol hTheta n omega)) + 1 := by
    positivity
  have hRadiusLe :
      2 * Real.sqrt
          (2 * Real.log (oneQubitAPSRadiusLogArgument protocol hTheta n omega)) + 1 <=
        12 * Real.sqrt (Real.log (n : Real)) := by
    nlinarith
  have hSquare := pow_le_pow_left₀ hRadiusNonnegative hRadiusLe 2
  rw [show (12 * Real.sqrt (Real.log (n : Real))) ^ 2 =
      144 * Real.log (n : Real) by
        rw [mul_pow, Real.sq_sqrt hLogN]
        norm_num] at hSquare
  exact hSquare

end

end QubitOracle.Paper
