import QubitOracle.Paper.OneQubitMixedBuresRemainder

/-!
# Full general-direction interior mixed-qubit Bures remainder

This file retains the radial scalar

`x = blochDot theta h / sqrt N`

instead of imposing the tangential condition `x = 0`.  The proof is entirely
algebraic and starts from the exact nested-square-root formula
`qubitBlochFidelitySq`.

Write `a = 1 - rSq`,
`t = sqrt (a * (a - 2*x - q))`, and
`A = x^2 + a*q`.  Rationalization gives

`1 - fidelity = A / (2 * (a - x + t))`

and the exact decomposition

`Bures - (q + x^2/a)/4
  = (1 - sqrt fidelity)^2
    + A * (a + x - t) / (4*a*(a-x+t))`.

The second summand contains the sign-changing odd cubic term.  Under the
explicit local condition `2*|x| + q <= a/2`, both square-root denominators are
bounded below by `a`, and direct rationalization bounds the odd numerator.
Using `x^2 <= rSq*q` then gives

`|Bures - (q + x^2/a)/4|
  <= |x|*q/margin^2 + (x^2*q + q^2)/margin^3`.

After substituting `x = b/sqrt N`, `q = c/N`, this becomes a cubic over
`sqrt N` plus a quartic over `N`.  No Taylor theorem or assumed remainder
estimate is used.
-/

namespace QubitOracle.Paper

noncomputable section

open scoped BigOperators ENNReal

/-! ## Scalar local region and exact algebra -/

/-- Explicit scalar region for the general-direction mixed-qubit expansion. -/
structure MixedBuresGeneralScalarRegion
    (rSq x q margin : ℝ) : Prop where
  radius_nonnegative : 0 ≤ rSq
  margin_positive : 0 < margin
  margin_le_gap : margin ≤ 1 - rSq
  displacement_nonnegative : 0 ≤ q
  cauchy : x ^ 2 ≤ rSq * q
  local_radius : 2 * |x| + q ≤ (1 - rSq) / 2

/-- Interior radial gap. -/
def mixedBuresGeneralGap (rSq : ℝ) : ℝ :=
  1 - rSq

/-- Inner square root in the exact qubit fidelity formula. -/
def mixedBuresGeneralInnerRoot (rSq x q : ℝ) : ℝ :=
  Real.sqrt
    (mixedBuresGeneralGap rSq *
      (mixedBuresGeneralGap rSq - 2 * x - q))

/-- Positive rationalization denominator. -/
def mixedBuresGeneralDenominator (rSq x q : ℝ) : ℝ :=
  mixedBuresGeneralGap rSq - x +
    mixedBuresGeneralInnerRoot rSq x q

/-- Numerator carrying the sign-changing odd cubic contribution. -/
def mixedBuresGeneralOddNumerator (rSq x q : ℝ) : ℝ :=
  mixedBuresGeneralGap rSq + x -
    mixedBuresGeneralInnerRoot rSq x q

/-- Nonnegative rationalized fidelity-defect numerator. -/
def mixedBuresGeneralEnergy (rSq x q : ℝ) : ℝ :=
  x ^ 2 + mixedBuresGeneralGap rSq * q

/-- Scalar Bures quadratic form. -/
def mixedBuresGeneralQuadratic (rSq x q : ℝ) : ℝ :=
  (q + x ^ 2 / mixedBuresGeneralGap rSq) / 4

/-- Fidelity defect before the outer square-root conversion to Bures loss. -/
def mixedBuresGeneralFidelityDefect (rSq x q : ℝ) : ℝ :=
  1 - qubitBlochFidelitySq rSq x q

/-- Exact odd term in the Bures remainder decomposition. -/
def mixedBuresGeneralOddTerm (rSq x q : ℝ) : ℝ :=
  mixedBuresGeneralEnergy rSq x q *
      mixedBuresGeneralOddNumerator rSq x q /
    (4 * mixedBuresGeneralGap rSq *
      mixedBuresGeneralDenominator rSq x q)

private theorem mixedBuresGeneral_gap_pos
    {rSq x q margin : ℝ}
    (h : MixedBuresGeneralScalarRegion rSq x q margin) :
    0 < mixedBuresGeneralGap rSq := by
  unfold mixedBuresGeneralGap
  exact lt_of_lt_of_le h.margin_positive h.margin_le_gap

private theorem mixedBuresGeneral_gap_le_one
    {rSq x q margin : ℝ}
    (h : MixedBuresGeneralScalarRegion rSq x q margin) :
    mixedBuresGeneralGap rSq ≤ 1 := by
  unfold mixedBuresGeneralGap
  linarith [h.radius_nonnegative]

private theorem mixedBuresGeneral_abs_x_le_quarter_gap
    {rSq x q margin : ℝ}
    (h : MixedBuresGeneralScalarRegion rSq x q margin) :
    |x| ≤ mixedBuresGeneralGap rSq / 4 := by
  have hq := h.displacement_nonnegative
  simpa [mixedBuresGeneralGap] using
    (show |x| ≤ (1 - rSq) / 4 by nlinarith [h.local_radius])

private theorem mixedBuresGeneral_inner_residual_ge_half_gap
    {rSq x q margin : ℝ}
    (h : MixedBuresGeneralScalarRegion rSq x q margin) :
    mixedBuresGeneralGap rSq / 2 ≤
      mixedBuresGeneralGap rSq - 2 * x - q := by
  have hx : x ≤ |x| := le_abs_self x
  unfold mixedBuresGeneralGap
  nlinarith [h.local_radius]

private theorem mixedBuresGeneral_inner_radicand_nonnegative
    {rSq x q margin : ℝ}
    (h : MixedBuresGeneralScalarRegion rSq x q margin) :
    0 ≤ mixedBuresGeneralGap rSq *
      (mixedBuresGeneralGap rSq - 2 * x - q) := by
  have hhalf : 0 ≤ mixedBuresGeneralGap rSq / 2 :=
    div_nonneg (mixedBuresGeneral_gap_pos h).le (by norm_num)
  exact mul_nonneg (mixedBuresGeneral_gap_pos h).le
    (hhalf.trans (mixedBuresGeneral_inner_residual_ge_half_gap h))

private theorem mixedBuresGeneral_innerRoot_sq
    {rSq x q margin : ℝ}
    (h : MixedBuresGeneralScalarRegion rSq x q margin) :
    (mixedBuresGeneralInnerRoot rSq x q) ^ 2 =
      mixedBuresGeneralGap rSq *
        (mixedBuresGeneralGap rSq - 2 * x - q) := by
  unfold mixedBuresGeneralInnerRoot
  exact Real.sq_sqrt (mixedBuresGeneral_inner_radicand_nonnegative h)

private theorem mixedBuresGeneral_innerRoot_ge_half_gap
    {rSq x q margin : ℝ}
    (h : MixedBuresGeneralScalarRegion rSq x q margin) :
    mixedBuresGeneralGap rSq / 2 ≤
      mixedBuresGeneralInnerRoot rSq x q := by
  let a := mixedBuresGeneralGap rSq
  let t := mixedBuresGeneralInnerRoot rSq x q
  have ha : 0 < a := mixedBuresGeneral_gap_pos h
  have ht : 0 ≤ t := by
    dsimp [t]
    exact Real.sqrt_nonneg _
  have ht_sq : t ^ 2 =
      a * (a - 2 * x - q) := by
    simpa [a, t] using mixedBuresGeneral_innerRoot_sq h
  have hresidual : a / 2 ≤ a - 2 * x - q := by
    simpa [a] using mixedBuresGeneral_inner_residual_ge_half_gap h
  have ht_sq_lower : a ^ 2 / 2 ≤ t ^ 2 := by
    rw [ht_sq]
    nlinarith [mul_le_mul_of_nonneg_left hresidual ha.le]
  by_contra hnot
  have hlt : t < a / 2 := lt_of_not_ge hnot
  have ht_sq_upper : t ^ 2 < a ^ 2 / 4 := by
    nlinarith
  nlinarith [sq_nonneg a]

private theorem mixedBuresGeneral_denominator_ge_gap
    {rSq x q margin : ℝ}
    (h : MixedBuresGeneralScalarRegion rSq x q margin) :
    mixedBuresGeneralGap rSq ≤
      mixedBuresGeneralDenominator rSq x q := by
  have hx := mixedBuresGeneral_abs_x_le_quarter_gap h
  have ht := mixedBuresGeneral_innerRoot_ge_half_gap h
  have hquarter_half :
      mixedBuresGeneralGap rSq / 4 ≤
        mixedBuresGeneralGap rSq / 2 := by
    linarith [mixedBuresGeneral_gap_pos h]
  have habs_le_t : |x| ≤ mixedBuresGeneralInnerRoot rSq x q :=
    hx.trans (hquarter_half.trans ht)
  have hx_le_t : x ≤ mixedBuresGeneralInnerRoot rSq x q :=
    (le_abs_self x).trans habs_le_t
  unfold mixedBuresGeneralDenominator
  linarith

private theorem mixedBuresGeneral_conjugateDenominator_ge_gap
    {rSq x q margin : ℝ}
    (h : MixedBuresGeneralScalarRegion rSq x q margin) :
    mixedBuresGeneralGap rSq ≤
      mixedBuresGeneralGap rSq + x +
      mixedBuresGeneralInnerRoot rSq x q := by
  have hx := mixedBuresGeneral_abs_x_le_quarter_gap h
  have ht := mixedBuresGeneral_innerRoot_ge_half_gap h
  have hquarter_half :
      mixedBuresGeneralGap rSq / 4 ≤
        mixedBuresGeneralGap rSq / 2 := by
    linarith [mixedBuresGeneral_gap_pos h]
  have habs_le_t : |x| ≤ mixedBuresGeneralInnerRoot rSq x q :=
    hx.trans (hquarter_half.trans ht)
  have hnegx_le_t : -x ≤ mixedBuresGeneralInnerRoot rSq x q :=
    (neg_le_abs x).trans habs_le_t
  nlinarith

private theorem mixedBuresGeneral_energy_nonnegative
    {rSq x q margin : ℝ}
    (h : MixedBuresGeneralScalarRegion rSq x q margin) :
    0 ≤ mixedBuresGeneralEnergy rSq x q := by
  unfold mixedBuresGeneralEnergy
  exact add_nonneg (sq_nonneg x)
    (mul_nonneg (mixedBuresGeneral_gap_pos h).le
      h.displacement_nonnegative)

private theorem mixedBuresGeneral_energy_le_q
    {rSq x q margin : ℝ}
    (h : MixedBuresGeneralScalarRegion rSq x q margin) :
    mixedBuresGeneralEnergy rSq x q ≤ q := by
  unfold mixedBuresGeneralEnergy mixedBuresGeneralGap
  nlinarith [h.cauchy]

/-- Rationalization identity for the fidelity defect. -/
theorem mixedBuresGeneral_fidelityDefect_product
    {rSq x q margin : ℝ}
    (h : MixedBuresGeneralScalarRegion rSq x q margin) :
    (mixedBuresGeneralGap rSq - x -
        mixedBuresGeneralInnerRoot rSq x q) *
      mixedBuresGeneralDenominator rSq x q =
        mixedBuresGeneralEnergy rSq x q := by
  unfold mixedBuresGeneralDenominator mixedBuresGeneralEnergy
  calc
    (mixedBuresGeneralGap rSq - x -
        mixedBuresGeneralInnerRoot rSq x q) *
        (mixedBuresGeneralGap rSq - x +
          mixedBuresGeneralInnerRoot rSq x q) =
      (mixedBuresGeneralGap rSq - x) ^ 2 -
        mixedBuresGeneralInnerRoot rSq x q ^ 2 := by ring
    _ = x ^ 2 + mixedBuresGeneralGap rSq * q := by
      rw [mixedBuresGeneral_innerRoot_sq h]
      ring

/-- Rationalization identity for the odd numerator. -/
theorem mixedBuresGeneral_oddNumerator_product
    {rSq x q margin : ℝ}
    (h : MixedBuresGeneralScalarRegion rSq x q margin) :
    mixedBuresGeneralOddNumerator rSq x q *
      (mixedBuresGeneralGap rSq + x +
        mixedBuresGeneralInnerRoot rSq x q) =
      4 * mixedBuresGeneralGap rSq * x + x ^ 2 +
        mixedBuresGeneralGap rSq * q := by
  unfold mixedBuresGeneralOddNumerator
  calc
    (mixedBuresGeneralGap rSq + x -
        mixedBuresGeneralInnerRoot rSq x q) *
        (mixedBuresGeneralGap rSq + x +
          mixedBuresGeneralInnerRoot rSq x q) =
      (mixedBuresGeneralGap rSq + x) ^ 2 -
        mixedBuresGeneralInnerRoot rSq x q ^ 2 := by ring
    _ = 4 * mixedBuresGeneralGap rSq * x + x ^ 2 +
        mixedBuresGeneralGap rSq * q := by
      rw [mixedBuresGeneral_innerRoot_sq h]
      ring

/-- Fidelity defect written in terms of the inner-root variables. -/
theorem mixedBuresGeneral_fidelityDefect_eq
    (rSq x q : ℝ) :
    mixedBuresGeneralFidelityDefect rSq x q =
      (mixedBuresGeneralGap rSq - x -
        mixedBuresGeneralInnerRoot rSq x q) / 2 := by
  unfold mixedBuresGeneralFidelityDefect qubitBlochFidelitySq
    mixedBuresGeneralInnerRoot mixedBuresGeneralGap
  ring_nf

/-- The scalar quadratic form equals `energy/(4*gap)`. -/
theorem mixedBuresGeneral_quadratic_eq_energy_div
    {rSq x q margin : ℝ}
    (h : MixedBuresGeneralScalarRegion rSq x q margin) :
    mixedBuresGeneralQuadratic rSq x q =
      mixedBuresGeneralEnergy rSq x q /
        (4 * mixedBuresGeneralGap rSq) := by
  have ha : mixedBuresGeneralGap rSq ≠ 0 :=
    ne_of_gt (mixedBuresGeneral_gap_pos h)
  unfold mixedBuresGeneralQuadratic mixedBuresGeneralEnergy
  field_simp [ha]
  ring

/-- The fidelity defect is nonnegative. -/
theorem mixedBuresGeneral_fidelityDefect_nonnegative
    {rSq x q margin : ℝ}
    (h : MixedBuresGeneralScalarRegion rSq x q margin) :
    0 ≤ mixedBuresGeneralFidelityDefect rSq x q := by
  have hgap := mixedBuresGeneral_gap_pos h
  have hden := mixedBuresGeneral_denominator_ge_gap h
  have hdenpos : 0 < mixedBuresGeneralDenominator rSq x q :=
    lt_of_lt_of_le hgap hden
  have henergy := mixedBuresGeneral_energy_nonnegative h
  have hproduct := mixedBuresGeneral_fidelityDefect_product h
  rw [mixedBuresGeneral_fidelityDefect_eq]
  by_contra hnot
  have hnegative :
      mixedBuresGeneralGap rSq - x -
          mixedBuresGeneralInnerRoot rSq x q < 0 := by
    linarith
  have hproductNegative :
      (mixedBuresGeneralGap rSq - x -
          mixedBuresGeneralInnerRoot rSq x q) *
        mixedBuresGeneralDenominator rSq x q < 0 :=
    mul_neg_of_neg_of_pos hnegative hdenpos
  rw [hproduct] at hproductNegative
  linarith

private theorem mixedBuresGeneral_fidelity_nonnegative
    {rSq x q margin : ℝ}
    (h : MixedBuresGeneralScalarRegion rSq x q margin) :
    0 ≤ qubitBlochFidelitySq rSq x q := by
  have ha_le := mixedBuresGeneral_gap_le_one h
  have hx := mixedBuresGeneral_abs_x_le_quarter_gap h
  have hxlower : -|x| ≤ x := neg_abs_le x
  have ht : 0 ≤ mixedBuresGeneralInnerRoot rSq x q :=
    Real.sqrt_nonneg _
  have hxgap : -(mixedBuresGeneralGap rSq) / 4 ≤ x := by
    linarith [neg_abs_le x]
  unfold qubitBlochFidelitySq mixedBuresGeneralInnerRoot
    mixedBuresGeneralGap at *
  linarith

private theorem mixedBuresGeneral_fidelity_le_one
    {rSq x q margin : ℝ}
    (h : MixedBuresGeneralScalarRegion rSq x q margin) :
    qubitBlochFidelitySq rSq x q ≤ 1 := by
  have hw := mixedBuresGeneral_fidelityDefect_nonnegative h
  unfold mixedBuresGeneralFidelityDefect at hw
  linarith

/-- Exact quotient formula for the fidelity defect. -/
theorem mixedBuresGeneral_fidelityDefect_quotient
    {rSq x q margin : ℝ}
    (h : MixedBuresGeneralScalarRegion rSq x q margin) :
    mixedBuresGeneralFidelityDefect rSq x q =
      mixedBuresGeneralEnergy rSq x q /
        (2 * mixedBuresGeneralDenominator rSq x q) := by
  have hdenpos : 0 < mixedBuresGeneralDenominator rSq x q :=
    lt_of_lt_of_le (mixedBuresGeneral_gap_pos h)
      (mixedBuresGeneral_denominator_ge_gap h)
  rw [mixedBuresGeneral_fidelityDefect_eq]
  apply (div_eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)
    (mul_ne_zero (by norm_num) (ne_of_gt hdenpos))).2
  calc
    (mixedBuresGeneralGap rSq - x -
        mixedBuresGeneralInnerRoot rSq x q) *
        (2 * mixedBuresGeneralDenominator rSq x q) =
      2 * ((mixedBuresGeneralGap rSq - x -
        mixedBuresGeneralInnerRoot rSq x q) *
          mixedBuresGeneralDenominator rSq x q) := by ring
    _ = 2 * mixedBuresGeneralEnergy rSq x q := by
      rw [mixedBuresGeneral_fidelityDefect_product h]
    _ = mixedBuresGeneralEnergy rSq x q * 2 := by ring

/-- Exact sign-changing odd part of the fidelity-defect remainder. -/
theorem mixedBuresGeneral_fidelityDefect_sub_quadratic
    {rSq x q margin : ℝ}
    (h : MixedBuresGeneralScalarRegion rSq x q margin) :
    mixedBuresGeneralFidelityDefect rSq x q -
        mixedBuresGeneralQuadratic rSq x q =
      mixedBuresGeneralOddTerm rSq x q := by
  have ha : mixedBuresGeneralGap rSq ≠ 0 :=
    ne_of_gt (mixedBuresGeneral_gap_pos h)
  have hden : mixedBuresGeneralDenominator rSq x q ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (mixedBuresGeneral_gap_pos h)
      (mixedBuresGeneral_denominator_ge_gap h))
  rw [mixedBuresGeneral_fidelityDefect_quotient h,
    mixedBuresGeneral_quadratic_eq_energy_div h]
  unfold mixedBuresGeneralOddTerm
  field_simp [ha, hden]
  unfold mixedBuresGeneralOddNumerator mixedBuresGeneralDenominator
  ring

/-- Exact decomposition isolating the odd cubic term. -/
theorem mixedBuresGeneral_exact_remainder_decomposition
    {rSq x q margin : ℝ}
    (h : MixedBuresGeneralScalarRegion rSq x q margin) :
    qubitBlochBuresSq rSq x q -
        mixedBuresGeneralQuadratic rSq x q =
      (1 - Real.sqrt (qubitBlochFidelitySq rSq x q)) ^ 2 +
        mixedBuresGeneralOddTerm rSq x q := by
  have hF : 0 ≤ qubitBlochFidelitySq rSq x q :=
    mixedBuresGeneral_fidelity_nonnegative h
  have hsquare :
      (Real.sqrt (qubitBlochFidelitySq rSq x q)) ^ 2 =
        qubitBlochFidelitySq rSq x q :=
    Real.sq_sqrt hF
  have houter :
      qubitBlochBuresSq rSq x q -
          mixedBuresGeneralFidelityDefect rSq x q =
        (1 - Real.sqrt (qubitBlochFidelitySq rSq x q)) ^ 2 := by
    unfold qubitBlochBuresSq mixedBuresGeneralFidelityDefect
    nlinarith
  calc
    qubitBlochBuresSq rSq x q -
        mixedBuresGeneralQuadratic rSq x q =
      (qubitBlochBuresSq rSq x q -
        mixedBuresGeneralFidelityDefect rSq x q) +
      (mixedBuresGeneralFidelityDefect rSq x q -
        mixedBuresGeneralQuadratic rSq x q) := by ring
    _ = (1 - Real.sqrt (qubitBlochFidelitySq rSq x q)) ^ 2 +
        mixedBuresGeneralOddTerm rSq x q := by
      rw [houter, mixedBuresGeneral_fidelityDefect_sub_quadratic h]

/-! ## Direct bounds for both exact summands -/

/-- The odd numerator is bounded by direct conjugate rationalization. -/
theorem mixedBuresGeneral_oddNumerator_abs_le
    {rSq x q margin : ℝ}
    (h : MixedBuresGeneralScalarRegion rSq x q margin) :
    |mixedBuresGeneralOddNumerator rSq x q| ≤
      4 * |x| + x ^ 2 / mixedBuresGeneralGap rSq + q := by
  let a := mixedBuresGeneralGap rSq
  let t := mixedBuresGeneralInnerRoot rSq x q
  let L := mixedBuresGeneralOddNumerator rSq x q
  let E := a + x + t
  have ha : 0 < a := mixedBuresGeneral_gap_pos h
  have hE : a ≤ E := by
    simpa [a, t, E] using
      mixedBuresGeneral_conjugateDenominator_ge_gap h
  have hE_nonneg : 0 ≤ E := le_trans ha.le hE
  have hprod : L * E = 4 * a * x + x ^ 2 + a * q := by
    simpa [a, t, L, E] using mixedBuresGeneral_oddNumerator_product h
  have hfirst : |4 * a * x| = 4 * a * |x| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
      abs_of_nonneg ha.le]
  have hsecond : |x ^ 2 + a * q| = x ^ 2 + a * q := by
    rw [abs_of_nonneg]
    exact add_nonneg (sq_nonneg x)
      (mul_nonneg ha.le h.displacement_nonnegative)
  have hnum :
      |4 * a * x + x ^ 2 + a * q| ≤
        4 * a * |x| + x ^ 2 + a * q := by
    have hadd := abs_add_le (4 * a * x) (x ^ 2 + a * q)
    rw [hfirst, hsecond] at hadd
    simpa [add_assoc] using hadd
  have habsprod : |L| * E = |4 * a * x + x ^ 2 + a * q| := by
    calc
      |L| * E = |L| * |E| := by rw [abs_of_nonneg hE_nonneg]
      _ = |L * E| := (abs_mul L E).symm
      _ = |4 * a * x + x ^ 2 + a * q| := by rw [hprod]
  have hmul :
      a * |L| ≤ 4 * a * |x| + x ^ 2 + a * q := by
    calc
      a * |L| ≤ E * |L| :=
        mul_le_mul_of_nonneg_right hE (abs_nonneg L)
      _ = |L| * E := mul_comm _ _
      _ = |4 * a * x + x ^ 2 + a * q| := habsprod
      _ ≤ 4 * a * |x| + x ^ 2 + a * q := hnum
  calc
    |mixedBuresGeneralOddNumerator rSq x q| = |L| := rfl
    _ ≤ (4 * a * |x| + x ^ 2 + a * q) / a := by
      apply (le_div_iff₀ ha).2
      simpa [mul_comm] using hmul
    _ = 4 * |x| + x ^ 2 / a + q := by
      field_simp [ne_of_gt ha]
    _ = 4 * |x| + x ^ 2 / mixedBuresGeneralGap rSq + q := rfl

/-- The outer square-root remainder is nonnegative and fourth order. -/
theorem mixedBuresGeneral_outerRemainder_bounds
    {rSq x q margin : ℝ}
    (h : MixedBuresGeneralScalarRegion rSq x q margin) :
    0 ≤ qubitBlochBuresSq rSq x q -
        mixedBuresGeneralFidelityDefect rSq x q ∧
    qubitBlochBuresSq rSq x q -
        mixedBuresGeneralFidelityDefect rSq x q ≤
      q ^ 2 / (4 * mixedBuresGeneralGap rSq ^ 2) := by
  let F := qubitBlochFidelitySq rSq x q
  let s := Real.sqrt F
  let w := mixedBuresGeneralFidelityDefect rSq x q
  let a := mixedBuresGeneralGap rSq
  let A := mixedBuresGeneralEnergy rSq x q
  let D := mixedBuresGeneralDenominator rSq x q
  have ha : 0 < a := mixedBuresGeneral_gap_pos h
  have hD : a ≤ D := by
    simpa [a, D] using mixedBuresGeneral_denominator_ge_gap h
  have hDpos : 0 < D := lt_of_lt_of_le ha hD
  have hA : 0 ≤ A := by
    simpa [A] using mixedBuresGeneral_energy_nonnegative h
  have hAq : A ≤ q := by
    simpa [A] using mixedBuresGeneral_energy_le_q h
  have hwquot : w = A / (2 * D) := by
    simpa [w, A, D] using mixedBuresGeneral_fidelityDefect_quotient h
  have hw0 : 0 ≤ w := by
    simpa [w] using mixedBuresGeneral_fidelityDefect_nonnegative h
  have hwupper : w ≤ q / (2 * a) := by
    rw [hwquot]
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * D)
      (by positivity : 0 < 2 * a)).2
    have hmul : A * a ≤ q * D := by
      calc
        A * a ≤ q * a := mul_le_mul_of_nonneg_right hAq ha.le
        _ ≤ q * D :=
          mul_le_mul_of_nonneg_left hD h.displacement_nonnegative
    nlinarith
  have hF0 : 0 ≤ F := by
    simpa [F] using mixedBuresGeneral_fidelity_nonnegative h
  have hF1 : F ≤ 1 := by
    simpa [F] using mixedBuresGeneral_fidelity_le_one h
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = F := by
    dsimp [s]
    exact Real.sq_sqrt hF0
  have hs1 : s ≤ 1 := by
    by_contra hnot
    have hone : 1 < s := lt_of_not_ge hnot
    nlinarith
  have houter :
      qubitBlochBuresSq rSq x q - w = (1 - s) ^ 2 := by
    dsimp [w, s, F]
    unfold qubitBlochBuresSq mixedBuresGeneralFidelityDefect
    nlinarith
  have hone_nonneg : 0 ≤ 1 - s := sub_nonneg.mpr hs1
  have hone_le_w : 1 - s ≤ w := by
    have hws : w = 1 - s ^ 2 := by
      dsimp [w, F]
      rw [hs_sq]
      rfl
    have hmul : 0 ≤ s * (1 - s) := mul_nonneg hs0 hone_nonneg
    rw [hws]
    nlinarith
  have hsquare_le : (1 - s) ^ 2 ≤ w ^ 2 := by
    have hmul : 0 ≤ (w - (1 - s)) * (w + (1 - s)) :=
      mul_nonneg (sub_nonneg.mpr hone_le_w)
        (add_nonneg hw0 hone_nonneg)
    nlinarith
  have hqdiv0 : 0 ≤ q / (2 * a) :=
    div_nonneg h.displacement_nonnegative
      (mul_nonneg (by norm_num) ha.le)
  have hw_sq_le : w ^ 2 ≤ (q / (2 * a)) ^ 2 := by
    have hmul :
        0 ≤ (q / (2 * a) - w) * (q / (2 * a) + w) :=
      mul_nonneg (sub_nonneg.mpr hwupper)
        (add_nonneg hqdiv0 hw0)
    nlinarith
  constructor
  · rw [show qubitBlochBuresSq rSq x q -
      mixedBuresGeneralFidelityDefect rSq x q = (1 - s) ^ 2 by
        simpa [w] using houter]
    positivity
  · calc
      qubitBlochBuresSq rSq x q -
          mixedBuresGeneralFidelityDefect rSq x q =
        (1 - s) ^ 2 := by simpa [w] using houter
      _ ≤ w ^ 2 := hsquare_le
      _ ≤ (q / (2 * a)) ^ 2 := hw_sq_le
      _ = q ^ 2 / (4 * mixedBuresGeneralGap rSq ^ 2) := by
        dsimp [a]
        ring

/-- Direct bound for the exact odd term. -/
theorem mixedBuresGeneral_oddTerm_abs_le
    {rSq x q margin : ℝ}
    (h : MixedBuresGeneralScalarRegion rSq x q margin) :
    |mixedBuresGeneralOddTerm rSq x q| ≤
      |x| * q / mixedBuresGeneralGap rSq ^ 2 +
      x ^ 2 * q / (4 * mixedBuresGeneralGap rSq ^ 3) +
      q ^ 2 / (4 * mixedBuresGeneralGap rSq ^ 2) := by
  let a := mixedBuresGeneralGap rSq
  let A := mixedBuresGeneralEnergy rSq x q
  let L := mixedBuresGeneralOddNumerator rSq x q
  let D := mixedBuresGeneralDenominator rSq x q
  let U := 4 * |x| + x ^ 2 / a + q
  have ha : 0 < a := mixedBuresGeneral_gap_pos h
  have hD : a ≤ D := by
    simpa [a, D] using mixedBuresGeneral_denominator_ge_gap h
  have hDpos : 0 < D := lt_of_lt_of_le ha hD
  have hA0 : 0 ≤ A := by
    simpa [A] using mixedBuresGeneral_energy_nonnegative h
  have hAq : A ≤ q := by
    simpa [A] using mixedBuresGeneral_energy_le_q h
  have hL : |L| ≤ U := by
    simpa [a, L, U] using mixedBuresGeneral_oddNumerator_abs_le h
  have hU0 : 0 ≤ U := by
    dsimp [U]
    exact add_nonneg
      (add_nonneg (mul_nonneg (by norm_num) (abs_nonneg x))
        (div_nonneg (sq_nonneg x) ha.le))
      h.displacement_nonnegative
  have habs :
      |mixedBuresGeneralOddTerm rSq x q| =
        A * |L| / (4 * a * D) := by
    change |A * L / (4 * a * D)| = A * |L| / (4 * a * D)
    rw [abs_div, abs_mul A L, abs_mul (4 * a) D,
      abs_of_nonneg hA0, abs_of_pos (mul_pos (by norm_num) ha),
      abs_of_pos hDpos]
  have hden : 4 * a ^ 2 ≤ 4 * a * D := by
    nlinarith [mul_le_mul_of_nonneg_left hD ha.le]
  calc
    |mixedBuresGeneralOddTerm rSq x q| =
        A * |L| / (4 * a * D) := habs
    _ ≤ q * U / (4 * a * D) := by
      gcongr
      exact h.displacement_nonnegative
    _ ≤ q * U / (4 * a ^ 2) := by
      gcongr
      exact mul_nonneg h.displacement_nonnegative hU0
    _ = |x| * q / a ^ 2 + x ^ 2 * q / (4 * a ^ 3) +
        q ^ 2 / (4 * a ^ 2) := by
      dsimp [U]
      field_simp [ne_of_gt ha]
    _ = |x| * q / mixedBuresGeneralGap rSq ^ 2 +
        x ^ 2 * q / (4 * mixedBuresGeneralGap rSq ^ 3) +
        q ^ 2 / (4 * mixedBuresGeneralGap rSq ^ 2) := rfl

/-- Full scalar absolute remainder with an explicit polynomial margin
constant. -/
theorem qubitBlochBuresSq_general_margin_remainder
    {rSq x q margin : ℝ}
    (h : MixedBuresGeneralScalarRegion rSq x q margin) :
    |qubitBlochBuresSq rSq x q -
        mixedBuresGeneralQuadratic rSq x q| ≤
      |x| * q / margin ^ 2 +
        (x ^ 2 * q + q ^ 2) / margin ^ 3 := by
  let a := mixedBuresGeneralGap rSq
  have ha : 0 < a := mixedBuresGeneral_gap_pos h
  have hmargin : 0 < margin := h.margin_positive
  have hma : margin ≤ a := h.margin_le_gap
  have ha1 : a ≤ 1 := mixedBuresGeneral_gap_le_one h
  have hm1 : margin ≤ 1 := hma.trans ha1
  have hmargin0 : 0 ≤ margin := hmargin.le
  have hpow2 : margin ^ 2 ≤ a ^ 2 := by gcongr
  have hpow3 : margin ^ 3 ≤ a ^ 3 := by gcongr
  have hm3_le_m2 : margin ^ 3 ≤ margin ^ 2 := by
    calc
      margin ^ 3 = margin ^ 2 * margin := by ring
      _ ≤ margin ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hm1 (sq_nonneg margin)
      _ = margin ^ 2 := mul_one _
  have hinv2 : 1 / a ^ 2 ≤ 1 / margin ^ 2 :=
    one_div_le_one_div_of_le (sq_pos_of_pos hmargin) hpow2
  have hinv3 : 1 / a ^ 3 ≤ 1 / margin ^ 3 :=
    one_div_le_one_div_of_le (pow_pos hmargin 3) hpow3
  have hinv2_to3 : 1 / a ^ 2 ≤ 1 / margin ^ 3 := by
    calc
      1 / a ^ 2 ≤ 1 / margin ^ 2 := hinv2
      _ ≤ 1 / margin ^ 3 :=
        one_div_le_one_div_of_le (pow_pos hmargin 3) hm3_le_m2
  have houter := mixedBuresGeneral_outerRemainder_bounds h
  have hodd := mixedBuresGeneral_oddTerm_abs_le h
  have hdecomp := mixedBuresGeneral_exact_remainder_decomposition h
  have habsSum := abs_add_le
    ((1 - Real.sqrt (qubitBlochFidelitySq rSq x q)) ^ 2)
    (mixedBuresGeneralOddTerm rSq x q)
  have houter_eq :
      (1 - Real.sqrt (qubitBlochFidelitySq rSq x q)) ^ 2 =
        qubitBlochBuresSq rSq x q -
          mixedBuresGeneralFidelityDefect rSq x q := by
    have hF := mixedBuresGeneral_fidelity_nonnegative h
    have hsquare := Real.sq_sqrt hF
    unfold qubitBlochBuresSq mixedBuresGeneralFidelityDefect
    nlinarith
  have hraw :
      |qubitBlochBuresSq rSq x q -
          mixedBuresGeneralQuadratic rSq x q| ≤
        |x| * q / a ^ 2 + x ^ 2 * q / (4 * a ^ 3) +
          q ^ 2 / (2 * a ^ 2) := by
    rw [hdecomp]
    calc
      |(1 - Real.sqrt (qubitBlochFidelitySq rSq x q)) ^ 2 +
          mixedBuresGeneralOddTerm rSq x q| ≤
        |(1 - Real.sqrt (qubitBlochFidelitySq rSq x q)) ^ 2| +
          |mixedBuresGeneralOddTerm rSq x q| := habsSum
      _ = (1 - Real.sqrt (qubitBlochFidelitySq rSq x q)) ^ 2 +
          |mixedBuresGeneralOddTerm rSq x q| := by
        rw [abs_of_nonneg (sq_nonneg _)]
      _ ≤ q ^ 2 / (4 * a ^ 2) +
          (|x| * q / a ^ 2 + x ^ 2 * q / (4 * a ^ 3) +
            q ^ 2 / (4 * a ^ 2)) := by
        rw [houter_eq]
        exact add_le_add houter.2 hodd
      _ = |x| * q / a ^ 2 + x ^ 2 * q / (4 * a ^ 3) +
          q ^ 2 / (2 * a ^ 2) := by ring
  have hq := h.displacement_nonnegative
  have hxq0 : 0 ≤ |x| * q := mul_nonneg (abs_nonneg x) hq
  have hx2q0 : 0 ≤ x ^ 2 * q := mul_nonneg (sq_nonneg x) hq
  have hq20 : 0 ≤ q ^ 2 := sq_nonneg q
  calc
    |qubitBlochBuresSq rSq x q -
        mixedBuresGeneralQuadratic rSq x q| ≤
      |x| * q / a ^ 2 + x ^ 2 * q / (4 * a ^ 3) +
        q ^ 2 / (2 * a ^ 2) := hraw
    _ ≤ |x| * q / margin ^ 2 +
        x ^ 2 * q / margin ^ 3 + q ^ 2 / margin ^ 3 := by
      have h1 : |x| * q / a ^ 2 ≤ |x| * q / margin ^ 2 := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        simpa [one_div] using mul_le_mul_of_nonneg_left hinv2 hxq0
      have h2 : x ^ 2 * q / (4 * a ^ 3) ≤
          x ^ 2 * q / margin ^ 3 := by
        have hquarter : 1 / (4 * a ^ 3) ≤ 1 / margin ^ 3 := by
          calc
            1 / (4 * a ^ 3) ≤ 1 / a ^ 3 := by
              have ha3 : 0 ≤ a ^ 3 := (pow_pos ha 3).le
              apply (div_le_div_iff₀ (by positivity : 0 < 4 * a ^ 3)
                (pow_pos ha 3)).2
              nlinarith
            _ ≤ 1 / margin ^ 3 := hinv3
        rw [div_eq_mul_inv, div_eq_mul_inv]
        simpa [one_div] using mul_le_mul_of_nonneg_left hquarter hx2q0
      have h3 : q ^ 2 / (2 * a ^ 2) ≤ q ^ 2 / margin ^ 3 := by
        have hhalf : 1 / (2 * a ^ 2) ≤ 1 / margin ^ 3 := by
          calc
            1 / (2 * a ^ 2) ≤ 1 / a ^ 2 := by
              apply (div_le_div_iff₀ (by positivity : 0 < 2 * a ^ 2)
                (sq_pos_of_pos ha)).2
              nlinarith
            _ ≤ 1 / margin ^ 3 := hinv2_to3
        rw [div_eq_mul_inv, div_eq_mul_inv]
        simpa [one_div] using mul_le_mul_of_nonneg_left hhalf hq20
      linarith
    _ = |x| * q / margin ^ 2 +
        (x ^ 2 * q + q ^ 2) / margin ^ 3 := by ring

/-! ## Root-sample scaling -/

/-- Scalar root-sample quadratic form before substituting Bloch vectors. -/
def mixedBuresGeneralRootNQuadratic
    (rSq b c : ℝ) : ℝ :=
  (c + b ^ 2 / mixedBuresGeneralGap rSq) / 4

/-- Root-`N` scalar consequence of the full local remainder. -/
theorem qubitBlochBuresSq_general_rootN_remainder
    {N rSq b c margin : ℝ}
    (hN : 0 < N)
    (hregion : MixedBuresGeneralScalarRegion
      rSq (b / Real.sqrt N) (c / N) margin) :
    |N * qubitBlochBuresSq rSq
        (b / Real.sqrt N) (c / N) -
      mixedBuresGeneralRootNQuadratic rSq b c| ≤
      |b| * c / (margin ^ 2 * Real.sqrt N) +
        (b ^ 2 * c + c ^ 2) / (margin ^ 3 * N) := by
  have hNne : N ≠ 0 := ne_of_gt hN
  have hspos : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hsne : Real.sqrt N ≠ 0 := ne_of_gt hspos
  have hs_sq : (Real.sqrt N) ^ 2 = N := Real.sq_sqrt hN.le
  have hbase := qubitBlochBuresSq_general_margin_remainder hregion
  have hquadraticScale :
      N * mixedBuresGeneralQuadratic rSq
          (b / Real.sqrt N) (c / N) =
        mixedBuresGeneralRootNQuadratic rSq b c := by
    unfold mixedBuresGeneralQuadratic mixedBuresGeneralRootNQuadratic
    field_simp [hNne, hsne]
    rw [hs_sq]
    ring
  have habsScale :
      |N * qubitBlochBuresSq rSq
          (b / Real.sqrt N) (c / N) -
        mixedBuresGeneralRootNQuadratic rSq b c| =
      N * |qubitBlochBuresSq rSq
          (b / Real.sqrt N) (c / N) -
        mixedBuresGeneralQuadratic rSq
          (b / Real.sqrt N) (c / N)| := by
    rw [← hquadraticScale, ← mul_sub, abs_mul, abs_of_pos hN]
  rw [habsScale]
  calc
    N * |qubitBlochBuresSq rSq
        (b / Real.sqrt N) (c / N) -
      mixedBuresGeneralQuadratic rSq
        (b / Real.sqrt N) (c / N)| ≤
      N * (|b / Real.sqrt N| * (c / N) / margin ^ 2 +
        ((b / Real.sqrt N) ^ 2 * (c / N) + (c / N) ^ 2) /
          margin ^ 3) :=
      mul_le_mul_of_nonneg_left hbase hN.le
    _ = |b| * c / (margin ^ 2 * Real.sqrt N) +
        (b ^ 2 * c + c ^ 2) / (margin ^ 3 * N) := by
      have hmargin_ne : margin ≠ 0 := ne_of_gt hregion.margin_positive
      rw [abs_div, abs_of_pos hspos]
      field_simp [hNne, hsne, hmargin_ne]
      ring_nf <;> simp only [hs_sq]

/-! ## Concrete `Fin 3` mixed-qubit endpoint -/

/-- Actual full-direction root-`N` Bures loss. -/
def mixedGeneralRootNBuresLossReal
    (N : ℝ) (theta h : Fin 3 → ℝ) : ℝ :=
  N * mixedBlochBuresSq theta
    ((Real.sqrt N)⁻¹ • h)

private theorem mixedGeneralRootScale_sq
    {N : ℝ} (hN : 0 < N) :
    ((Real.sqrt N)⁻¹) ^ 2 = N⁻¹ := by
  rw [inv_pow, Real.sq_sqrt hN.le]

/-- Full general-direction physical-risk remainder on an interior one-qubit
Bloch chart.  The explicit small-radius premise guarantees
`2*|x|+q <= gap/2` after root-sample scaling. -/
theorem mixedGeneralRootNBuresLossReal_abs_remainder
    {N margin R : ℝ} {theta h : Fin 3 → ℝ}
    (hN : 0 < N)
    (hinterior : MixedQubitInteriorWithMargin margin theta)
    (hR : 0 ≤ R)
    (hradius : blochNormSq h ≤ R ^ 2)
    (hsmall :
      2 * R / Real.sqrt N + R ^ 2 / N ≤ margin / 2) :
    |mixedGeneralRootNBuresLossReal N theta h -
        mixedQubitBuresQuadraticAt theta h| ≤
      R ^ 3 / (margin ^ 2 * Real.sqrt N) +
        2 * R ^ 4 / (margin ^ 3 * N) := by
  rcases hinterior with ⟨hmargin, hmargin_one, htheta⟩
  have hNne : N ≠ 0 := ne_of_gt hN
  have hspos : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hsne : Real.sqrt N ≠ 0 := ne_of_gt hspos
  have hs_sq : (Real.sqrt N) ^ 2 = N := Real.sq_sqrt hN.le
  have htheta0 : 0 ≤ blochNormSq theta := by
    unfold blochNormSq
    positivity
  have hh0 : 0 ≤ blochNormSq h := by
    unfold blochNormSq
    positivity
  have hmargin0 : 0 ≤ margin := hmargin.le
  have hone_minus_margin : 0 ≤ 1 - margin := sub_nonneg.mpr hmargin_one
  have hmarginProduct : 0 ≤ margin * (1 - margin) :=
    mul_nonneg hmargin0 hone_minus_margin
  have hgap : margin ≤ 1 - blochNormSq theta := by
    nlinarith
  have htheta_le_one : blochNormSq theta ≤ 1 := by
    nlinarith [sq_nonneg (1 - margin)]
  have hcauchy := bloch_cauchy_schwarz theta h
  have hb_sq : (blochDot theta h) ^ 2 ≤ R ^ 2 := by
    calc
      (blochDot theta h) ^ 2 ≤
          blochNormSq theta * blochNormSq h := hcauchy
      _ ≤ 1 * R ^ 2 := by
        gcongr
      _ = R ^ 2 := one_mul _
  have hb_abs : |blochDot theta h| ≤ R := by
    apply (sq_le_sq₀ (abs_nonneg (blochDot theta h)) hR).1
    simpa only [sq_abs] using hb_sq
  have hscaledCauchy :
      (blochDot theta h / Real.sqrt N) ^ 2 ≤
        blochNormSq theta * (blochNormSq h / N) := by
    field_simp [hNne, hsne]
    nlinarith
  have hscaledLocal :
      2 * |blochDot theta h / Real.sqrt N| +
          blochNormSq h / N ≤
        (1 - blochNormSq theta) / 2 := by
    have habsScale :
        |blochDot theta h / Real.sqrt N| =
          |blochDot theta h| / Real.sqrt N := by
      rw [abs_div, abs_of_pos hspos]
    rw [habsScale]
    have hfirst :
        |blochDot theta h| / Real.sqrt N ≤ R / Real.sqrt N :=
      div_le_div_of_nonneg_right hb_abs hspos.le
    have hsecond : blochNormSq h / N ≤ R ^ 2 / N :=
      div_le_div_of_nonneg_right hradius hN.le
    calc
      2 * (|blochDot theta h| / Real.sqrt N) + blochNormSq h / N ≤
          2 * (R / Real.sqrt N) + R ^ 2 / N := by gcongr
      _ = 2 * R / Real.sqrt N + R ^ 2 / N := by ring
      _ ≤ margin / 2 := hsmall
      _ ≤ (1 - blochNormSq theta) / 2 := by linarith
  have hregion : MixedBuresGeneralScalarRegion
      (blochNormSq theta)
      (blochDot theta h / Real.sqrt N)
      (blochNormSq h / N) margin :=
    { radius_nonnegative := htheta0
      margin_positive := hmargin
      margin_le_gap := hgap
      displacement_nonnegative := div_nonneg hh0 hN.le
      cauchy := hscaledCauchy
      local_radius := hscaledLocal }
  have hscalar := qubitBlochBuresSq_general_rootN_remainder
    hN hregion
  have hdotScale :
      blochDot theta ((Real.sqrt N)⁻¹ • h) =
        blochDot theta h / Real.sqrt N := by
    calc
      blochDot theta ((Real.sqrt N)⁻¹ • h) =
          (Real.sqrt N)⁻¹ * blochDot theta h := by
        unfold blochDot
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      _ = blochDot theta h / Real.sqrt N := by
        rw [div_eq_mul_inv]
        ring
  have hnormScale :
      blochNormSq ((Real.sqrt N)⁻¹ • h) =
        blochNormSq h / N := by
    rw [blochNormSq_smul, mixedGeneralRootScale_sq hN]
    ring
  have hquadratic :
      mixedQubitBuresQuadraticAt theta h =
        mixedBuresGeneralRootNQuadratic
          (blochNormSq theta) (blochDot theta h) (blochNormSq h) := by
    rfl
  have hphysical :
      mixedGeneralRootNBuresLossReal N theta h =
        N * qubitBlochBuresSq (blochNormSq theta)
          (blochDot theta h / Real.sqrt N) (blochNormSq h / N) := by
    simp [mixedGeneralRootNBuresLossReal, mixedBlochBuresSq,
      hdotScale, hnormScale]
  have hscaled :
      |mixedGeneralRootNBuresLossReal N theta h -
          mixedQubitBuresQuadraticAt theta h| ≤
        |blochDot theta h| * blochNormSq h /
            (margin ^ 2 * Real.sqrt N) +
          ((blochDot theta h) ^ 2 * blochNormSq h +
            (blochNormSq h) ^ 2) / (margin ^ 3 * N) := by
    rw [hphysical, hquadratic]
    exact hscalar
  have hcubic :
      |blochDot theta h| * blochNormSq h ≤ R ^ 3 := by
    calc
      |blochDot theta h| * blochNormSq h ≤
          R * blochNormSq h :=
        mul_le_mul_of_nonneg_right hb_abs hh0
      _ ≤ R * R ^ 2 := mul_le_mul_of_nonneg_left hradius hR
      _ = R ^ 3 := by ring
  have hbsqR : (blochDot theta h) ^ 2 ≤ R ^ 2 := hb_sq
  have hquarticOne :
      (blochDot theta h) ^ 2 * blochNormSq h ≤ R ^ 4 := by
    calc
      (blochDot theta h) ^ 2 * blochNormSq h ≤
          R ^ 2 * R ^ 2 := by gcongr
      _ = R ^ 4 := by ring
  have hquarticTwo : (blochNormSq h) ^ 2 ≤ R ^ 4 := by
    have hmul :
        0 ≤ (R ^ 2 - blochNormSq h) *
          (R ^ 2 + blochNormSq h) :=
      mul_nonneg (sub_nonneg.mpr hradius)
        (add_nonneg (sq_nonneg R) hh0)
    nlinarith
  have hquartic :
      (blochDot theta h) ^ 2 * blochNormSq h +
          (blochNormSq h) ^ 2 ≤ 2 * R ^ 4 := by
    linarith
  have hcubicDen : 0 < margin ^ 2 * Real.sqrt N := by positivity
  have hquarticDen : 0 < margin ^ 3 * N := by positivity
  calc
    |mixedGeneralRootNBuresLossReal N theta h -
        mixedQubitBuresQuadraticAt theta h| ≤
      |blochDot theta h| * blochNormSq h /
          (margin ^ 2 * Real.sqrt N) +
        ((blochDot theta h) ^ 2 * blochNormSq h +
          (blochNormSq h) ^ 2) / (margin ^ 3 * N) := hscaled
    _ ≤ R ^ 3 / (margin ^ 2 * Real.sqrt N) +
        2 * R ^ 4 / (margin ^ 3 * N) := by
      exact add_le_add
        (div_le_div_of_nonneg_right hcubic hcubicDen.le)
        (div_le_div_of_nonneg_right hquartic hquarticDen.le)

end

end QubitOracle.Paper
