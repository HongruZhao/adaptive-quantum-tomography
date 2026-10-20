import QubitOracle.Paper.OneQubitBuresRiskRemainder

/-!
# A correct interior mixed-qubit Bures remainder

The raw Bloch-coordinate Bures expansion has a sign-changing cubic term at a
nonzero mixed-state truth.  This file therefore does not reuse the false global
one-sided comparison between physical and quadratic loss.

We close the strongest elementary slice on which that cubic term vanishes:
local perturbations `h` satisfying `blochDot theta h = 0`.  For every interior
truth with radial margin `margin`, and every root-sample perturbation inside the
explicit radius condition, the exact qubit fidelity formula gives

`0 <= N * Bures(theta, theta + h/sqrt N) - Q_theta(h)`

and

`N * Bures(theta, theta + h/sqrt N) - Q_theta(h)
    <= (1/(4*margin) + 1/4) * (blochNormSq h)^2 / N`.

Thus this tangential result is stronger than a cubic-plus-quartic absolute
bound: its cubic constant is zero.  A symmetric ENNReal integration lemma and
a concrete fourth-moment risk bound are included below.

The unresolved general-direction theorem is stated only in this documentation:
one must retain `x = blochDot theta h / sqrt N` and bound the sign-changing
cubic part of the exact nested-square-root formula.  No theorem below assumes
that missing Taylor estimate.
-/

namespace QubitOracle
namespace Paper

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory

/-- Explicit fourth-order constant for a tangential perturbation at radial
margin `margin`. -/
def mixedTangentialBuresRemainderConstant (margin : ℝ) : ℝ :=
  1 / (4 * margin) + 1 / 4

/-- The scalar exact-formula remainder when the radial displacement `x` is
zero.  The proof uses only the definitions of `qubitBlochFidelitySq` and
`qubitBlochBuresSq`, square-root identities, and ordered-field algebra. -/
theorem qubitBlochBuresSq_tangential_remainder
    (rSq q margin : ℝ)
    (hrSq : 0 ≤ rSq)
    (hmargin : 0 < margin)
    (hgap : margin ≤ 1 - rSq)
    (hq : 0 ≤ q)
    (hlocal : q ≤ 1 - rSq) :
    0 ≤ qubitBlochBuresSq rSq 0 q - q / 4 ∧
    qubitBlochBuresSq rSq 0 q - q / 4 ≤
      q ^ 2 * mixedTangentialBuresRemainderConstant margin := by
  let a : ℝ := 1 - rSq
  let t : ℝ := Real.sqrt (a * (a - q))
  let F : ℝ := qubitBlochFidelitySq rSq 0 q
  let s : ℝ := Real.sqrt F
  let w : ℝ := 1 - F
  let m : ℝ := a - q / 2
  have ha : 0 < a := by
    dsimp [a]
    linarith
  have haq : 0 ≤ a - q := by
    dsimp [a]
    linarith
  have hab : 0 ≤ a * (a - q) := mul_nonneg ha.le haq
  have ht : 0 ≤ t := by
    dsimp [t]
    exact Real.sqrt_nonneg _
  have ht_sq : t ^ 2 = a * (a - q) := by
    dsimp [t]
    exact Real.sq_sqrt hab
  have ht_le_a : t ≤ a := by
    have ht_sq_le : t ^ 2 ≤ a ^ 2 := by
      rw [ht_sq]
      nlinarith [mul_nonneg ha.le hq]
    by_contra hnot
    have hat : a < t := lt_of_not_ge hnot
    have hsum : 0 < t + a := by linarith
    have hpositive : 0 < (t - a) * (t + a) :=
      mul_pos (sub_pos.mpr hat) hsum
    nlinarith
  have hm : 0 ≤ m := by
    dsimp [m]
    nlinarith
  have hmid_product : (m - t) * (m + t) = q ^ 2 / 4 := by
    dsimp [m]
    calc
      (a - q / 2 - t) * (a - q / 2 + t) =
          (a - q / 2) ^ 2 - t ^ 2 := by ring
      _ = q ^ 2 / 4 := by
        rw [ht_sq]
        ring
  have ht_le_m : t ≤ m := by
    by_contra hnot
    have hmt : m < t := lt_of_not_ge hnot
    have hsum : 0 < m + t := by linarith
    have hnegative : (m - t) * (m + t) < 0 :=
      mul_neg_of_neg_of_pos (sub_neg.mpr hmt) hsum
    rw [hmid_product] at hnegative
    nlinarith [sq_nonneg q]
  have ht_lower : a - q ≤ t := by
    have hlower : 0 ≤ a - q := haq
    have hproduct :
        (t - (a - q)) * (t + (a - q)) = q * (a - q) := by
      calc
        (t - (a - q)) * (t + (a - q)) =
            t ^ 2 - (a - q) ^ 2 := by ring
        _ = q * (a - q) := by
          rw [ht_sq]
          ring
    by_contra hnot
    have hta : t < a - q := lt_of_not_ge hnot
    have hsum : 0 < t + (a - q) := by linarith
    have hnegative :
        (t - (a - q)) * (t + (a - q)) < 0 :=
      mul_neg_of_neg_of_pos (sub_neg.mpr hta) hsum
    rw [hproduct] at hnegative
    have hnonnegative : 0 ≤ q * (a - q) :=
      mul_nonneg hq hlower
    linarith
  have hF_def : F = (1 + rSq + t) / 2 := by
    simp [F, qubitBlochFidelitySq, t, a]
  have hF_nonneg : 0 ≤ F := by
    rw [hF_def]
    nlinarith
  have hF_le_one : F ≤ 1 := by
    rw [hF_def]
    dsimp [a] at ht_le_a
    nlinarith
  have hs : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = F := by
    dsimp [s]
    exact Real.sq_sqrt hF_nonneg
  have hs_le_one : s ≤ 1 := by
    by_contra hnot
    have hone : 1 < s := lt_of_not_ge hnot
    nlinarith
  have hw_def : w = (a - t) / 2 := by
    dsimp [w]
    rw [hF_def]
    dsimp [a]
    ring
  have hw_nonneg : 0 ≤ w := by
    rw [hw_def]
    linarith
  have hw_lower : q / 4 ≤ w := by
    rw [hw_def]
    dsimp [m] at ht_le_m
    linarith
  have hw_upper : w ≤ q / 2 := by
    rw [hw_def]
    linarith
  have hm_minus_t_nonneg : 0 ≤ m - t := sub_nonneg.mpr ht_le_m
  have hdenominator_lower : a / 2 ≤ m + t := by
    dsimp [m]
    nlinarith
  have hproduct_bound : (m - t) * (a / 2) ≤ q ^ 2 / 4 := by
    calc
      (m - t) * (a / 2) ≤ (m - t) * (m + t) :=
        mul_le_mul_of_nonneg_left hdenominator_lower hm_minus_t_nonneg
      _ = q ^ 2 / 4 := hmid_product
  have hmid_remainder : (m - t) / 2 ≤ (q ^ 2 / 4) / a := by
    apply (le_div_iff₀ ha).2
    nlinarith
  have hw_remainder : w - q / 4 ≤ q ^ 2 / (4 * a) := by
    calc
      w - q / 4 = (m - t) / 2 := by
        rw [hw_def]
        dsimp [m]
        ring
      _ ≤ (q ^ 2 / 4) / a := hmid_remainder
      _ = q ^ 2 / (4 * a) := by
        field_simp [ha.ne']
  have hw_s : w = 1 - s ^ 2 := by
    dsimp [w]
    rw [hs_sq]
  have hB_def : qubitBlochBuresSq rSq 0 q = 2 * (1 - s) := by
    simp [qubitBlochBuresSq, s, F]
  have hB_minus_w :
      qubitBlochBuresSq rSq 0 q - w = (1 - s) ^ 2 := by
    rw [hB_def, hw_s]
    ring
  have hone_minus_s_nonneg : 0 ≤ 1 - s := sub_nonneg.mpr hs_le_one
  have hone_minus_s_le_w : 1 - s ≤ w := by
    have hmul : 0 ≤ s * (1 - s) :=
      mul_nonneg hs hone_minus_s_nonneg
    rw [hw_s]
    nlinarith
  have hone_minus_s_sq_le : (1 - s) ^ 2 ≤ w ^ 2 := by
    have hmul : 0 ≤ (w - (1 - s)) * (w + (1 - s)) :=
      mul_nonneg (sub_nonneg.mpr hone_minus_s_le_w)
        (add_nonneg hw_nonneg hone_minus_s_nonneg)
    nlinarith
  have hw_sq_le : w ^ 2 ≤ q ^ 2 / 4 := by
    have hhalf_nonneg : 0 ≤ q / 2 := by positivity
    have hmul : 0 ≤ (q / 2 - w) * (q / 2 + w) :=
      mul_nonneg (sub_nonneg.mpr hw_upper)
        (add_nonneg hhalf_nonneg hw_nonneg)
    nlinarith
  have hroot_remainder_nonneg :
      0 ≤ qubitBlochBuresSq rSq 0 q - w := by
    rw [hB_minus_w]
    positivity
  have hroot_remainder_upper :
      qubitBlochBuresSq rSq 0 q - w ≤ q ^ 2 / 4 := by
    rw [hB_minus_w]
    exact hone_minus_s_sq_le.trans hw_sq_le
  have hquadratic_remainder_nonneg : 0 ≤ w - q / 4 := by
    linarith
  have hdenominator_order : 4 * margin ≤ 4 * a := by
    dsimp [a]
    linarith
  have hinverse_order : 1 / (4 * a) ≤ 1 / (4 * margin) :=
    one_div_le_one_div_of_le (by positivity) hdenominator_order
  constructor
  · calc
      0 ≤ (qubitBlochBuresSq rSq 0 q - w) + (w - q / 4) :=
        add_nonneg hroot_remainder_nonneg hquadratic_remainder_nonneg
      _ = qubitBlochBuresSq rSq 0 q - q / 4 := by ring
  · calc
      qubitBlochBuresSq rSq 0 q - q / 4 =
          (qubitBlochBuresSq rSq 0 q - w) + (w - q / 4) := by
            ring
      _ ≤ q ^ 2 / 4 + q ^ 2 / (4 * a) :=
        add_le_add hroot_remainder_upper hw_remainder
      _ = q ^ 2 * (1 / 4 + 1 / (4 * a)) := by ring
      _ ≤ q ^ 2 * (1 / 4 + 1 / (4 * margin)) := by
        gcongr
      _ = q ^ 2 * mixedTangentialBuresRemainderConstant margin := by
        unfold mixedTangentialBuresRemainderConstant
        ring

/-- Root-`N` scalar version.  Here `c` is the squared norm of the unscaled
local perturbation. -/
theorem qubitBlochBuresSq_tangential_rootN_remainder
    (N rSq c margin : ℝ)
    (hN : 0 < N)
    (hrSq : 0 ≤ rSq)
    (hmargin : 0 < margin)
    (hgap : margin ≤ 1 - rSq)
    (hc : 0 ≤ c)
    (hlocal : c ≤ N * (1 - rSq)) :
    0 ≤ N * qubitBlochBuresSq rSq 0 (c / N) - c / 4 ∧
    N * qubitBlochBuresSq rSq 0 (c / N) - c / 4 ≤
      c ^ 2 / N * mixedTangentialBuresRemainderConstant margin := by
  have hNne : N ≠ 0 := ne_of_gt hN
  have hq : 0 ≤ c / N := div_nonneg hc hN.le
  have hqlocal : c / N ≤ 1 - rSq :=
    (div_le_iff₀ hN).2 (by simpa [mul_comm] using hlocal)
  have hb := qubitBlochBuresSq_tangential_remainder
    rSq (c / N) margin hrSq hmargin hgap hq hqlocal
  constructor
  · calc
      N * qubitBlochBuresSq rSq 0 (c / N) - c / 4 =
          N * (qubitBlochBuresSq rSq 0 (c / N) - (c / N) / 4) := by
            field_simp [hNne]
      _ ≥ 0 := mul_nonneg hN.le hb.1
  · calc
      N * qubitBlochBuresSq rSq 0 (c / N) - c / 4 =
          N * (qubitBlochBuresSq rSq 0 (c / N) - (c / N) / 4) := by
            field_simp [hNne]
      _ ≤ N * ((c / N) ^ 2 *
          mixedTangentialBuresRemainderConstant margin) :=
        mul_le_mul_of_nonneg_left hb.2 hN.le
      _ = c ^ 2 / N * mixedTangentialBuresRemainderConstant margin := by
        field_simp [hNne]

/-- Actual root-`N` mixed-qubit Bures loss for a Bloch-coordinate error. -/
def mixedTangentialRootNBuresLossReal
    (N : ℝ) (theta h : Fin 3 → ℝ) : ℝ :=
  N * mixedBlochBuresSq theta
    ((Real.sqrt N)⁻¹ • h)

private theorem mixedRootScale_sq
    {N : ℝ} (hN : 0 < N) :
    ((Real.sqrt N)⁻¹) ^ 2 = N⁻¹ := by
  rw [inv_pow, Real.sq_sqrt hN.le]

/-- A `Fin 3` tangential perturbation obeys the explicit fourth-order
root-sample Bures remainder.  The radius premise ensures that the displaced
Bloch vector remains physical. -/
theorem mixedTangentialRootNBuresLossReal_remainder_bounds
    {N margin R : ℝ} {theta h : Fin 3 → ℝ}
    (hN : 0 < N)
    (hinterior : MixedQubitInteriorWithMargin margin theta)
    (hR : 0 ≤ R)
    (hradius : blochNormSq h ≤ R ^ 2)
    (hNradius : R ^ 2 ≤ N * margin)
    (htangent : blochDot theta h = 0) :
    0 ≤ mixedTangentialRootNBuresLossReal N theta h -
        mixedQubitBuresQuadraticAt theta h ∧
    mixedTangentialRootNBuresLossReal N theta h -
        mixedQubitBuresQuadraticAt theta h ≤
      (blochNormSq h) ^ 2 / N *
        mixedTangentialBuresRemainderConstant margin := by
  rcases hinterior with ⟨hmargin, hmargin_one, htheta⟩
  have hmargin_nonneg : 0 ≤ margin := hmargin.le
  have hone_minus_margin : 0 ≤ 1 - margin := sub_nonneg.mpr hmargin_one
  have hmargin_product : 0 ≤ margin * (1 - margin) :=
    mul_nonneg hmargin_nonneg hone_minus_margin
  have hsquare_le : (1 - margin) ^ 2 ≤ 1 - margin := by
    nlinarith
  have hgap : margin ≤ 1 - blochNormSq theta := by
    nlinarith
  have htheta_nonneg : 0 ≤ blochNormSq theta := by
    unfold blochNormSq
    positivity
  have hh_nonneg : 0 ≤ blochNormSq h := by
    unfold blochNormSq
    positivity
  have hlocal : blochNormSq h ≤ N * (1 - blochNormSq theta) := by
    calc
      blochNormSq h ≤ R ^ 2 := hradius
      _ ≤ N * margin := hNradius
      _ ≤ N * (1 - blochNormSq theta) :=
        mul_le_mul_of_nonneg_left hgap hN.le
  have hdot_scale :
      blochDot theta ((Real.sqrt N)⁻¹ • h) = 0 := by
    calc
      blochDot theta ((Real.sqrt N)⁻¹ • h) =
          (Real.sqrt N)⁻¹ * blochDot theta h := by
        unfold blochDot
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      _ = 0 := by rw [htangent, mul_zero]
  have hnorm_scale :
      blochNormSq ((Real.sqrt N)⁻¹ • h) =
        blochNormSq h / N := by
    rw [blochNormSq_smul, mixedRootScale_sq hN]
    ring
  have hscalar := qubitBlochBuresSq_tangential_rootN_remainder
    N (blochNormSq theta) (blochNormSq h) margin hN
    htheta_nonneg hmargin hgap hh_nonneg hlocal
  simpa [mixedTangentialRootNBuresLossReal, mixedBlochBuresSq,
    hdot_scale, hnorm_scale, mixedQubitBuresQuadraticAt, htangent,
    div_eq_mul_inv, mul_comm] using hscalar

/-- Absolute-value form of the concrete tangential bound.  Its cubic constant
is exactly zero. -/
theorem mixedTangentialRootNBuresLossReal_abs_remainder
    {N margin R : ℝ} {theta h : Fin 3 → ℝ}
    (hN : 0 < N)
    (hinterior : MixedQubitInteriorWithMargin margin theta)
    (hR : 0 ≤ R)
    (hradius : blochNormSq h ≤ R ^ 2)
    (hNradius : R ^ 2 ≤ N * margin)
    (htangent : blochDot theta h = 0) :
    |mixedTangentialRootNBuresLossReal N theta h -
        mixedQubitBuresQuadraticAt theta h| ≤
      (blochNormSq h) ^ 2 / N *
        mixedTangentialBuresRemainderConstant margin := by
  have hb := mixedTangentialRootNBuresLossReal_remainder_bounds
    hN hinterior hR hradius hNradius htangent
  rw [abs_of_nonneg hb.1]
  exact hb.2

/-! ## Symmetric ENNReal risk transfer -/

/-- A two-sided pointwise ENNReal envelope transfers to two-sided bounds on
expectations.  Unlike the older one-sided physical-risk wrapper, this lemma is
valid for sign-changing Taylor remainders. -/
theorem lintegral_twoSidedRiskTransfer
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (physical quadratic moment : Omega → ℝ≥0∞)
    (rate C : ℝ≥0∞)
    (hphysicalMeasurable : Measurable physical)
    (hquadraticMeasurable : Measurable quadratic)
    (hmomentMeasurable : Measurable moment)
    (hpointwise : ∀ omega,
      physical omega ≤ quadratic omega + rate * moment omega ∧
      quadratic omega ≤ physical omega + rate * moment omega)
    (hmoment : (∫⁻ omega, moment omega ∂mu) ≤ C) :
    (∫⁻ omega, physical omega ∂mu) ≤
        (∫⁻ omega, quadratic omega ∂mu) + rate * C ∧
    (∫⁻ omega, quadratic omega ∂mu) ≤
        (∫⁻ omega, physical omega ∂mu) + rate * C := by
  constructor
  · calc
      (∫⁻ omega, physical omega ∂mu) ≤
          ∫⁻ omega, quadratic omega + rate * moment omega ∂mu :=
        lintegral_mono fun omega => (hpointwise omega).1
      _ = (∫⁻ omega, quadratic omega ∂mu) +
          ∫⁻ omega, rate * moment omega ∂mu := by
        rw [lintegral_add_left hquadraticMeasurable]
      _ = (∫⁻ omega, quadratic omega ∂mu) +
          rate * ∫⁻ omega, moment omega ∂mu := by
        rw [lintegral_const_mul rate hmomentMeasurable]
      _ ≤ (∫⁻ omega, quadratic omega ∂mu) + rate * C := by
        gcongr
  · calc
      (∫⁻ omega, quadratic omega ∂mu) ≤
          ∫⁻ omega, physical omega + rate * moment omega ∂mu :=
        lintegral_mono fun omega => (hpointwise omega).2
      _ = (∫⁻ omega, physical omega ∂mu) +
          ∫⁻ omega, rate * moment omega ∂mu := by
        rw [lintegral_add_left hphysicalMeasurable]
      _ = (∫⁻ omega, physical omega ∂mu) +
          rate * ∫⁻ omega, moment omega ∂mu := by
        rw [lintegral_const_mul rate hmomentMeasurable]
      _ ≤ (∫⁻ omega, physical omega ∂mu) + rate * C := by
        gcongr

/-- ENNReal physical loss associated with the concrete tangential chart. -/
def mixedTangentialRootNBuresLossENNReal
    (N : ℝ) (theta h : Fin 3 → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (mixedTangentialRootNBuresLossReal N theta h)

/-- ENNReal quadratic loss at the mixed-state truth. -/
def mixedBuresQuadraticLossENNReal
    (theta h : Fin 3 → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (mixedQubitBuresQuadraticAt theta h)

/-- Fourth envelope used by the tangential risk transfer. -/
def mixedTangentialFourthEnvelope
    (h : Fin 3 → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((blochNormSq h) ^ 2)

/-- The explicit fixed-`N` ENNReal rate. -/
def mixedTangentialBuresRemainderRate
    (N margin : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (mixedTangentialBuresRemainderConstant margin / N)

/-- Pointwise ENNReal form of the concrete tangential Taylor bound. -/
theorem mixedTangentialRootNBuresLossENNReal_bounds
    {N margin R : ℝ} {theta h : Fin 3 → ℝ}
    (hN : 0 < N)
    (hinterior : MixedQubitInteriorWithMargin margin theta)
    (hR : 0 ≤ R)
    (hradius : blochNormSq h ≤ R ^ 2)
    (hNradius : R ^ 2 ≤ N * margin)
    (htangent : blochDot theta h = 0) :
    mixedBuresQuadraticLossENNReal theta h ≤
        mixedTangentialRootNBuresLossENNReal N theta h ∧
    mixedTangentialRootNBuresLossENNReal N theta h ≤
      mixedBuresQuadraticLossENNReal theta h +
        mixedTangentialBuresRemainderRate N margin *
          mixedTangentialFourthEnvelope h := by
  have hb := mixedTangentialRootNBuresLossReal_remainder_bounds
    hN hinterior hR hradius hNradius htangent
  have hthetaInterior : blochNormSq theta < 1 := by
    have hden := mixedQubitInterior_denominator_pos hinterior
    linarith
  have hquadratic : 0 ≤ mixedQubitBuresQuadraticAt theta h :=
    mixedQubitBuresQuadraticAt_nonneg hthetaInterior
  have hconstant :
      0 ≤ mixedTangentialBuresRemainderConstant margin := by
    rcases hinterior with ⟨hmargin, _hmargin_one, _htheta⟩
    unfold mixedTangentialBuresRemainderConstant
    positivity
  have hnorm : 0 ≤ blochNormSq h := by
    unfold blochNormSq
    positivity
  have hremainder :
      0 ≤ mixedTangentialBuresRemainderConstant margin / N *
        (blochNormSq h) ^ 2 :=
    mul_nonneg (div_nonneg hconstant hN.le) (sq_nonneg _)
  have hfactor :
      ENNReal.ofReal
          (mixedTangentialBuresRemainderConstant margin / N *
            (blochNormSq h) ^ 2) =
        mixedTangentialBuresRemainderRate N margin *
          mixedTangentialFourthEnvelope h := by
    rw [ENNReal.ofReal_mul (div_nonneg hconstant hN.le)]
    rfl
  constructor
  · exact ENNReal.ofReal_le_ofReal (by linarith [hb.1])
  · have hupperReal :
        mixedTangentialRootNBuresLossReal N theta h ≤
          mixedQubitBuresQuadraticAt theta h +
            mixedTangentialBuresRemainderConstant margin / N *
              (blochNormSq h) ^ 2 := by
      have heq :
          (blochNormSq h) ^ 2 / N *
              mixedTangentialBuresRemainderConstant margin =
            mixedTangentialBuresRemainderConstant margin / N *
              (blochNormSq h) ^ 2 := by ring
      rw [← heq]
      linarith [hb.2]
    calc
      mixedTangentialRootNBuresLossENNReal N theta h ≤
          ENNReal.ofReal
            (mixedQubitBuresQuadraticAt theta h +
              mixedTangentialBuresRemainderConstant margin / N *
                (blochNormSq h) ^ 2) :=
        ENNReal.ofReal_le_ofReal hupperReal
      _ = mixedBuresQuadraticLossENNReal theta h +
          ENNReal.ofReal
            (mixedTangentialBuresRemainderConstant margin / N *
              (blochNormSq h) ^ 2) := by
        rw [ENNReal.ofReal_add hquadratic hremainder]
        rfl
      _ = mixedBuresQuadraticLossENNReal theta h +
          mixedTangentialBuresRemainderRate N margin *
            mixedTangentialFourthEnvelope h := by rw [hfactor]

/-- Concrete expected-risk transfer on the tangential interior chart.  A
uniform fourth-moment bound `C4` leaves the explicit error
`mixedTangentialBuresRemainderRate N margin * C4`. -/
theorem mixedTangentialExpectedBuresRisk_bounds
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (N margin R C4 : ℝ)
    (theta : Fin 3 → ℝ)
    (error : Omega → Fin 3 → ℝ)
    (hN : 0 < N)
    (hinterior : MixedQubitInteriorWithMargin margin theta)
    (hR : 0 ≤ R)
    (hNradius : R ^ 2 ≤ N * margin)
    (hradius : ∀ omega, blochNormSq (error omega) ≤ R ^ 2)
    (htangent : ∀ omega, blochDot theta (error omega) = 0)
    (hquadraticMeasurable : Measurable
      (fun omega => mixedBuresQuadraticLossENNReal theta (error omega)))
    (hphysicalMeasurable : Measurable
      (fun omega =>
        mixedTangentialRootNBuresLossENNReal N theta (error omega)))
    (hfourthMeasurable : Measurable
      (fun omega => mixedTangentialFourthEnvelope (error omega)))
    (hfourthMoment :
      (∫⁻ omega, mixedTangentialFourthEnvelope (error omega) ∂mu) ≤
        ENNReal.ofReal C4) :
    (∫⁻ omega, mixedBuresQuadraticLossENNReal theta (error omega) ∂mu) ≤
        ∫⁻ omega,
          mixedTangentialRootNBuresLossENNReal N theta (error omega) ∂mu ∧
    (∫⁻ omega,
        mixedTangentialRootNBuresLossENNReal N theta (error omega) ∂mu) ≤
      (∫⁻ omega,
        mixedBuresQuadraticLossENNReal theta (error omega) ∂mu) +
        mixedTangentialBuresRemainderRate N margin * ENNReal.ofReal C4 := by
  have hpointwise : ∀ omega,
      mixedBuresQuadraticLossENNReal theta (error omega) ≤
          mixedTangentialRootNBuresLossENNReal N theta (error omega) ∧
      mixedTangentialRootNBuresLossENNReal N theta (error omega) ≤
        mixedBuresQuadraticLossENNReal theta (error omega) +
          mixedTangentialBuresRemainderRate N margin *
            mixedTangentialFourthEnvelope (error omega) := by
    intro omega
    exact mixedTangentialRootNBuresLossENNReal_bounds hN hinterior hR
      (hradius omega) hNradius (htangent omega)
  constructor
  · exact lintegral_mono fun omega => (hpointwise omega).1
  · calc
      (∫⁻ omega,
          mixedTangentialRootNBuresLossENNReal N theta (error omega) ∂mu) ≤
        ∫⁻ omega,
          mixedBuresQuadraticLossENNReal theta (error omega) +
            mixedTangentialBuresRemainderRate N margin *
              mixedTangentialFourthEnvelope (error omega) ∂mu :=
        lintegral_mono fun omega => (hpointwise omega).2
      _ = (∫⁻ omega,
          mixedBuresQuadraticLossENNReal theta (error omega) ∂mu) +
          ∫⁻ omega,
            mixedTangentialBuresRemainderRate N margin *
              mixedTangentialFourthEnvelope (error omega) ∂mu := by
        rw [lintegral_add_left hquadraticMeasurable]
      _ = (∫⁻ omega,
          mixedBuresQuadraticLossENNReal theta (error omega) ∂mu) +
          mixedTangentialBuresRemainderRate N margin *
            ∫⁻ omega, mixedTangentialFourthEnvelope (error omega) ∂mu := by
        rw [lintegral_const_mul
          (mixedTangentialBuresRemainderRate N margin)
          hfourthMeasurable]
      _ ≤ (∫⁻ omega,
          mixedBuresQuadraticLossENNReal theta (error omega) ∂mu) +
          mixedTangentialBuresRemainderRate N margin *
            ENNReal.ofReal C4 := by
        gcongr

end

end Paper
end QubitOracle
