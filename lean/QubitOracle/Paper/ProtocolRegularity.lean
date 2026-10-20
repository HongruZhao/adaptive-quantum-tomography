import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.MixedAxisFisher
import QubitOracle.Paper.MixedProbabilityFloor
import QubitOracle.RankOneLosses
import QubitOracle.TwoBasis
/-! Supporting definitions and proved lemmas used by the manuscript. -/

open Filter MeasureTheory
open scoped BigOperators

namespace QubitOracle
namespace Paper

/-- The summand in the manuscript's square-root DQM defect. -/
noncomputable def finiteDQMResidual
    {Y D : Type*} [Fintype D]
    (pLocal pBase : Y -> Real) (score : Y -> D -> Real)
    (u : D -> Real) (y : Y) : Real :=
  Real.sqrt (pLocal y) - Real.sqrt (pBase y) -
    (1 / 2 : Real) * (∑ j, u j * score y j) * Real.sqrt (pBase y)

/-- Exact finite-outcome version of `D_i(u)` in the manuscript. -/
noncomputable def finiteDQMDefect
    {Y D : Type*} [Fintype Y] [Fintype D]
    (pLocal pBase : Y -> Real) (score : Y -> D -> Real)
    (u : D -> Real) : Real :=
  ∑ y, (finiteDQMResidual pLocal pBase score u y) ^ 2

theorem finiteDQMDefect_nonnegative
    {Y D : Type*} [Fintype Y] [Fintype D]
    (pLocal pBase : Y -> Real) (score : Y -> D -> Real)
    (u : D -> Real) :
    0 <= finiteDQMDefect pLocal pBase score u := by
  unfold finiteDQMDefect
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- A uniform `A/n` remainder for each square-root mass gives a per-round
`B/n^2` DQM bound, with `B = |Y| A^2`. -/
theorem finiteDQMDefect_le_card_mul_sq_div
    {Y D : Type*} [Fintype Y] [Fintype D]
    (pLocal pBase : Y -> Real) (score : Y -> D -> Real)
    (u : D -> Real) (n : Nat) (A : Real) (hA : 0 <= A)
    (hrem : ∀ y,
      |finiteDQMResidual pLocal pBase score u y| <= A / (n : Real)) :
    finiteDQMDefect pLocal pBase score u <=
      ((Fintype.card Y : Real) * A ^ 2) / (n : Real) ^ 2 := by
  unfold finiteDQMDefect
  calc
    ∑ y, (finiteDQMResidual pLocal pBase score u y) ^ 2 <=
        ∑ _y : Y, (A / (n : Real)) ^ 2 := by
      apply Finset.sum_le_sum
      intro y _
      have hquot : 0 <= A / (n : Real) :=
        div_nonneg hA (Nat.cast_nonneg n)
      have habs := hrem y
      have hsq :=
        (sq_le_sq₀
          (abs_nonneg (finiteDQMResidual pLocal pBase score u y)) hquot).2 habs
      simpa only [sq_abs] using hsq
    _ = ((Fintype.card Y : Real) * A ^ 2) / (n : Real) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

theorem tendsto_div_natCast_zero (B : Real) :
    Tendsto (fun n : Nat => B / (n : Real)) atTop (nhds 0) :=
  tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

/-- A deterministic eventual envelope tending to zero implies convergence in
measure. This is the precise probability step used after the uniform DQM
bound. -/
theorem tendstoInMeasure_of_eventually_uniform_norm_le
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (f : Nat -> Omega -> Real) (b : Nat -> Real)
    (hb : Tendsto b atTop (nhds 0))
    (hbound : ∀ᶠ n in atTop, ∀ omega, ‖f n omega‖ <= b n) :
    TendstoInMeasure mu f atTop 0 := by
  rw [tendstoInMeasure_iff_norm]
  intro epsilon hepsilon
  have hb_epsilon : ∀ᶠ n in atTop, b n < epsilon :=
    (tendsto_order.1 hb).2 epsilon hepsilon
  have heq :
      (fun n => mu {omega | epsilon <= ‖f n omega - (0 : Omega -> Real) omega‖})
        =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [hb_epsilon, hbound] with n hbn hfn
    have hempty :
        {omega | epsilon <= ‖f n omega - (0 : Omega -> Real) omega‖} = ∅ := by
      ext omega
      simp only [Set.mem_setOf_eq, Pi.zero_apply, sub_zero,
        Set.mem_empty_iff_false, iff_false]
      exact not_le_of_gt (lt_of_le_of_lt (hfn omega) hbn)
    rw [hempty, measure_empty]
  exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds



/-! ## Uniform score bounds and eventual Lindeberg vanishing -/

/-- Unified scalar score for the two binary-axis outcomes. -/
noncomputable def binaryAxisScoreByOutcome (t : Real) : BinaryOutcome -> Real
  | .plus => binaryAxisPlusScore t
  | .minus => binaryAxisMinusScore t

/-- The interior radial gap uniformly bounds both scalar outcome scores. -/
theorem binaryAxisScoreByOutcome_norm_le
    (t s : Real) (ht : |t| <= s) (hs : s < 1)
    (y : BinaryOutcome) :
    ‖binaryAxisScoreByOutcome t y‖ <= (1 - s)⁻¹ := by
  have hgap : 0 < 1 - s := by linarith
  rcases y with _ | _
  · have ht_lower : -s <= t := (abs_le.mp ht).1
    have hden : 1 - s <= 1 + t := by linarith
    have hden_pos : 0 < 1 + t := lt_of_lt_of_le hgap hden
    have hinv : (1 + t)⁻¹ <= (1 - s)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hgap hden
    simp only [binaryAxisScoreByOutcome, binaryAxisPlusScore,
      Real.norm_eq_abs]
    rw [abs_of_pos (inv_pos.mpr hden_pos)]
    exact hinv
  · have ht_upper : t <= s := (abs_le.mp ht).2
    have hden : 1 - s <= 1 - t := by linarith
    have hden_pos : 0 < 1 - t := lt_of_lt_of_le hgap hden
    have hinv : (1 - t)⁻¹ <= (1 - s)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hgap hden
    simp only [binaryAxisScoreByOutcome, binaryAxisMinusScore,
      Real.norm_eq_abs, abs_neg]
    rw [abs_of_pos (inv_pos.mpr hden_pos)]
    exact hinv




/-- Three-dimensional Bloch score vector for one binary-axis outcome. -/
noncomputable def mixedAxisScoreVector
    (t : Real) (axis : Fin 3 -> Real) (y : BinaryOutcome) :
    EuclideanSpace Real (Fin 3) :=
  WithLp.toLp 2 (fun j => binaryAxisScoreByOutcome t y * axis j)

theorem mixedAxisScoreVector_norm_sq
    (t : Real) (axis : Fin 3 -> Real) (y : BinaryOutcome) :
    ‖mixedAxisScoreVector t axis y‖ ^ 2 =
      (binaryAxisScoreByOutcome t y) ^ 2 * blochNormSq axis := by
  rw [EuclideanSpace.norm_sq_eq]
  unfold mixedAxisScoreVector
  simp only [WithLp.ofLp_toLp, Real.norm_eq_abs]
  calc
    ∑ i, |binaryAxisScoreByOutcome t y * axis i| ^ 2 =
        ∑ i, (binaryAxisScoreByOutcome t y) ^ 2 * (axis i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul, mul_pow, sq_abs, sq_abs]
    _ = (binaryAxisScoreByOutcome t y) ^ 2 *
        ∑ i, (axis i) ^ 2 := by
      rw [Finset.mul_sum]
    _ = (binaryAxisScoreByOutcome t y) ^ 2 * blochNormSq axis := rfl

theorem mixedAxisScoreVector_norm_le
    (t s : Real) (axis : Fin 3 -> Real)
    (ht : |t| <= s) (hs : s < 1)
    (haxis : blochNormSq axis <= 1) (y : BinaryOutcome) :
    ‖mixedAxisScoreVector t axis y‖ <= (1 - s)⁻¹ := by
  have hgap : 0 < 1 - s := by linarith
  have hK : 0 <= (1 - s)⁻¹ := (inv_pos.mpr hgap).le
  have hscalar := binaryAxisScoreByOutcome_norm_le t s ht hs y
  have hscalar_sq :
      ‖binaryAxisScoreByOutcome t y‖ ^ 2 <= ((1 - s)⁻¹) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hK).2 hscalar
  have hvector_sq :
      ‖mixedAxisScoreVector t axis y‖ ^ 2 <= ((1 - s)⁻¹) ^ 2 := by
    rw [mixedAxisScoreVector_norm_sq]
    calc
      (binaryAxisScoreByOutcome t y) ^ 2 * blochNormSq axis <=
          (binaryAxisScoreByOutcome t y) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left haxis (sq_nonneg _)
      _ = (binaryAxisScoreByOutcome t y) ^ 2 := by ring
      _ = ‖binaryAxisScoreByOutcome t y‖ ^ 2 := by
        rw [Real.norm_eq_abs, sq_abs]
      _ <= ((1 - s)⁻¹) ^ 2 := hscalar_sq
  exact (sq_le_sq₀ (norm_nonneg _) hK).1 hvector_sq


/-! ## Interior mixed-qubit probability floor -/

theorem protocol_blochNormSq_nonnegative (theta : Fin 3 -> Real) :
    0 <= blochNormSq theta := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Euclidean Bloch norm in the coordinates used by the manuscript. -/
noncomputable def blochNorm (theta : Fin 3 -> Real) : Real :=
  Real.sqrt (blochNormSq theta)

theorem blochNorm_nonnegative (theta : Fin 3 -> Real) :
    0 <= blochNorm theta :=
  Real.sqrt_nonneg _

theorem blochNorm_sq (theta : Fin 3 -> Real) :
    (blochNorm theta) ^ 2 = blochNormSq theta := by
  exact Real.sq_sqrt (protocol_blochNormSq_nonnegative theta)

/-- A projective axis of squared norm at most one has Bloch projection at
most the radial norm of the state. -/
theorem abs_blochDot_le_blochNorm
    (theta axis : Fin 3 -> Real)
    (haxis : blochNormSq axis <= 1) :
    |blochDot theta axis| <= blochNorm theta := by
  have htheta : 0 <= blochNormSq theta :=
    protocol_blochNormSq_nonnegative theta
  have hdot :
      (blochDot theta axis) ^ 2 <= blochNormSq theta := by
    calc
      (blochDot theta axis) ^ 2 <=
          blochNormSq theta * blochNormSq axis :=
        bloch_cauchy_schwarz theta axis
      _ <= blochNormSq theta * 1 :=
        mul_le_mul_of_nonneg_left haxis htheta
      _ = blochNormSq theta := by ring
  apply (sq_le_sq₀ (abs_nonneg _) (blochNorm_nonnegative theta)).1
  simpa only [sq_abs, blochNorm_sq] using hdot

theorem blochNorm_lt_one_of_normSq_lt_one
    (theta : Fin 3 -> Real) (htheta : blochNormSq theta < 1) :
    blochNorm theta < 1 := by
  have hsqrt := blochNorm_nonnegative theta
  have hsq := blochNorm_sq theta
  nlinarith

/-- Exact mixed-protocol probability floor at an interior truth. -/
theorem mixedProjectiveBornProbability_floor
    (theta axis : Fin 3 -> Real)
    (haxis : blochNormSq axis <= 1) (y : BinaryOutcome) :
    (1 - blochNorm theta) / 2 <=
      binaryBornProbability (blochDot theta axis) y :=
  binaryBornProbability_lower_bound
    (blochDot theta axis) (blochNorm theta)
      (abs_blochDot_le_blochNorm theta axis haxis) y

theorem mixedProjectiveBornProbability_pos
    (theta axis : Fin 3 -> Real)
    (htheta : blochNormSq theta < 1)
    (haxis : blochNormSq axis <= 1) (y : BinaryOutcome) :
    0 < binaryBornProbability (blochDot theta axis) y :=
  binaryBornProbability_pos
    (blochDot theta axis) (blochNorm theta)
      (abs_blochDot_le_blochNorm theta axis haxis)
      (blochNorm_lt_one_of_normSq_lt_one theta htheta) y


/-! ## Rank-one compact-local Bures control -/

theorem protocol_tangentRadiusSq_nonnegative
    {d : Nat} (h : TangentIndex d -> Real) :
    0 <= tangentRadiusSq h := by
  unfold tangentRadiusSq
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _



end Paper
end QubitOracle
