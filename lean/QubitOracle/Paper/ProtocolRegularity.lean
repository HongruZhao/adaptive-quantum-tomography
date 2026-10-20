import QubitOracle.Paper.AdaptiveConditions
import QubitOracle.Paper.AdaptiveLANTaylor
import QubitOracle.Paper.SequentialMartingale
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.MixedProbabilityFloor
import QubitOracle.Paper.MixedAxisFisher
import QubitOracle.Paper.PureBuresLocal
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Regular-round DQM arithmetic for the proposed adaptive protocols

This module isolates the deterministic part of the manuscript's protocol
verification. A uniform Taylor remainder for each square-root Born mass is
converted into the displayed per-round DQM rate. The rate is then summed and
converted into convergence in probability. No derivative bound for a
specific controller is assumed silently: it remains an explicit premise.
-/

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

/-- The displayed `B/n^2` per-round rate, together with at most `n` regular
rounds, yields the manuscript's S-DQM convergence in probability. -/
theorem protocolDQMRate_tendstoInMeasure
    {Omega I : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (rounds : Nat -> Finset I)
    (defect : Nat -> Omega -> I -> Real) (B : Real)
    (hB : 0 <= B)
    (hcard : ∀ n, (rounds n).card <= n)
    (hnonnegative : ∀ n omega i, i ∈ rounds n -> 0 <= defect n omega i)
    (hrate : ∀ n, 0 < n -> ∀ omega i, i ∈ rounds n ->
      defect n omega i <= B / (n : Real) ^ 2) :
    TendstoInMeasure mu
      (fun n omega => ∑ i ∈ rounds n, defect n omega i) atTop 0 := by
  apply tendstoInMeasure_of_eventually_uniform_norm_le
    mu (fun n omega => ∑ i ∈ rounds n, defect n omega i)
      (fun n => B / (n : Real)) (tendsto_div_natCast_zero B)
  filter_upwards [eventually_ge_atTop (1 : Nat)] with n hn
  have hnpos : 0 < n := by omega
  intro omega
  have hsum_nonnegative :
      0 <= ∑ i ∈ rounds n, defect n omega i :=
    Finset.sum_nonneg fun i hi => hnonnegative n omega i hi
  rw [Real.norm_eq_abs, abs_of_nonneg hsum_nonnegative]
  exact sum_per_round_dqm_defect_le
    (rounds n) (defect n omega) n B hnpos (hcard n) hB
      (hrate n hnpos omega)

/-- Differentiating normalization of the finite Born masses gives the regular
weighted score-centering identity. -/
theorem protocolRegularScore_centered
    {Theta M Y D : Type*} [Fintype Y]
    (model : FiniteScoreModel Theta M Y D)
    (theta : Theta) (m : M) (regularWeight : Real) :
    finiteOutcomeExpectation model.outcome theta m
      (fun y => regularWeight • model.score theta m y) = 0 :=
  finiteOutcomeExpectation_weightedScore_eq_zero
    model theta m regularWeight

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

/-- Uniformly bounded scores make every finite conditional tail moment
eventually exactly zero. -/
theorem finiteTailScoreMoment_eventually_zero_of_uniform_bound
    {Y E : Type*} [Fintype Y] [Norm E]
    (mass : Y -> Real) (score : Y -> E) (K epsilon : Real)
    (hscore : ∀ y, ‖score y‖ <= K) (hepsilon : 0 < epsilon) :
    ∀ᶠ n : Nat in atTop,
      finiteTailScoreMoment mass score epsilon n = 0 := by
  have hsqrt :
      Tendsto (fun n : Nat => Real.sqrt (n : Real)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hscaled :
      Tendsto (fun n : Nat => epsilon * Real.sqrt (n : Real)) atTop atTop :=
    hsqrt.const_mul_atTop hepsilon
  filter_upwards [(tendsto_atTop.1 hscaled) K] with n hn
  apply finiteTailScoreMoment_eq_zero_of_bounded
  intro y
  exact (hscore y).trans hn

/-- Uniform boundedness over every regular round makes the complete finite
martingale Lindeberg sum eventually exactly zero. -/
theorem finiteMartingaleLindeberg_eventually_zero_of_uniform_bound
    {I Y E : Type*} [Fintype Y] [Norm E]
    (rounds : Nat -> Finset I)
    (mass : I -> Y -> Real) (score : I -> Y -> E)
    (regularWeight : I -> Real) (K epsilon : Real)
    (hscore : ∀ i y, ‖score i y‖ <= K) (hepsilon : 0 < epsilon) :
    ∀ᶠ n : Nat in atTop,
      finiteMartingaleLindebergSum (rounds n) regularWeight
        (fun i => finiteTailScoreMoment (mass i) (score i) epsilon n) n = 0 := by
  have hsqrt :
      Tendsto (fun n : Nat => Real.sqrt (n : Real)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hscaled :
      Tendsto (fun n : Nat => epsilon * Real.sqrt (n : Real)) atTop atTop :=
    hsqrt.const_mul_atTop hepsilon
  filter_upwards [(tendsto_atTop.1 hscaled) K] with n hn
  apply finiteMartingaleLindebergSum_eq_zero
  intro i _
  apply finiteTailScoreMoment_eq_zero_of_bounded
  intro y
  exact (hscore i y).trans hn

/-- Mixed binary-axis projected scores satisfy eventual Lindeberg uniformly
over any adaptive collection whose Bloch projections stay in `[-s,s]`. -/
theorem mixedBinaryAxisLindeberg_eventually_zero
    {I : Type*} (rounds : Nat -> Finset I)
    (mass : I -> BinaryOutcome -> Real) (projection : I -> Real)
    (regularWeight : I -> Real) (s epsilon : Real)
    (hs : s < 1) (hprojection : ∀ i, |projection i| <= s)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ n : Nat in atTop,
      finiteMartingaleLindebergSum (rounds n) regularWeight
        (fun i => finiteTailScoreMoment (mass i)
          (binaryAxisScoreByOutcome (projection i)) epsilon n) n = 0 :=
  finiteMartingaleLindeberg_eventually_zero_of_uniform_bound
    rounds mass (fun i => binaryAxisScoreByOutcome (projection i))
      regularWeight (1 - s)⁻¹ epsilon
      (fun i y => binaryAxisScoreByOutcome_norm_le
        (projection i) s (hprojection i) hs y)
      hepsilon

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

/-- Full three-dimensional mixed-axis score arrays have eventually zero
Lindeberg sum under the uniform interior radial margin. -/
theorem mixedAxisVectorLindeberg_eventually_zero
    {I : Type*} (rounds : Nat -> Finset I)
    (mass : I -> BinaryOutcome -> Real)
    (projection : I -> Real) (axis : I -> Fin 3 -> Real)
    (regularWeight : I -> Real) (s epsilon : Real)
    (hs : s < 1) (hprojection : ∀ i, |projection i| <= s)
    (haxis : ∀ i, blochNormSq (axis i) <= 1)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ n : Nat in atTop,
      finiteMartingaleLindebergSum (rounds n) regularWeight
        (fun i => finiteTailScoreMoment (mass i)
          (fun y => mixedAxisScoreVector (projection i) (axis i) y)
          epsilon n) n = 0 :=
  finiteMartingaleLindeberg_eventually_zero_of_uniform_bound
    rounds mass
      (fun i y => mixedAxisScoreVector (projection i) (axis i) y)
      regularWeight (1 - s)⁻¹ epsilon
      (fun i y => mixedAxisScoreVector_norm_le
        (projection i) s (axis i) (hprojection i) hs (haxis i) y)
      hepsilon

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

/-- The actual interior mixed-qubit binary protocol satisfies the
three-dimensional martingale Lindeberg condition for every predictable
sequence of projective axes. -/
theorem mixedProtocolVectorLindeberg_eventually_zero
    {I : Type*} (rounds : Nat -> Finset I)
    (theta : Fin 3 -> Real) (axis : I -> Fin 3 -> Real)
    (regularWeight : I -> Real) (epsilon : Real)
    (hinterior : blochNormSq theta < 1)
    (haxis : ∀ i, blochNormSq (axis i) <= 1)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ n : Nat in atTop,
      finiteMartingaleLindebergSum (rounds n) regularWeight
        (fun i => finiteTailScoreMoment
          (fun y => binaryBornProbability (blochDot theta (axis i)) y)
          (fun y => mixedAxisScoreVector
            (blochDot theta (axis i)) (axis i) y)
          epsilon n) n = 0 :=
  mixedAxisVectorLindeberg_eventually_zero
    rounds
      (fun i y => binaryBornProbability (blochDot theta (axis i)) y)
      (fun i => blochDot theta (axis i)) axis regularWeight
      (blochNorm theta) epsilon
      (blochNorm_lt_one_of_normSq_lt_one theta hinterior)
      (fun i => abs_blochDot_le_blochNorm theta (axis i) (haxis i))
      haxis hepsilon

/-! ## Rank-one compact-local Bures control -/

theorem protocol_tangentRadiusSq_nonnegative
    {d : Nat} (h : TangentIndex d -> Real) :
    0 <= tangentRadiusSq h := by
  unfold tangentRadiusSq
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The exact pure-state upper expansion implies a `C(h)/n` bound under the
local scaling `a^2 = 1/n`. -/
theorem pureProtocolBuresLocal_upper
    {d : Nat} (shots : Nat) (hshots : 0 < shots)
    (a : Real) (h : TangentIndex d -> Real)
    (ha : a ^ 2 = ((shots : Real))⁻¹)
    (hchart : a ^ 2 * tangentRadiusSq h <= 4) :
    buresChartLoss (a • h) <=
      (tangentRadiusSq h / 4 + (tangentRadiusSq h) ^ 2 / 16) /
        (shots : Real) := by
  let r := tangentRadiusSq h
  have hr : 0 <= r := protocol_tangentRadiusSq_nonnegative h
  have hshotsReal : 0 < (shots : Real) := by exact_mod_cast hshots
  have hshotsOne : 1 <= (shots : Real) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hshots))
  have hinv_nonnegative : 0 <= ((shots : Real))⁻¹ :=
    inv_nonneg.mpr hshotsReal.le
  have hinv_le_one : ((shots : Real))⁻¹ <= 1 :=
    inv_le_one_of_one_le₀ hshotsOne
  have hinv_sq_le : ((shots : Real))⁻¹ ^ 2 <= ((shots : Real))⁻¹ := by
    nlinarith
  have hupper := buresChartLoss_smul_upper a h hchart
  calc
    buresChartLoss (a • h) <=
        a ^ 2 * r / 4 + a ^ 4 * r ^ 2 / 16 := hupper
    _ = r / 4 * ((shots : Real))⁻¹ +
        r ^ 2 / 16 * ((shots : Real))⁻¹ ^ 2 := by
      rw [show a ^ 4 = (a ^ 2) ^ 2 by ring, ha]
      ring
    _ <= r / 4 * ((shots : Real))⁻¹ +
        r ^ 2 / 16 * ((shots : Real))⁻¹ := by
      have hcoefficient : 0 <= r ^ 2 / 16 := by positivity
      have hsecond :
          r ^ 2 / 16 * ((shots : Real))⁻¹ ^ 2 <=
            r ^ 2 / 16 * ((shots : Real))⁻¹ :=
        mul_le_mul_of_nonneg_left hinv_sq_le hcoefficient
      exact add_le_add (le_refl _) hsecond
    _ = (r / 4 + r ^ 2 / 16) / (shots : Real) := by
      rw [div_eq_mul_inv]
      ring

/-- Uniform rank-one Bures control on a chart ball
`tangentRadiusSq h <= R`. -/
theorem pureProtocolBuresCompact_upper
    {d : Nat} (shots : Nat) (hshots : 0 < shots)
    (a : Real) (h : TangentIndex d -> Real) (R : Real)
    (hR : 0 <= R) (hradius : tangentRadiusSq h <= R)
    (ha : a ^ 2 = ((shots : Real))⁻¹)
    (hchart : a ^ 2 * tangentRadiusSq h <= 4) :
    buresChartLoss (a • h) <=
      (R / 4 + R ^ 2 / 16) / (shots : Real) := by
  have hr : 0 <= tangentRadiusSq h :=
    protocol_tangentRadiusSq_nonnegative h
  have hr_sq : (tangentRadiusSq h) ^ 2 <= R ^ 2 :=
    (sq_le_sq₀ hr hR).2 hradius
  have hconstant :
      tangentRadiusSq h / 4 + (tangentRadiusSq h) ^ 2 / 16 <=
        R / 4 + R ^ 2 / 16 := by
    nlinarith
  exact (pureProtocolBuresLocal_upper shots hshots a h ha hchart).trans
    (div_le_div_of_nonneg_right hconstant (Nat.cast_nonneg shots))

end Paper
end QubitOracle
