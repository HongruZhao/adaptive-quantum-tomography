import QubitOracle.Paper.SqrtDQM

/-!
# Protocol-specific DQM for mixed qubit projective measurements

The binary Born law is affine in the Bloch vector.  This file identifies its
exact score linearization and combines it with `SqrtDQM` to obtain the
per-round square-root DQM remainder required by adaptive LAN.
-/

namespace QubitOracle.Paper

open scoped BigOperators
open Filter

noncomputable section

theorem blochDot_shift
    (theta h axis : Fin 3 → ℝ) (a : ℝ) :
    QubitOracle.blochDot (fun j => theta j + a * h j) axis =
      QubitOracle.blochDot theta axis +
        a * QubitOracle.blochDot h axis := by
  unfold QubitOracle.blochDot
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  congr 1
  calc
    ∑ j, a * h j * axis j = ∑ j, a * (h j * axis j) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = a * ∑ j, h j * axis j := by
      rw [Finset.mul_sum]

theorem mixedAxisScoreVector_displacement_dot
    (t a : ℝ) (h axis : Fin 3 → ℝ) (y : BinaryOutcome) :
    (∑ j, (a * h j) * mixedAxisScoreVector t axis y j) =
      a * QubitOracle.blochDot h axis * binaryAxisScoreByOutcome t y := by
  change
    (∑ j, (a * h j) * (binaryAxisScoreByOutcome t y * axis j)) =
      a * QubitOracle.blochDot h axis * binaryAxisScoreByOutcome t y
  unfold QubitOracle.blochDot
  calc
    ∑ j, (a * h j) * (binaryAxisScoreByOutcome t y * axis j) =
        ∑ j, (a * binaryAxisScoreByOutcome t y) * (h j * axis j) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (a * binaryAxisScoreByOutcome t y) * ∑ j, h j * axis j := by
      rw [Finset.mul_sum]
    _ = a * (∑ j, h j * axis j) * binaryAxisScoreByOutcome t y := by
      ring

theorem binaryBornProbability_increment
    (t delta : ℝ) (y : BinaryOutcome) :
    binaryBornProbability (t + delta) y - binaryBornProbability t y =
      y.sign * delta / 2 := by
  cases y <;> simp [binaryBornProbability, BinaryOutcome.sign] <;> ring

theorem binaryBornProbability_mul_score
    (t : ℝ) (y : BinaryOutcome)
    (hp : 0 < binaryBornProbability t y) :
    binaryBornProbability t y * binaryAxisScoreByOutcome t y = y.sign / 2 := by
  cases y with
  | plus =>
      have hpos : 0 < 1 + t := by
        simpa [binaryBornProbability, BinaryOutcome.sign] using hp
      have hden : 1 + t ≠ 0 := ne_of_gt hpos
      simp only [binaryBornProbability, binaryAxisScoreByOutcome,
        BinaryOutcome.sign, QubitOracle.binaryAxisPlusScore]
      field_simp [hden]
  | minus =>
      have hpos : 0 < 1 - t := by
        simpa [binaryBornProbability, BinaryOutcome.sign] using hp
      have hden : 1 - t ≠ 0 := ne_of_gt hpos
      simp only [binaryBornProbability, binaryAxisScoreByOutcome,
        BinaryOutcome.sign, QubitOracle.binaryAxisMinusScore]
      field_simp [hden] <;> ring

theorem binaryBorn_sqrt_score_linear_term
    (t delta : ℝ) (y : BinaryOutcome)
    (hp : 0 < binaryBornProbability t y) :
    (1 / 2 * (delta * binaryAxisScoreByOutcome t y)) *
        Real.sqrt (binaryBornProbability t y) =
      (binaryBornProbability (t + delta) y - binaryBornProbability t y) /
        (2 * Real.sqrt (binaryBornProbability t y)) := by
  have hp0 : 0 ≤ binaryBornProbability t y := le_of_lt hp
  have hsqrt : 0 < Real.sqrt (binaryBornProbability t y) :=
    Real.sqrt_pos.2 hp
  have hsqrt_ne : Real.sqrt (binaryBornProbability t y) ≠ 0 := ne_of_gt hsqrt
  have hsqrt_sq : (Real.sqrt (binaryBornProbability t y)) ^ 2 =
      binaryBornProbability t y := Real.sq_sqrt hp0
  have hscore := binaryBornProbability_mul_score t y hp
  rw [binaryBornProbability_increment]
  apply (eq_div_iff (mul_ne_zero (by norm_num) hsqrt_ne)).2
  calc
    ((1 / 2 * (delta * binaryAxisScoreByOutcome t y)) *
          Real.sqrt (binaryBornProbability t y)) *
        (2 * Real.sqrt (binaryBornProbability t y)) =
        delta * (Real.sqrt (binaryBornProbability t y)) ^ 2 *
          binaryAxisScoreByOutcome t y := by ring
    _ = delta * (binaryBornProbability t y *
          binaryAxisScoreByOutcome t y) := by rw [hsqrt_sq]; ring
    _ = delta * (y.sign / 2) := by rw [hscore]
    _ = y.sign * delta / 2 := by ring

/-- The exact DQM linear term for a Bloch displacement `a • h`. -/
theorem mixedProjectiveBorn_sqrt_score_linear_term
    (theta h axis : Fin 3 → ℝ) (a : ℝ) (y : BinaryOutcome)
    (hp : 0 < binaryBornProbability (QubitOracle.blochDot theta axis) y) :
    (1 / 2 * ∑ j, (a * h j) *
        mixedAxisScoreVector (QubitOracle.blochDot theta axis) axis y j) *
        Real.sqrt (binaryBornProbability (QubitOracle.blochDot theta axis) y) =
      (binaryBornProbability
          (QubitOracle.blochDot (fun j => theta j + a * h j) axis) y -
        binaryBornProbability (QubitOracle.blochDot theta axis) y) /
        (2 * Real.sqrt
          (binaryBornProbability (QubitOracle.blochDot theta axis) y)) := by
  rw [mixedAxisScoreVector_displacement_dot]
  rw [blochDot_shift]
  exact binaryBorn_sqrt_score_linear_term
    (QubitOracle.blochDot theta axis)
    (a * QubitOracle.blochDot h axis) y hp

/-- Per-outcome square-root DQM remainder for the actual mixed-qubit binary
projective model, under a common local probability floor. -/
theorem mixedProjective_finiteDQMResidual_abs_le
    (theta h axis : Fin 3 → ℝ) (a m : ℝ) (y : BinaryOutcome)
    (hm : 0 < m)
    (hlocal : m ≤ binaryBornProbability
      (QubitOracle.blochDot (fun j => theta j + a * h j) axis) y)
    (hbase : m ≤ binaryBornProbability
      (QubitOracle.blochDot theta axis) y) :
    |finiteDQMResidual
        (fun z => binaryBornProbability
          (QubitOracle.blochDot (fun j => theta j + a * h j) axis) z)
        (fun z => binaryBornProbability (QubitOracle.blochDot theta axis) z)
        (fun z j => mixedAxisScoreVector
          (QubitOracle.blochDot theta axis) axis z j)
        (fun j => a * h j) y| ≤
      ((a * QubitOracle.blochDot h axis) / 2) ^ 2 /
        (2 * m * Real.sqrt m) := by
  have hp : 0 < binaryBornProbability (QubitOracle.blochDot theta axis) y :=
    lt_of_lt_of_le hm hbase
  unfold finiteDQMResidual
  rw [mixedProjectiveBorn_sqrt_score_linear_term theta h axis a y hp]
  rw [blochDot_shift]
  have hbound := abs_sqrt_sub_linearization_le hm hlocal hbase
  rw [blochDot_shift] at hbound
  rw [binaryBornProbability_increment] at hbound
  rw [binaryBornProbability_increment]
  cases y <;>
    simpa [BinaryOutcome.sign, neg_div, neg_sq] using hbound

theorem blochNorm_eq_euclideanNorm (v : Fin 3 → ℝ) :
    blochNorm v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 3))‖ := by
  unfold blochNorm QubitOracle.blochNormSq
  rw [EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp [Real.norm_eq_abs, sq_abs]

theorem blochNorm_shift_le
    (theta h : Fin 3 → ℝ) (a : ℝ) :
    blochNorm (fun j => theta j + a * h j) ≤
      blochNorm theta + |a| * blochNorm h := by
  let thetaE : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 theta
  let hE : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 h
  have hshift :
      (WithLp.toLp 2 (fun j => theta j + a * h j) :
        EuclideanSpace ℝ (Fin 3)) = thetaE + a • hE := by
    ext j
    rfl
  rw [blochNorm_eq_euclideanNorm, hshift]
  calc
    ‖thetaE + a • hE‖ ≤ ‖thetaE‖ + ‖a • hE‖ := norm_add_le _ _
    _ = ‖thetaE‖ + |a| * ‖hE‖ := by
      rw [norm_smul]
      simp [Real.norm_eq_abs]
    _ = blochNorm theta + |a| * blochNorm h := by
      rw [blochNorm_eq_euclideanNorm theta,
        blochNorm_eq_euclideanNorm h]

theorem mixedProjective_base_quarter_gap_floor
    (theta axis : Fin 3 → ℝ)
    (htheta : blochNorm theta < 1)
    (haxis : QubitOracle.blochNormSq axis ≤ 1)
    (y : BinaryOutcome) :
    (1 - blochNorm theta) / 4 ≤
      binaryBornProbability (QubitOracle.blochDot theta axis) y := by
  have hfloor := mixedProjectiveBornProbability_floor theta axis haxis y
  linarith

theorem mixedProjective_local_quarter_gap_floor
    (theta h axis : Fin 3 → ℝ) (a : ℝ)
    (htheta : blochNorm theta < 1)
    (haxis : QubitOracle.blochNormSq axis ≤ 1)
    (hsmall : |a| * blochNorm h ≤ (1 - blochNorm theta) / 2)
    (y : BinaryOutcome) :
    (1 - blochNorm theta) / 4 ≤
      binaryBornProbability
        (QubitOracle.blochDot (fun j => theta j + a * h j) axis) y := by
  have hnorm := blochNorm_shift_le theta h a
  have hlocalNorm :
      blochNorm (fun j => theta j + a * h j) ≤
        (1 + blochNorm theta) / 2 := by
    linarith
  have hfloor := mixedProjectiveBornProbability_floor
    (fun j => theta j + a * h j) axis haxis y
  linarith

/-- Actual mixed-qubit DQM remainder with its probability-floor hypotheses
discharged by the interior Bloch gap and a local-neighborhood condition. -/
theorem mixedProjective_interior_finiteDQMResidual_abs_le
    (theta h axis : Fin 3 → ℝ) (a : ℝ) (y : BinaryOutcome)
    (htheta : blochNorm theta < 1)
    (haxis : QubitOracle.blochNormSq axis ≤ 1)
    (hsmall : |a| * blochNorm h ≤ (1 - blochNorm theta) / 2) :
    |finiteDQMResidual
        (fun z => binaryBornProbability
          (QubitOracle.blochDot (fun j => theta j + a * h j) axis) z)
        (fun z => binaryBornProbability (QubitOracle.blochDot theta axis) z)
        (fun z j => mixedAxisScoreVector
          (QubitOracle.blochDot theta axis) axis z j)
        (fun j => a * h j) y| ≤
      ((a * QubitOracle.blochDot h axis) / 2) ^ 2 /
        (2 * ((1 - blochNorm theta) / 4) *
          Real.sqrt ((1 - blochNorm theta) / 4)) := by
  apply mixedProjective_finiteDQMResidual_abs_le
  · linarith
  · exact mixedProjective_local_quarter_gap_floor
      theta h axis a htheta haxis hsmall y
  · exact mixedProjective_base_quarter_gap_floor theta axis htheta haxis y

theorem eventually_invSqrt_mul_blochNorm_le_half_gap
    (theta h : Fin 3 → ℝ)
    (htheta : blochNorm theta < 1) :
    ∀ᶠ n : ℕ in atTop,
      |(Real.sqrt (n : ℝ))⁻¹| * blochNorm h ≤
        (1 - blochNorm theta) / 2 := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hcast
  have hinv : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hsqrt
  have hscaled : Tendsto
      (fun n : ℕ => |(Real.sqrt (n : ℝ))⁻¹| * blochNorm h)
      atTop (nhds 0) := by
    simpa using hinv.abs.mul_const (blochNorm h)
  have hgap : 0 < (1 - blochNorm theta) / 2 := by linarith
  filter_upwards [(tendsto_order.1 hscaled).2 _ hgap] with n hn
  exact le_of_lt hn

/-- For every fixed local direction, the actual binary projective DQM bound
holds eventually at the LAN scale `1 / sqrt n`, uniformly over both outcomes. -/
theorem mixedProjective_interior_DQM_eventually
    (theta h axis : Fin 3 → ℝ)
    (htheta : blochNorm theta < 1)
    (haxis : QubitOracle.blochNormSq axis ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ∀ y : BinaryOutcome,
      |finiteDQMResidual
          (fun z => binaryBornProbability
            (QubitOracle.blochDot
              (fun j => theta j + (Real.sqrt (n : ℝ))⁻¹ * h j) axis) z)
          (fun z => binaryBornProbability
            (QubitOracle.blochDot theta axis) z)
          (fun z j => mixedAxisScoreVector
            (QubitOracle.blochDot theta axis) axis z j)
          (fun j => (Real.sqrt (n : ℝ))⁻¹ * h j) y| ≤
        ((((Real.sqrt (n : ℝ))⁻¹ *
            QubitOracle.blochDot h axis) / 2) ^ 2) /
          (2 * ((1 - blochNorm theta) / 4) *
            Real.sqrt ((1 - blochNorm theta) / 4)) := by
  filter_upwards [eventually_invSqrt_mul_blochNorm_le_half_gap
    theta h htheta] with n hn
  intro y
  exact mixedProjective_interior_finiteDQMResidual_abs_le
    theta h axis (Real.sqrt (n : ℝ))⁻¹ y htheta haxis hn

def mixedDQMRateConstant (theta h : Fin 3 → ℝ) : ℝ :=
  (blochNorm h) ^ 2 /
    (8 * ((1 - blochNorm theta) / 4) *
      Real.sqrt ((1 - blochNorm theta) / 4))

theorem mixedDQMRateConstant_nonnegative
    (theta h : Fin 3 → ℝ) (htheta : blochNorm theta < 1) :
    0 ≤ mixedDQMRateConstant theta h := by
  unfold mixedDQMRateConstant
  positivity

theorem mixed_invSqrt_remainder_eq_rate
    (n : ℕ) (hn : 0 < n) (z m : ℝ) (hm : 0 < m) :
    ((((Real.sqrt (n : ℝ))⁻¹ * z) / 2) ^ 2) /
        (2 * m * Real.sqrt m) =
      (z ^ 2 / (8 * m * Real.sqrt m)) / (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hsqrt
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hm_ne : m ≠ 0 := ne_of_gt hm
  have hsqrtm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hsqrtm_ne : Real.sqrt m ≠ 0 := ne_of_gt hsqrtm
  have hsqrt_sq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt (le_of_lt hnR)
  field_simp [hsqrt_ne, hn_ne, hm_ne, hsqrtm_ne]
  nlinarith

theorem mixedProjective_interior_DQM_invSqrt_rate
    (n : ℕ) (hn : 0 < n)
    (theta h axis : Fin 3 → ℝ) (y : BinaryOutcome)
    (htheta : blochNorm theta < 1)
    (haxis : QubitOracle.blochNormSq axis ≤ 1)
    (hsmall : |(Real.sqrt (n : ℝ))⁻¹| * blochNorm h ≤
      (1 - blochNorm theta) / 2) :
    |finiteDQMResidual
        (fun z => binaryBornProbability
          (QubitOracle.blochDot
            (fun j => theta j + (Real.sqrt (n : ℝ))⁻¹ * h j) axis) z)
        (fun z => binaryBornProbability (QubitOracle.blochDot theta axis) z)
        (fun z j => mixedAxisScoreVector
          (QubitOracle.blochDot theta axis) axis z j)
        (fun j => (Real.sqrt (n : ℝ))⁻¹ * h j) y| ≤
      mixedDQMRateConstant theta h / (n : ℝ) := by
  let m : ℝ := (1 - blochNorm theta) / 4
  have hm : 0 < m := by dsimp [m]; linarith
  have hraw := mixedProjective_interior_finiteDQMResidual_abs_le
    theta h axis (Real.sqrt (n : ℝ))⁻¹ y htheta haxis hsmall
  have hdot := abs_blochDot_le_blochNorm h axis haxis
  have hzlower : -blochNorm h ≤ QubitOracle.blochDot h axis :=
    (abs_le.mp hdot).1
  have hzupper : QubitOracle.blochDot h axis ≤ blochNorm h :=
    (abs_le.mp hdot).2
  have hzsq : (QubitOracle.blochDot h axis) ^ 2 ≤ (blochNorm h) ^ 2 := by
    have hprod : 0 ≤
        (blochNorm h - QubitOracle.blochDot h axis) *
          (blochNorm h + QubitOracle.blochDot h axis) :=
      mul_nonneg (sub_nonneg.mpr hzupper) (by linarith)
    nlinarith
  have hden : 0 < 8 * m * Real.sqrt m := by positivity
  have hquot :
      (QubitOracle.blochDot h axis) ^ 2 / (8 * m * Real.sqrt m) ≤
        (blochNorm h) ^ 2 / (8 * m * Real.sqrt m) :=
    (div_le_div_iff₀ hden hden).2
      (mul_le_mul_of_nonneg_right hzsq (le_of_lt hden))
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  calc
    |finiteDQMResidual
        (fun z => binaryBornProbability
          (QubitOracle.blochDot
            (fun j => theta j + (Real.sqrt (n : ℝ))⁻¹ * h j) axis) z)
        (fun z => binaryBornProbability (QubitOracle.blochDot theta axis) z)
        (fun z j => mixedAxisScoreVector
          (QubitOracle.blochDot theta axis) axis z j)
        (fun j => (Real.sqrt (n : ℝ))⁻¹ * h j) y| ≤
        ((((Real.sqrt (n : ℝ))⁻¹ *
          QubitOracle.blochDot h axis) / 2) ^ 2) /
          (2 * m * Real.sqrt m) := by simpa [m] using hraw
    _ = ((QubitOracle.blochDot h axis) ^ 2 /
          (8 * m * Real.sqrt m)) / (n : ℝ) :=
      mixed_invSqrt_remainder_eq_rate n hn _ m hm
    _ ≤ ((blochNorm h) ^ 2 / (8 * m * Real.sqrt m)) / (n : ℝ) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hquot (le_of_lt (inv_pos.mpr hnR))
    _ = mixedDQMRateConstant theta h / (n : ℝ) := by
      rfl

theorem mixedProjective_interior_DQMDefect_invSqrt_rate
    (n : ℕ) (hn : 0 < n)
    (theta h axis : Fin 3 → ℝ)
    (htheta : blochNorm theta < 1)
    (haxis : QubitOracle.blochNormSq axis ≤ 1)
    (hsmall : |(Real.sqrt (n : ℝ))⁻¹| * blochNorm h ≤
      (1 - blochNorm theta) / 2) :
    finiteDQMDefect
        (fun z => binaryBornProbability
          (QubitOracle.blochDot
            (fun j => theta j + (Real.sqrt (n : ℝ))⁻¹ * h j) axis) z)
        (fun z => binaryBornProbability (QubitOracle.blochDot theta axis) z)
        (fun z j => mixedAxisScoreVector
          (QubitOracle.blochDot theta axis) axis z j)
        (fun j => (Real.sqrt (n : ℝ))⁻¹ * h j) ≤
      (Fintype.card BinaryOutcome : ℝ) *
        (mixedDQMRateConstant theta h) ^ 2 / (n : ℝ) ^ 2 := by
  apply finiteDQMDefect_le_card_mul_sq_div
  · exact mixedDQMRateConstant_nonnegative theta h htheta
  · intro y
    exact mixedProjective_interior_DQM_invSqrt_rate
      n hn theta h axis y htheta haxis hsmall

theorem mixedProjective_interior_DQMDefect_eventually
    (theta h axis : Fin 3 → ℝ)
    (htheta : blochNorm theta < 1)
    (haxis : QubitOracle.blochNormSq axis ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      finiteDQMDefect
          (fun z => binaryBornProbability
            (QubitOracle.blochDot
              (fun j => theta j + (Real.sqrt (n : ℝ))⁻¹ * h j) axis) z)
          (fun z => binaryBornProbability (QubitOracle.blochDot theta axis) z)
          (fun z j => mixedAxisScoreVector
            (QubitOracle.blochDot theta axis) axis z j)
          (fun j => (Real.sqrt (n : ℝ))⁻¹ * h j) ≤
        (Fintype.card BinaryOutcome : ℝ) *
          (mixedDQMRateConstant theta h) ^ 2 / (n : ℝ) ^ 2 := by
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < n :=
    Filter.eventually_atTop.2 ⟨1, fun n hn => by omega⟩
  filter_upwards [hpos,
    eventually_invSqrt_mul_blochNorm_le_half_gap theta h htheta] with n hn hsmall
  exact mixedProjective_interior_DQMDefect_invSqrt_rate
    n hn theta h axis htheta haxis hsmall

def mixedProjectiveDQMDefectAt
    (n : ℕ) (theta h axis : Fin 3 → ℝ) : ℝ :=
  finiteDQMDefect
    (fun z => binaryBornProbability
      (QubitOracle.blochDot
        (fun j => theta j + (Real.sqrt (n : ℝ))⁻¹ * h j) axis) z)
    (fun z => binaryBornProbability (QubitOracle.blochDot theta axis) z)
    (fun z j => mixedAxisScoreVector
      (QubitOracle.blochDot theta axis) axis z j)
    (fun j => (Real.sqrt (n : ℝ))⁻¹ * h j)

theorem mixedProjectiveDQMDefectAt_nonnegative
    (n : ℕ) (theta h axis : Fin 3 → ℝ) :
    0 ≤ mixedProjectiveDQMDefectAt n theta h axis := by
  unfold mixedProjectiveDQMDefectAt
  exact finiteDQMDefect_nonnegative _ _ _ _

theorem mixedProjectiveDQMDefectAt_eventually_le
    (theta h axis : Fin 3 → ℝ)
    (htheta : blochNorm theta < 1)
    (haxis : QubitOracle.blochNormSq axis ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      mixedProjectiveDQMDefectAt n theta h axis ≤
        (Fintype.card BinaryOutcome : ℝ) *
          (mixedDQMRateConstant theta h) ^ 2 / (n : ℝ) ^ 2 := by
  simpa [mixedProjectiveDQMDefectAt] using
    mixedProjective_interior_DQMDefect_eventually
      theta h axis htheta haxis

/-- Pathwise verification of S-DQM for the actual mixed-qubit projective
protocol.  The adaptive controller and exploration randomization may choose
arbitrary axes; only the projective-axis norm bound and at most `n` retained
rounds are used. -/
theorem mixedProtocol_SDQM_tendstoInMeasure
    {Omega I : Type*} [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega)
    (rounds : ℕ → Finset I)
    (axis : ℕ → Omega → I → Fin 3 → ℝ)
    (theta h : Fin 3 → ℝ)
    (htheta : blochNorm theta < 1)
    (hcard : ∀ n, (rounds n).card ≤ n)
    (haxis : ∀ n omega i, i ∈ rounds n →
      QubitOracle.blochNormSq (axis n omega i) ≤ 1) :
    MeasureTheory.TendstoInMeasure mu
      (fun n omega => ∑ i ∈ rounds n,
        mixedProjectiveDQMDefectAt n theta h (axis n omega i))
      atTop 0 := by
  let B : ℝ := (Fintype.card BinaryOutcome : ℝ) *
    (mixedDQMRateConstant theta h) ^ 2
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  apply tendstoInMeasure_of_eventually_uniform_norm_le mu
    (fun n omega => ∑ i ∈ rounds n,
      mixedProjectiveDQMDefectAt n theta h (axis n omega i))
    (fun n => B / (n : ℝ))
    (tendsto_div_natCast_zero B)
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < n :=
    Filter.eventually_atTop.2 ⟨1, fun n hn => by omega⟩
  filter_upwards [hpos,
    eventually_invSqrt_mul_blochNorm_le_half_gap theta h htheta] with n hn hsmall
  intro omega
  have hnonnegative :
      0 ≤ ∑ i ∈ rounds n,
        mixedProjectiveDQMDefectAt n theta h (axis n omega i) := by
    exact Finset.sum_nonneg fun i _ =>
      mixedProjectiveDQMDefectAt_nonnegative
        n theta h (axis n omega i)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonnegative]
  apply sum_per_round_dqm_defect_le
    (rounds n)
    (fun i => mixedProjectiveDQMDefectAt n theta h (axis n omega i))
    n B hn (hcard n) hB
  intro i hi
  dsimp [B]
  simpa [mixedProjectiveDQMDefectAt] using
    mixedProjective_interior_DQMDefect_invSqrt_rate
      n hn theta h (axis n omega i) htheta (haxis n omega i hi) hsmall

end

end QubitOracle.Paper
