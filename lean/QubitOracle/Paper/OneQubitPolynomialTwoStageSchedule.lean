import QubitOracle.Paper.OneQubitPauliPilotConsistency

/-!
# A concrete polynomial two-stage qubit schedule

At integer index `n`, put `m = n + 1`.  The deterministic schedule uses
`m^5` complete three-Pauli pilot blocks and `m^6` final-stage shots, hence
`3*m^5 + m^6` observations in total.  This replaces all fractional-power
asymptotics by exact integer arithmetic.

The only probabilistic premise below is the paired Hoeffding Theorem 2 contract
already isolated in `OneQubitPauliPilotBornProductLaw` and assembled in
`OneQubitPauliPilotConsistency`.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory Set
open scoped ENNReal

/-- The positive integer schedule parameter `m = n + 1`. -/
def polynomialScheduleM (n : ℕ) : ℕ := Nat.succ n

private theorem polynomialScheduleMReal_pos (n : ℕ) :
    0 < (polynomialScheduleM n : ℝ) := by
  simp only [polynomialScheduleM, Nat.cast_succ]
  positivity

private theorem polynomialScheduleMReal_ne_zero (n : ℕ) :
    (polynomialScheduleM n : ℝ) ≠ 0 :=
  ne_of_gt (polynomialScheduleMReal_pos n)

/-- Number of complete pilot blocks; every block has the three Pauli axes. -/
def polynomialPilotBlocks (n : ℕ) : ℕ := polynomialScheduleM n ^ 5

/-- Actual number of pilot observations. -/
def polynomialPilotObservations (n : ℕ) : ℕ :=
  3 * polynomialPilotBlocks n

/-- Number of final-stage observations. -/
def polynomialFinalShots (n : ℕ) : ℕ := polynomialScheduleM n ^ 6

/-- Total number of observations in the two stages. -/
def polynomialTotalShots (n : ℕ) : ℕ :=
  polynomialPilotObservations n + polynomialFinalShots n

/-- Pilot-observation fraction, in its algebraically reduced form. -/
noncomputable def polynomialPilotFraction (n : ℕ) : ℝ :=
  3 / ((polynomialScheduleM n : ℝ) + 3)

/-- Final-stage fraction, in its algebraically reduced form. -/
noncomputable def polynomialFinalFraction (n : ℕ) : ℝ :=
  (polynomialScheduleM n : ℝ) /
    ((polynomialScheduleM n : ℝ) + 3)

/-- The reduced pilot fraction is exactly the pilot-count/total-count ratio. -/
theorem polynomialPilotFraction_eq_observationRatio (n : ℕ) :
    polynomialPilotFraction n =
      (polynomialPilotObservations n : ℝ) /
        (polynomialTotalShots n : ℝ) := by
  have hmpos : 0 < (polynomialScheduleM n : ℝ) :=
    polynomialScheduleMReal_pos n
  have hmne : (polynomialScheduleM n : ℝ) ≠ 0 := ne_of_gt hmpos
  have hlinear : (polynomialScheduleM n : ℝ) + 3 ≠ 0 := by
    positivity
  have htotal :
      3 * (polynomialScheduleM n : ℝ) ^ 5 +
          (polynomialScheduleM n : ℝ) ^ 6 ≠ 0 := by
    positivity
  unfold polynomialPilotFraction polynomialTotalShots
    polynomialPilotObservations polynomialPilotBlocks polynomialFinalShots
  push_cast
  field_simp [hmne, hlinear, htotal]
  ring

/-- The reduced final fraction is exactly the final-count/total-count ratio. -/
theorem polynomialFinalFraction_eq_observationRatio (n : ℕ) :
    polynomialFinalFraction n =
      (polynomialFinalShots n : ℝ) /
        (polynomialTotalShots n : ℝ) := by
  have hmpos : 0 < (polynomialScheduleM n : ℝ) :=
    polynomialScheduleMReal_pos n
  have hmne : (polynomialScheduleM n : ℝ) ≠ 0 := ne_of_gt hmpos
  have hlinear : (polynomialScheduleM n : ℝ) + 3 ≠ 0 := by
    positivity
  have htotal :
      3 * (polynomialScheduleM n : ℝ) ^ 5 +
          (polynomialScheduleM n : ℝ) ^ 6 ≠ 0 := by
    positivity
  unfold polynomialFinalFraction polynomialTotalShots
    polynomialPilotObservations polynomialPilotBlocks polynomialFinalShots
  push_cast
  field_simp [hmne, hlinear, htotal]
  ring

private theorem polynomialScheduleMReal_tendsto :
    Tendsto (fun n : ℕ => (polynomialScheduleM n : ℝ)) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards
    [(tendsto_atTop.1 tendsto_natCast_atTop_atTop) b] with n hn
  calc
    b ≤ (n : ℝ) := hn
    _ ≤ (polynomialScheduleM n : ℝ) := by
      simp [polynomialScheduleM]

private theorem polynomialScheduleDenominatorReal_tendsto :
    Tendsto
      (fun n : ℕ => (polynomialScheduleM n : ℝ) + 3)
      atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards
    [(tendsto_atTop.1 polynomialScheduleMReal_tendsto) (b - 3)] with n hn
  linarith

/-- The pilot consumes a vanishing fraction of all observations. -/
theorem polynomialPilotFraction_tendsto_zero :
    Tendsto polynomialPilotFraction atTop (nhds 0) := by
  have hinv :
      Tendsto
        (fun n : ℕ =>
          ((polynomialScheduleM n : ℝ) + 3)⁻¹)
        atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp polynomialScheduleDenominatorReal_tendsto
  have hmul :
      Tendsto
        (fun n : ℕ =>
          (3 : ℝ) * ((polynomialScheduleM n : ℝ) + 3)⁻¹)
        atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hinv
  change Tendsto
    (fun n : ℕ => 3 / ((polynomialScheduleM n : ℝ) + 3))
    atTop (nhds 0)
  simpa only [div_eq_mul_inv] using hmul

/-- The final-stage and pilot fractions add exactly to one. -/
theorem polynomialFinalFraction_eq_one_sub_pilot (n : ℕ) :
    polynomialFinalFraction n = 1 - polynomialPilotFraction n := by
  have hlinear : (polynomialScheduleM n : ℝ) + 3 ≠ 0 := by
    have : 0 < (polynomialScheduleM n : ℝ) :=
      polynomialScheduleMReal_pos n
    positivity
  unfold polynomialFinalFraction polynomialPilotFraction
  field_simp [hlinear]
  ring

/-- The final stage consumes an asymptotic fraction one of all observations. -/
theorem polynomialFinalFraction_tendsto_one :
    Tendsto polynomialFinalFraction atTop (nhds 1) := by
  have hfun :
      polynomialFinalFraction =
        (fun n : ℕ => 1 - polynomialPilotFraction n) := by
    funext n
    exact polynomialFinalFraction_eq_one_sub_pilot n
  rw [hfun]
  simpa using tendsto_const_nhds.sub polynomialPilotFraction_tendsto_zero

/-- Index in the common pilot-consistency product space corresponding to
exactly `m^5` complete pilot blocks. -/
def polynomialPilotIndex (n : ℕ) : ℕ := polynomialPilotBlocks n - 1

/-- The scheduled pilot has at least one complete block. -/
theorem polynomialPilotBlocks_pos (n : ℕ) : 0 < polynomialPilotBlocks n := by
  unfold polynomialPilotBlocks polynomialScheduleM
  positivity

/-- The common-space coordinate at `polynomialPilotIndex n` has exactly `m^5`
blocks, with no off-by-one discrepancy. -/
theorem polynomialPilotIndex_succ (n : ℕ) :
    Nat.succ (polynomialPilotIndex n) = polynomialPilotBlocks n := by
  have hpos := polynomialPilotBlocks_pos n
  unfold polynomialPilotIndex
  omega

/-- Pilot estimator selected according to the polynomial schedule. -/
noncomputable def polynomialPilotEstimator
    (n : ℕ) (omega : PauliPilotConsistencySampleSpace) : RLSVector 3 :=
  pauliPilotConsistencyEstimator (polynomialPilotIndex n) omega

/-- Coordinate threshold `1/m^2`. -/
noncomputable def polynomialPilotThreshold (n : ℕ) : ℝ :=
  1 / (polynomialScheduleM n : ℝ) ^ 2

/-- The simultaneous three-coordinate bad event at threshold `1/m^2`. -/
def polynomialPilotBadEvent (theta : RLSVector 3) (n : ℕ) :
    Set PauliPilotConsistencySampleSpace :=
  QubitOracle.coordinateDeltaBadEvent
    polynomialPilotEstimator theta n (polynomialPilotThreshold n)

/-- Explicit simultaneous-tail envelope.  Its exponent is exactly `m/2`. -/
noncomputable def polynomialPilotBadEventEnvelope (n : ℕ) : ℝ≥0∞ :=
  6 * ENNReal.ofReal
    (Real.exp (-((polynomialScheduleM n : ℝ) / 2)))

/-- The schedule turns the finite-pilot Hoeffding exponent into exactly `m/2`. -/
theorem polynomialPilotFiniteHoeffdingEnvelope_eq (n : ℕ) :
    pauliPilotFiniteHoeffdingEnvelope
        (polynomialPilotIndex n) (polynomialPilotThreshold n) =
      polynomialPilotBadEventEnvelope n := by
  have hcast :
      (Nat.succ (polynomialPilotIndex n) : ℝ) =
        (polynomialScheduleM n : ℝ) ^ 5 := by
    rw [polynomialPilotIndex_succ]
    simp [polynomialPilotBlocks]
  have hmne : (polynomialScheduleM n : ℝ) ≠ 0 :=
    polynomialScheduleMReal_ne_zero n
  have hcollapse :
      -((polynomialScheduleM n : ℝ) ^ 5 *
            (1 / (polynomialScheduleM n : ℝ) ^ 2) ^ 2 / 2) =
        -((polynomialScheduleM n : ℝ) / 2) := by
    field_simp [hmne]
  unfold pauliPilotFiniteHoeffdingEnvelope
    pauliPilotCoordinateHoeffdingEnvelope polynomialPilotThreshold
    polynomialPilotBadEventEnvelope
  rw [hcast, hcollapse]
  ring

/-- Explicit scheduled bad-event bound under only the already isolated paired
Hoeffding contracts. -/
theorem polynomialPilot_badEvent_bound
    (theta : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (hHoeffding : PauliPilotConsistencyHoeffdingContracts theta hphysical)
    (n : ℕ) :
    pauliPilotConsistencyMeasure theta (polynomialPilotBadEvent theta n) ≤
      polynomialPilotBadEventEnvelope n := by
  have hthreshold : 0 < polynomialPilotThreshold n := by
    unfold polynomialPilotThreshold
    exact one_div_pos.mpr (pow_pos (polynomialScheduleMReal_pos n) 2)
  calc
    pauliPilotConsistencyMeasure theta (polynomialPilotBadEvent theta n) =
      pauliPilotConsistencyMeasure theta
        (QubitOracle.coordinateDeltaBadEvent
          pauliPilotConsistencyEstimator theta
          (polynomialPilotIndex n) (polynomialPilotThreshold n)) := by
            rfl
    _ ≤ pauliPilotFiniteHoeffdingEnvelope
          (polynomialPilotIndex n) (polynomialPilotThreshold n) :=
      pauliPilotConsistency_finite_tail
        theta hphysical hHoeffding (polynomialPilotIndex n)
          (polynomialPilotThreshold n) hthreshold
    _ = polynomialPilotBadEventEnvelope n :=
      polynomialPilotFiniteHoeffdingEnvelope_eq n

/-- The explicit `6 exp(-m/2)` bad-event envelope tends to zero. -/
theorem polynomialPilotBadEventEnvelope_tendsto_zero :
    Tendsto polynomialPilotBadEventEnvelope atTop (nhds 0) := by
  have hnegative : (-(1 / 2 : ℝ)) < 0 := by norm_num
  have hscaled :
      Tendsto
        (fun n : ℕ =>
          (polynomialScheduleM n : ℝ) * (-(1 / 2 : ℝ)))
        atTop atBot :=
    polynomialScheduleMReal_tendsto.atTop_mul_const_of_neg hnegative
  have hfun :
      (fun n : ℕ =>
        (polynomialScheduleM n : ℝ) * (-(1 / 2 : ℝ))) =
      (fun n : ℕ => -((polynomialScheduleM n : ℝ) / 2)) := by
    funext n
    ring
  have htoBot :
      Tendsto
        (fun n : ℕ => -((polynomialScheduleM n : ℝ) / 2))
        atTop atBot :=
    hfun ▸ hscaled
  have hexp :
      Tendsto
        (fun n : ℕ =>
          Real.exp (-((polynomialScheduleM n : ℝ) / 2)))
        atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp htoBot
  have hofReal :
      Tendsto
        (fun n : ℕ => ENNReal.ofReal
          (Real.exp (-((polynomialScheduleM n : ℝ) / 2))))
        atTop (nhds 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hexp
  have hmul :
      Tendsto (fun x : ℝ≥0∞ => 6 * x) (nhds 0) (nhds 0) :=
    by
      simpa using
        (ENNReal.continuousAt_const_mul
          (a := (6 : ℝ≥0∞)) (b := (0 : ℝ≥0∞))
          (Or.inl (by norm_num))).tendsto
  change Tendsto
    (fun n : ℕ => 6 * ENNReal.ofReal
      (Real.exp (-((polynomialScheduleM n : ℝ) / 2))))
    atTop (nhds 0)
  simpa only [Function.comp_def] using hmul.comp hofReal

/-- Consequently, the scheduled simultaneous pilot bad-event probability tends
to zero under only the paired Hoeffding contracts. -/
theorem polynomialPilot_badEventProbability_tendsto_zero
    (theta : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (hHoeffding : PauliPilotConsistencyHoeffdingContracts theta hphysical) :
    Tendsto
      (fun n : ℕ =>
        pauliPilotConsistencyMeasure theta (polynomialPilotBadEvent theta n))
      atTop (nhds 0) := by
  exact Tendsto.squeeze tendsto_const_nhds
    polynomialPilotBadEventEnvelope_tendsto_zero
    (fun _ => bot_le)
    (fun n => polynomialPilot_badEvent_bound
      theta hphysical hHoeffding n)

/-- Explicit sum of the three squared Bloch-coordinate pilot errors. -/
noncomputable def polynomialPilotSquaredCoordinateError
    (theta : RLSVector 3) (n : ℕ)
    (omega : PauliPilotConsistencySampleSpace) : ℝ :=
  ((polynomialPilotEstimator n omega 0 - theta 0) ^ 2 +
    (polynomialPilotEstimator n omega 1 - theta 1) ^ 2) +
    (polynomialPilotEstimator n omega 2 - theta 2) ^ 2

/-- The squared-coordinate error is nonnegative. -/
theorem polynomialPilotSquaredCoordinateError_nonneg
    (theta : RLSVector 3) (n : ℕ)
    (omega : PauliPilotConsistencySampleSpace) :
    0 ≤ polynomialPilotSquaredCoordinateError theta n omega := by
  unfold polynomialPilotSquaredCoordinateError
  positivity

/-- Squaring the scheduled threshold gives exactly `1/m^4`. -/
theorem polynomialPilotThreshold_sq (n : ℕ) :
    polynomialPilotThreshold n ^ 2 =
      1 / (polynomialScheduleM n : ℝ) ^ 4 := by
  have hmne : (polynomialScheduleM n : ℝ) ≠ 0 :=
    polynomialScheduleMReal_ne_zero n
  unfold polynomialPilotThreshold
  field_simp [hmne]

/-- On the simultaneous good event, the sum of the three squared coordinate
errors is at most `3/m^4`. -/
theorem polynomialPilot_squaredCoordinateError_le_on_good
    (theta : RLSVector 3) (n : ℕ)
    (omega : PauliPilotConsistencySampleSpace)
    (hgood : omega ∉ polynomialPilotBadEvent theta n) :
    polynomialPilotSquaredCoordinateError theta n omega ≤
      3 / (polynomialScheduleM n : ℝ) ^ 4 := by
  have hcoordinate (j : Fin 3) :
      |polynomialPilotEstimator n omega j - theta j| <
        polynomialPilotThreshold n := by
    by_contra hnot
    have hle :
        polynomialPilotThreshold n ≤
          |polynomialPilotEstimator n omega j - theta j| :=
      le_of_not_gt hnot
    apply hgood
    change ∃ k : Fin 3,
      polynomialPilotThreshold n ≤
        |polynomialPilotEstimator n omega k - theta k|
    exact ⟨j, hle⟩
  have hcoordinateSq (j : Fin 3) :
      (polynomialPilotEstimator n omega j - theta j) ^ 2 ≤
        1 / (polynomialScheduleM n : ℝ) ^ 4 := by
    let e : ℝ := polynomialPilotEstimator n omega j - theta j
    change e ^ 2 ≤ 1 / (polynomialScheduleM n : ℝ) ^ 4
    have habs : |e| ≤ polynomialPilotThreshold n := by
      simpa only [e] using le_of_lt (hcoordinate j)
    have hmul :
        |e| * |e| ≤
          polynomialPilotThreshold n * polynomialPilotThreshold n :=
      mul_self_le_mul_self (abs_nonneg e) habs
    calc
      e ^ 2 = |e| * |e| := by
        rw [pow_two, ← abs_mul, abs_of_nonneg (mul_self_nonneg e)]
      _ ≤ polynomialPilotThreshold n * polynomialPilotThreshold n := hmul
      _ = polynomialPilotThreshold n ^ 2 := by ring
      _ = 1 / (polynomialScheduleM n : ℝ) ^ 4 :=
        polynomialPilotThreshold_sq n
  unfold polynomialPilotSquaredCoordinateError
  calc
    ((polynomialPilotEstimator n omega 0 - theta 0) ^ 2 +
        (polynomialPilotEstimator n omega 1 - theta 1) ^ 2) +
        (polynomialPilotEstimator n omega 2 - theta 2) ^ 2 ≤
      ((1 / (polynomialScheduleM n : ℝ) ^ 4) +
        (1 / (polynomialScheduleM n : ℝ) ^ 4)) +
        (1 / (polynomialScheduleM n : ℝ) ^ 4) :=
      add_le_add (add_le_add (hcoordinateSq 0) (hcoordinateSq 1))
        (hcoordinateSq 2)
    _ = 3 / (polynomialScheduleM n : ℝ) ^ 4 := by ring

/-- The total number of shots is bounded by `4*m^6`. -/
theorem polynomialTotalShots_le_four_mul_m_pow_six (n : ℕ) :
    polynomialTotalShots n ≤ 4 * polynomialScheduleM n ^ 6 := by
  have hm : 1 ≤ polynomialScheduleM n := by
    unfold polynomialScheduleM
    omega
  have hpow : polynomialScheduleM n ^ 5 ≤ polynomialScheduleM n ^ 6 := by
    calc
      polynomialScheduleM n ^ 5 = polynomialScheduleM n ^ 5 * 1 := by ring
      _ ≤ polynomialScheduleM n ^ 5 * polynomialScheduleM n :=
        Nat.mul_le_mul_left _ hm
      _ = polynomialScheduleM n ^ 6 := by ring
  unfold polynomialTotalShots polynomialPilotObservations
    polynomialPilotBlocks polynomialFinalShots
  omega

/-- The square root of the total sample size is at most `2*m^3`. -/
theorem polynomialSqrtTotalShots_le_two_mul_m_cube (n : ℕ) :
    Real.sqrt (polynomialTotalShots n : ℝ) ≤
      2 * (polynomialScheduleM n : ℝ) ^ 3 := by
  have hreal :
      (polynomialTotalShots n : ℝ) ≤
        4 * (polynomialScheduleM n : ℝ) ^ 6 := by
    exact_mod_cast polynomialTotalShots_le_four_mul_m_pow_six n
  calc
    Real.sqrt (polynomialTotalShots n : ℝ) ≤
        Real.sqrt (4 * (polynomialScheduleM n : ℝ) ^ 6) :=
      Real.sqrt_le_sqrt hreal
    _ = 2 * (polynomialScheduleM n : ℝ) ^ 3 := by
      rw [show 4 * (polynomialScheduleM n : ℝ) ^ 6 =
        (2 * (polynomialScheduleM n : ℝ) ^ 3) ^ 2 by ring]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
      positivity

/-- Deterministic envelope for the root-total-shot-scaled squared error. -/
noncomputable def polynomialScaledSquaredErrorEnvelope (n : ℕ) : ℝ :=
  6 / (polynomialScheduleM n : ℝ)

/-- On the good event, `sqrt(totalShots)` times squared coordinate error is at
most `6/m`. -/
theorem polynomialPilot_scaledSquaredError_le_on_good
    (theta : RLSVector 3) (n : ℕ)
    (omega : PauliPilotConsistencySampleSpace)
    (hgood : omega ∉ polynomialPilotBadEvent theta n) :
    Real.sqrt (polynomialTotalShots n : ℝ) *
        polynomialPilotSquaredCoordinateError theta n omega ≤
      polynomialScaledSquaredErrorEnvelope n := by
  have hsqrt := polynomialSqrtTotalShots_le_two_mul_m_cube n
  have herror :=
    polynomialPilot_squaredCoordinateError_le_on_good theta n omega hgood
  have hproduct :
      Real.sqrt (polynomialTotalShots n : ℝ) *
          polynomialPilotSquaredCoordinateError theta n omega ≤
        (2 * (polynomialScheduleM n : ℝ) ^ 3) *
          (3 / (polynomialScheduleM n : ℝ) ^ 4) :=
    mul_le_mul hsqrt herror
      (polynomialPilotSquaredCoordinateError_nonneg theta n omega)
      (by positivity)
  have hmne : (polynomialScheduleM n : ℝ) ≠ 0 :=
    polynomialScheduleMReal_ne_zero n
  calc
    Real.sqrt (polynomialTotalShots n : ℝ) *
        polynomialPilotSquaredCoordinateError theta n omega ≤
      (2 * (polynomialScheduleM n : ℝ) ^ 3) *
        (3 / (polynomialScheduleM n : ℝ) ^ 4) := hproduct
    _ = 6 / (polynomialScheduleM n : ℝ) := by
      field_simp [hmne]
      ring
    _ = polynomialScaledSquaredErrorEnvelope n := rfl

/-- The deterministic `6/m` scaled-error envelope tends to zero. -/
theorem polynomialScaledSquaredErrorEnvelope_tendsto_zero :
    Tendsto polynomialScaledSquaredErrorEnvelope atTop (nhds 0) := by
  have hinv :
      Tendsto
        (fun n : ℕ => (polynomialScheduleM n : ℝ)⁻¹)
        atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp polynomialScheduleMReal_tendsto
  have hmul :
      Tendsto
        (fun n : ℕ => (6 : ℝ) * (polynomialScheduleM n : ℝ)⁻¹)
        atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hinv
  change Tendsto
    (fun n : ℕ => 6 / (polynomialScheduleM n : ℝ)) atTop (nhds 0)
  simpa only [div_eq_mul_inv] using hmul

/-- Along any sequence of outcomes lying in every scheduled good event,
`sqrt(totalShots)` times the squared three-coordinate pilot error tends to zero. -/
theorem polynomialPilot_scaledSquaredError_tendsto_zero_on_good
    (theta : RLSVector 3)
    (omega : ℕ → PauliPilotConsistencySampleSpace)
    (hgood : ∀ n : ℕ, omega n ∉ polynomialPilotBadEvent theta n) :
    Tendsto
      (fun n : ℕ =>
        Real.sqrt (polynomialTotalShots n : ℝ) *
          polynomialPilotSquaredCoordinateError theta n (omega n))
      atTop (nhds 0) := by
  exact Tendsto.squeeze tendsto_const_nhds
    polynomialScaledSquaredErrorEnvelope_tendsto_zero
    (fun n => mul_nonneg (Real.sqrt_nonneg _)
      (polynomialPilotSquaredCoordinateError_nonneg theta n (omega n)))
    (fun n => polynomialPilot_scaledSquaredError_le_on_good
      theta n (omega n) (hgood n))

end QubitOracle.Paper
