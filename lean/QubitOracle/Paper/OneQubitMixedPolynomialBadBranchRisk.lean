import QubitOracle.Paper.OneQubitPolynomialTwoStageSchedule
import QubitOracle.Paper.OneQubitMixedGoodBranchUniformEnvelopeClosed

/-!
# Mixed-qubit polynomial bad-branch risk

The concrete schedule has `m = n + 1`, at most `4 * m^6` total shots, and
pilot bad-event envelope `6 * exp (-m / 2)`.  The seventh Taylor term of the
exponential gives an explicit reciprocal majorant, so total shots times the
bad-event envelope tends to zero.

The second part controls a set `lintegral` for any fixed-bounded nonnegative
loss.  The final theorem packages this bad-branch estimate together with the
already closed uniform good-branch envelope.  It does not identify that package
with an adaptive estimator law.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace QubitOracle.Paper

noncomputable section

/-- The seventh Taylor term gives the explicit degree-six exponential bound
`m^6 exp(-m/2) ≤ 645120/m` for the positive schedule parameter `m`. -/
theorem polynomialSchedule_pow_six_mul_exp_neg_half_le (n : ℕ) :
    (polynomialScheduleM n : ℝ) ^ 6 *
        Real.exp (-((polynomialScheduleM n : ℝ) / 2)) ≤
      645120 / (polynomialScheduleM n : ℝ) := by
  let m : ℝ := polynomialScheduleM n
  have hm : 0 < m := by
    dsimp [m, polynomialScheduleM]
    positivity
  have hmne : m ≠ 0 := ne_of_gt hm
  have hTaylor :
      (m / 2) ^ 7 / (Nat.factorial 7 : ℝ) ≤ Real.exp (m / 2) :=
    Real.pow_div_factorial_le_exp (m / 2) (by positivity) 7
  have hTaylorTermPos :
      0 < (m / 2) ^ 7 / (Nat.factorial 7 : ℝ) := by
    positivity
  have hExpNeg :
      Real.exp (-(m / 2)) ≤ 645120 / m ^ 7 := by
    calc
      Real.exp (-(m / 2)) = 1 / Real.exp (m / 2) := by
        rw [Real.exp_neg, one_div]
      _ ≤ 1 / ((m / 2) ^ 7 / (Nat.factorial 7 : ℝ)) :=
        one_div_le_one_div_of_le hTaylorTermPos hTaylor
      _ = 645120 / m ^ 7 := by
        norm_num [Nat.factorial]
        field_simp [hmne]
        ring
  change m ^ 6 * Real.exp (-(m / 2)) ≤ 645120 / m
  calc
    m ^ 6 * Real.exp (-(m / 2)) ≤
        m ^ 6 * (645120 / m ^ 7) :=
      mul_le_mul_of_nonneg_left hExpNeg (by positivity)
    _ = 645120 / m := by
      field_simp [hmne]

/-- Real-valued form of total shots times the explicit scheduled bad-event
envelope. -/
def polynomialTotalShotsBadEventEnvelopeReal (n : ℕ) : ℝ :=
  (polynomialTotalShots n : ℝ) *
    (6 * Real.exp (-((polynomialScheduleM n : ℝ) / 2)))

/-- Explicit `O(1/m)` majorant for total shots times the bad-event envelope. -/
theorem polynomialTotalShotsBadEventEnvelopeReal_le (n : ℕ) :
    polynomialTotalShotsBadEventEnvelopeReal n ≤
      2580480 * polynomialScaledSquaredErrorEnvelope n := by
  have hshots :
      (polynomialTotalShots n : ℝ) ≤
        4 * (polynomialScheduleM n : ℝ) ^ 6 := by
    exact_mod_cast polynomialTotalShots_le_four_mul_m_pow_six n
  have hdecay := polynomialSchedule_pow_six_mul_exp_neg_half_le n
  unfold polynomialTotalShotsBadEventEnvelopeReal
  calc
    (polynomialTotalShots n : ℝ) *
        (6 * Real.exp (-((polynomialScheduleM n : ℝ) / 2))) ≤
      (4 * (polynomialScheduleM n : ℝ) ^ 6) *
        (6 * Real.exp (-((polynomialScheduleM n : ℝ) / 2))) :=
      mul_le_mul_of_nonneg_right hshots (by positivity)
    _ = 24 * ((polynomialScheduleM n : ℝ) ^ 6 *
        Real.exp (-((polynomialScheduleM n : ℝ) / 2))) := by ring
    _ ≤ 24 * (645120 / (polynomialScheduleM n : ℝ)) :=
      mul_le_mul_of_nonneg_left hdecay (by norm_num)
    _ = 2580480 * polynomialScaledSquaredErrorEnvelope n := by
      unfold polynomialScaledSquaredErrorEnvelope
      ring

/-- The real total-shot-scaled exponential envelope tends to zero. -/
theorem polynomialTotalShotsBadEventEnvelopeReal_tendsto_zero :
    Tendsto polynomialTotalShotsBadEventEnvelopeReal atTop (nhds 0) := by
  have hmajor :
      Tendsto
        (fun n : ℕ =>
          2580480 * polynomialScaledSquaredErrorEnvelope n)
        atTop (nhds 0) := by
    simpa using
      tendsto_const_nhds.mul polynomialScaledSquaredErrorEnvelope_tendsto_zero
  exact Tendsto.squeeze tendsto_const_nhds hmajor
    (fun n => by
      unfold polynomialTotalShotsBadEventEnvelopeReal
      positivity)
    polynomialTotalShotsBadEventEnvelopeReal_le

/-- The real and `ENNReal` versions of the total-shot-scaled envelope agree. -/
theorem polynomialTotalShotsBadEventEnvelope_ofReal (n : ℕ) :
    ENNReal.ofReal (polynomialTotalShotsBadEventEnvelopeReal n) =
      (polynomialTotalShots n : ℝ≥0∞) *
        polynomialPilotBadEventEnvelope n := by
  unfold polynomialTotalShotsBadEventEnvelopeReal
    polynomialPilotBadEventEnvelope
  rw [ENNReal.ofReal_mul (by positivity)]
  rw [ENNReal.ofReal_mul (by norm_num)]
  norm_num

/-- Total shots times the established exponential pilot bad-event upper bound
tends to zero. -/
theorem polynomialTotalShots_mul_badEventEnvelope_tendsto_zero :
    Tendsto
      (fun n : ℕ =>
        (polynomialTotalShots n : ℝ≥0∞) *
          polynomialPilotBadEventEnvelope n)
      atTop (nhds 0) := by
  have hofReal :
      Tendsto
        (fun n : ℕ =>
          ENNReal.ofReal (polynomialTotalShotsBadEventEnvelopeReal n))
        atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (ENNReal.continuous_ofReal.tendsto 0).comp
        polynomialTotalShotsBadEventEnvelopeReal_tendsto_zero
  apply hofReal.congr'
  filter_upwards with n
  exact polynomialTotalShotsBadEventEnvelope_ofReal n

/-- The simultaneous polynomial pilot bad event is measurable in the common
pilot product space. -/
theorem polynomialPilotBadEvent_measurable
    (theta : RLSVector 3) (n : ℕ) :
    MeasurableSet (polynomialPilotBadEvent theta n) := by
  have hCoordinateEvent (j : Fin 3) :
      MeasurableSet
        {omega : PauliPilotConsistencySampleSpace |
          polynomialPilotThreshold n ≤
            |polynomialPilotEstimator n omega j - theta j|} := by
    let E : Set (PauliPilotPath (Nat.succ (polynomialPilotIndex n))) :=
      {path |
        polynomialPilotThreshold n ≤ |pauliPilotEstimate path j - theta j|}
    have hE : MeasurableSet E := by
      exact MeasurableSet.of_discrete
    have hEval : Measurable
        (fun omega : PauliPilotConsistencySampleSpace =>
          omega (polynomialPilotIndex n)) :=
      measurable_pi_apply _
    have hPreimage : MeasurableSet
        ((fun omega : PauliPilotConsistencySampleSpace =>
          omega (polynomialPilotIndex n)) ⁻¹' E) :=
      hEval hE
    simpa [E, polynomialPilotEstimator, pauliPilotConsistencyEstimator] using
      hPreimage
  unfold polynomialPilotBadEvent QubitOracle.coordinateDeltaBadEvent
  have hUnion :
      {omega : PauliPilotConsistencySampleSpace |
        ∃ j : Fin 3,
          polynomialPilotThreshold n ≤
            |polynomialPilotEstimator n omega j - theta j|} =
        ⋃ j : Fin 3,
          {omega : PauliPilotConsistencySampleSpace |
            polynomialPilotThreshold n ≤
              |polynomialPilotEstimator n omega j - theta j|} := by
    ext omega
    simp
  rw [hUnion]
  exact MeasurableSet.iUnion hCoordinateEvent

/-- Total-shot-scaled expected contribution of a nonnegative loss restricted
to the scheduled pilot bad event. -/
def polynomialMixedBadBranchScaledContribution
    (theta : RLSVector 3)
    (loss : ℕ → PauliPilotConsistencySampleSpace → ℝ≥0∞)
    (n : ℕ) : ℝ≥0∞ :=
  (polynomialTotalShots n : ℝ≥0∞) *
    ∫⁻ omega in polynomialPilotBadEvent theta n,
      loss n omega ∂pauliPilotConsistencyMeasure theta

/-- A fixed pointwise loss bound controls the bad-branch set integral by the
constant times the bad-event probability. -/
theorem polynomialMixedBadBranch_lintegral_le_constant_mul_probability
    (theta : RLSVector 3)
    (loss : ℕ → PauliPilotConsistencySampleSpace → ℝ≥0∞)
    (C : ℝ≥0∞)
    (hLoss : ∀ n omega, loss n omega ≤ C)
    (n : ℕ) :
    (∫⁻ omega in polynomialPilotBadEvent theta n,
        loss n omega ∂pauliPilotConsistencyMeasure theta) ≤
      C * pauliPilotConsistencyMeasure theta
        (polynomialPilotBadEvent theta n) := by
  calc
    (∫⁻ omega in polynomialPilotBadEvent theta n,
        loss n omega ∂pauliPilotConsistencyMeasure theta) ≤
      ∫⁻ _omega in polynomialPilotBadEvent theta n,
        C ∂pauliPilotConsistencyMeasure theta := by
          apply lintegral_mono
          exact fun omega => hLoss n omega
    _ = C * pauliPilotConsistencyMeasure theta
        (polynomialPilotBadEvent theta n) := by
      simp [polynomialPilotBadEvent_measurable theta n]

/-- The concrete Hoeffding bad-event bound dominates every fixed-bounded
bad-branch expected contribution after total-shot scaling. -/
theorem polynomialMixedBadBranchScaledContribution_le
    (theta : RLSVector 3)
    (hphysical : PauliPilotPhysicalBloch theta)
    (hHoeffding : PauliPilotConsistencyHoeffdingContracts theta hphysical)
    (loss : ℕ → PauliPilotConsistencySampleSpace → ℝ≥0∞)
    (C : ℝ≥0∞)
    (hLoss : ∀ n omega, loss n omega ≤ C)
    (n : ℕ) :
    polynomialMixedBadBranchScaledContribution theta loss n ≤
      C * ((polynomialTotalShots n : ℝ≥0∞) *
        polynomialPilotBadEventEnvelope n) := by
  unfold polynomialMixedBadBranchScaledContribution
  calc
    (polynomialTotalShots n : ℝ≥0∞) *
        (∫⁻ omega in polynomialPilotBadEvent theta n,
          loss n omega ∂pauliPilotConsistencyMeasure theta) ≤
      (polynomialTotalShots n : ℝ≥0∞) *
        (C * pauliPilotConsistencyMeasure theta
          (polynomialPilotBadEvent theta n)) :=
      mul_le_mul_of_nonneg_left
        (polynomialMixedBadBranch_lintegral_le_constant_mul_probability
          theta loss C hLoss n) bot_le
    _ ≤ (polynomialTotalShots n : ℝ≥0∞) *
        (C * polynomialPilotBadEventEnvelope n) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (polynomialPilot_badEvent_bound
            theta hphysical hHoeffding n) bot_le) bot_le
    _ = C * ((polynomialTotalShots n : ℝ≥0∞) *
        polynomialPilotBadEventEnvelope n) := by
      ac_rfl

/-- Any fixed finite bound on the nonnegative bad-branch loss makes its
total-shot-scaled expected contribution vanish. -/
theorem polynomialMixedBadBranchScaledContribution_tendsto_zero
    (theta : RLSVector 3)
    (hphysical : PauliPilotPhysicalBloch theta)
    (hHoeffding : PauliPilotConsistencyHoeffdingContracts theta hphysical)
    (loss : ℕ → PauliPilotConsistencySampleSpace → ℝ≥0∞)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hLoss : ∀ n omega, loss n omega ≤ C) :
    Tendsto
      (polynomialMixedBadBranchScaledContribution theta loss)
      atTop (nhds 0) := by
  have hmajor :
      Tendsto
        (fun n : ℕ => C *
          ((polynomialTotalShots n : ℝ≥0∞) *
            polynomialPilotBadEventEnvelope n))
        atTop (nhds 0) := by
    simpa [Function.comp_def] using
      ((ENNReal.continuousAt_const_mul
        (a := C) (b := (0 : ℝ≥0∞)) (Or.inl hC)).tendsto).comp
          polynomialTotalShots_mul_badEventEnvelope_tendsto_zero
  exact Tendsto.squeeze tendsto_const_nhds hmajor
    (fun _ => bot_le)
    (polynomialMixedBadBranchScaledContribution_le
      theta hphysical hHoeffding loss C hLoss)

/-- Exact deterministic package needed before a separate adaptive joint-law
argument: one common good-branch envelope dominates every good outcome, and
that envelope plus the bounded bad-branch expected contribution tends to zero. -/
theorem mixedPolynomialGoodEnvelope_with_badBranchContribution
    (b theta : RLSVector 3) (qFinal : ℕ → ℕ)
    (hqFinal : ∀ n, 0 < qFinal n)
    (hPositive : 0 < QubitOracle.blochNormSq theta)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hphysical : PauliPilotPhysicalBloch theta)
    (hHoeffding : PauliPilotConsistencyHoeffdingContracts theta hphysical)
    (loss : ℕ → PauliPilotConsistencySampleSpace → ℝ≥0∞)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hLoss : ∀ n omega, loss n omega ≤ C) :
    ∃ envelope : ℕ → ℝ≥0∞,
      Tendsto envelope atTop (nhds 0) ∧
      (∀ᶠ n in atTop, ∀ omega : PauliPilotConsistencySampleSpace,
        omega ∉ polynomialPilotBadEvent theta n →
          ENNReal.ofReal
            |mixedFrameConditionalScaledQuadraticRisk (q := qFinal n) theta
                (mixedPilotSelectedLocalFrame b
                  (polynomialPilotEstimator n omega)) - 9 / 4| ≤
            envelope n) ∧
      Tendsto
        (fun n => envelope n +
          polynomialMixedBadBranchScaledContribution theta loss n)
        atTop (nhds 0) := by
  rcases mixedPilotGoodBranchUniformFrameContinuityPremise_closed
      b theta qFinal hqFinal hPositive hInterior hSeed with
    ⟨envelope, hEnvelope, hGood⟩
  have hBad := polynomialMixedBadBranchScaledContribution_tendsto_zero
    theta hphysical hHoeffding loss C hC hLoss
  refine ⟨envelope, hEnvelope, hGood, ?_⟩
  simpa using hEnvelope.add hBad

namespace Label

/-- Paper-facing concrete polynomial good/bad risk-reduction package.  It stops
before identifying an adaptive estimator's expected loss with this package. -/
theorem lem_SI_mixed_polynomial_good_bad_risk_qubit_reduction
    (b theta : RLSVector 3) (qFinal : ℕ → ℕ)
    (hqFinal : ∀ n, 0 < qFinal n)
    (hPositive : 0 < QubitOracle.blochNormSq theta)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hphysical : PauliPilotPhysicalBloch theta)
    (hHoeffding : PauliPilotConsistencyHoeffdingContracts theta hphysical)
    (loss : ℕ → PauliPilotConsistencySampleSpace → ℝ≥0∞)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hLoss : ∀ n omega, loss n omega ≤ C) :
    ∃ envelope : ℕ → ℝ≥0∞,
      Tendsto envelope atTop (nhds 0) ∧
      Tendsto
        (fun n => envelope n +
          polynomialMixedBadBranchScaledContribution theta loss n)
        atTop (nhds 0) := by
  rcases mixedPolynomialGoodEnvelope_with_badBranchContribution
      b theta qFinal hqFinal hPositive hInterior hSeed
      hphysical hHoeffding loss C hC hLoss with
    ⟨envelope, hEnvelope, _hGood, hCombined⟩
  exact ⟨envelope, hEnvelope, hCombined⟩

end Label

end

end QubitOracle.Paper
