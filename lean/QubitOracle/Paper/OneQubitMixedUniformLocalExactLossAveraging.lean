import QubitOracle.Paper.OneQubitMixedUniformLocalQuadraticTransfer

namespace QubitOracle.Paper

noncomputable section

open Filter MeasureTheory

local instance mixedUniformExactLossConsistencyPathMeasurableSpace (q : ℕ) :
    MeasurableSpace (PauliPilotPath q) :=
  pauliPilotConsistencyPathMeasurableSpace q

/-- Cylinder measurability of the scheduled pilot bad event under the explicit
finite-path measurable-space instance used by this module. -/
theorem mixedUniformPolynomialPilotBadEvent_measurable
    (theta : RLSVector 3) (n : ℕ) :
    MeasurableSet (polynomialPilotBadEvent theta n) := by
  let E : Set (PauliPilotPath (Nat.succ (polynomialPilotIndex n))) :=
    {path | ∃ j : Fin 3,
      polynomialPilotThreshold n ≤ |pauliPilotEstimate path j - theta j|}
  have hE : MeasurableSet E := MeasurableSet.of_discrete
  have hEval : Measurable
      (fun omega : PauliPilotConsistencySampleSpace =>
        omega (polynomialPilotIndex n)) :=
    measurable_pi_apply _
  have hPreimage : MeasurableSet
      ((fun omega : PauliPilotConsistencySampleSpace =>
        omega (polynomialPilotIndex n)) ⁻¹' E) :=
    hEval hE
  simpa [E, polynomialPilotBadEvent, QubitOracle.coordinateDeltaBadEvent,
    polynomialPilotEstimator, pauliPilotConsistencyEstimator] using hPreimage

/-- A measurable good/bad split for nonnegative integrals over a probability
measure.  No measurability of the integrand is needed. -/
theorem lintegral_le_const_add_const_mul_measure_of_good
    {alpha : Type*} [MeasurableSpace alpha]
    (mu : Measure alpha) [IsProbabilityMeasure mu]
    (bad : Set alpha) (hBadMeasurable : MeasurableSet bad)
    (f : alpha → ENNReal) (goodBound globalBound : ENNReal)
    (hGood : ∀ x, x ∉ bad → f x ≤ goodBound)
    (hGlobal : ∀ x, f x ≤ globalBound) :
    (∫⁻ x, f x ∂mu) ≤ goodBound + globalBound * mu bad := by
  rw [← lintegral_add_compl f hBadMeasurable]
  have hBadIntegral :
      (∫⁻ x in bad, f x ∂mu) ≤ globalBound * mu bad := by
    calc
      (∫⁻ x in bad, f x ∂mu) ≤
          ∫⁻ _x in bad, globalBound ∂mu :=
        setLIntegral_mono' hBadMeasurable (fun x _hx => hGlobal x)
      _ = globalBound * mu bad := by simp [hBadMeasurable]
  have hGoodIntegral :
      (∫⁻ x in badᶜ, f x ∂mu) ≤ goodBound := by
    calc
      (∫⁻ x in badᶜ, f x ∂mu) ≤
          ∫⁻ _x in badᶜ, goodBound ∂mu := by
        apply setLIntegral_mono' hBadMeasurable.compl
        intro x hx
        exact hGood x (by simpa using hx)
      _ ≤ ∫⁻ _x, goodBound ∂mu :=
        setLIntegral_le_lintegral badᶜ (fun _x => goodBound)
      _ = goodBound := by simp
  calc
    (∫⁻ x in bad, f x ∂mu) + ∫⁻ x in badᶜ, f x ∂mu ≤
        globalBound * mu bad + goodBound :=
      add_le_add hBadIntegral hGoodIntegral
    _ = goodBound + globalBound * mu bad := add_comm _ _

/-- On every good pilot outcome, safeguarded squared-Bures risk at the actual
local truth is uniformly below the oracle value. -/
theorem mixedExactCycleLocalPolynomialGood_uniform_exactBuresRisk
    (b theta : RLSVector 3) (H epsilon : ℝ)
    (hH : 0 ≤ H)
    (hPositive : 0 < QubitOracle.blochNormSq theta)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ n in atTop,
      ∀ h : RLSVector 3, MixedLocalDirectionBall H h →
      ∀ omega : PauliPilotConsistencySampleSpace,
        MixedExactCycleLocalPolynomialPilotGood theta n h omega →
          mixedFrameConditionalScaledSafeguardedBuresRisk
              (q := mixedUniformLocalExactCycleQFinal n)
              (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h)
              (mixedPilotSelectedLocalFrame b
                (polynomialPilotEstimator n omega)) <
            9 / 4 + epsilon := by
  have hHalf : 0 < epsilon / 2 := by linarith
  have hQuadratic :=
    mixedExactCycleLocalPolynomialGood_uniform_localQuadraticRisk
      b theta H (epsilon / 2) hH hPositive hInterior hSeed hHalf
  have hRate :=
    mixedExactCycleLocal_uniform_BuresTransferRate_tendsto_zero
      theta H hInterior (epsilon / 2) hHalf
  have hMargin :=
    mixedExactCycleLocal_uniform_remainder_margin theta H hInterior
  filter_upwards [hQuadratic, hRate, hMargin] with
      n hQuadraticN hRateN hMarginN
  intro h hBall omega hGood
  let z := mixedLocalAlternative theta mixedUniformLocalExactCycleN n h
  let R := mixedPilotSelectedLocalFrame b (polynomialPilotEstimator n omega)
  have hR : MixedFrameOrthonormal R :=
    mixedPilotSelectedLocalFrame_orthonormal _ _
  have hLocalInterior : QubitOracle.blochNormSq z < 1 := by
    have := (hMarginN h hBall).2
    dsimp [z]
    linarith
  have hTransfer :=
    mixedFrameConditionalScaledSafeguardedBuresRisk_transfer
      (mixedUniformLocalExactCycleQFinal_pos n) z hLocalInterior R hR
  have hQuadraticGood := hQuadraticN h hBall omega hGood
  have hRateSmall := hRateN h hBall
  rw [abs_le] at hTransfer
  dsimp [z, R] at hTransfer hQuadraticGood ⊢
  linarith

/-- The same good-outcome statement for ordinary infidelity. -/
theorem mixedExactCycleLocalPolynomialGood_uniform_ordinaryInfidelityRisk
    (b theta : RLSVector 3) (H epsilon : ℝ)
    (hH : 0 ≤ H)
    (hPositive : 0 < QubitOracle.blochNormSq theta)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ n in atTop,
      ∀ h : RLSVector 3, MixedLocalDirectionBall H h →
      ∀ omega : PauliPilotConsistencySampleSpace,
        MixedExactCycleLocalPolynomialPilotGood theta n h omega →
          mixedFrameConditionalScaledOrdinaryInfidelityRisk
              (q := mixedUniformLocalExactCycleQFinal n)
              (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h)
              (mixedPilotSelectedLocalFrame b
                (polynomialPilotEstimator n omega)) <
            9 / 4 + epsilon := by
  have hHalf : 0 < epsilon / 2 := by linarith
  have hTwice : 0 < 2 * epsilon := by positivity
  have hBures :=
    mixedExactCycleLocalPolynomialGood_uniform_exactBuresRisk
      b theta H (epsilon / 2) hH hPositive hInterior hSeed hHalf
  have hSecond :=
    mixedExactCycleLocal_uniform_BuresSecondMomentRate_tendsto_zero
      theta H hInterior (2 * epsilon) hTwice
  have hMargin :=
    mixedExactCycleLocal_uniform_remainder_margin theta H hInterior
  filter_upwards [hBures, hSecond, hMargin] with
      n hBuresN hSecondN hMarginN
  intro h hBall omega hGood
  let z := mixedLocalAlternative theta mixedUniformLocalExactCycleN n h
  let R := mixedPilotSelectedLocalFrame b (polynomialPilotEstimator n omega)
  have hR : MixedFrameOrthonormal R :=
    mixedPilotSelectedLocalFrame_orthonormal _ _
  have hLocalInterior : QubitOracle.blochNormSq z < 1 := by
    have := (hMarginN h hBall).2
    dsimp [z]
    linarith
  have hPhysical : PauliPilotPhysicalBloch z := by
    simpa [PauliPilotPhysicalBloch, QubitOracle.blochNormSq] using
      le_of_lt hLocalInterior
  have hCorrection :=
    mixedFrameConditionalOrdinaryInfidelity_abs_sub_bures_le
      (mixedUniformLocalExactCycleQFinal_pos n) z hLocalInterior hPhysical R hR
  have hBuresGood := hBuresN h hBall omega hGood
  have hSecondSmall := hSecondN h hBall
  rw [abs_le] at hCorrection
  dsimp [z, R] at hCorrection hBuresGood ⊢
  linarith

/-- A center-only finite constant uniformly bounds every local conditional
quadratic risk for all sufficiently large rows. -/
noncomputable def mixedExactCycleUniformQuadraticRiskBound
    (theta : RLSVector 3) : ℝ :=
  mixedInteriorFrameScaledQuadraticRiskBound theta + 1

theorem mixedExactCycleUniformQuadraticRiskBound_nonnegative
    (theta : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1) :
    0 ≤ mixedExactCycleUniformQuadraticRiskBound theta := by
  unfold mixedExactCycleUniformQuadraticRiskBound
  have h := mixedInteriorFrameScaledQuadraticRiskBound_nonnegative
    theta hInterior
  linarith

theorem mixedExactCycleLocal_uniform_quadraticRisk_globalBound
    (theta : RLSVector 3) (H : ℝ)
    (hH : 0 ≤ H)
    (hInterior : QubitOracle.blochNormSq theta < 1) :
    ∀ᶠ n in atTop,
      ∀ h : RLSVector 3, MixedLocalDirectionBall H h →
      ∀ R : Matrix (Fin 3) (Fin 3) ℝ, MixedFrameOrthonormal R →
        mixedFrameConditionalScaledQuadraticRisk
            (q := mixedUniformLocalExactCycleQFinal n)
            (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h) R ≤
          mixedExactCycleUniformQuadraticRiskBound theta := by
  have hTransfer :=
    mixedExactCycleLocal_uniform_quadraticRisk_transfer
      theta H 1 hH hInterior (by norm_num)
  filter_upwards [hTransfer] with n hTransferN
  intro h hBall R hR
  have hCenter := mixedFrameConditionalScaledQuadraticRisk_le_interiorBound
    (mixedUniformLocalExactCycleQFinal_pos n) theta hInterior R hR
  have hLocal := hTransferN h hBall R hR
  rw [abs_lt] at hLocal
  unfold mixedExactCycleUniformQuadraticRiskBound
  linarith

/-- The uniform Hoeffding contract makes every fixed finite multiple of the
local pilot bad-event probability vanish. -/
theorem mixedExactCycleLocalPilot_badContribution_uniform
    (theta : RLSVector 3) (H C epsilon : ℝ)
    (hC : 0 ≤ C)
    (hHoeffding : MixedExactCycleUniformFiniteHoeffdingContract theta H)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ n in atTop, ∀ h : RLSVector 3,
      MixedLocalDirectionBall H h →
        ENNReal.ofReal C *
            (pauliPilotConsistencyMeasure
              (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h))
              (polynomialPilotBadEvent
                (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h) n) <
          ENNReal.ofReal epsilon := by
  let factor : ENNReal := ENNReal.ofReal C + 1
  have hFactorZero : factor ≠ 0 := by
    dsimp [factor]
    simp
  have hFactorTop : factor ≠ ⊤ := by
    dsimp [factor]
    simp
  have hEpsilonENN : 0 < ENNReal.ofReal epsilon :=
    ENNReal.ofReal_pos.mpr hepsilon
  have hThreshold : 0 < ENNReal.ofReal epsilon / factor :=
    ENNReal.div_pos hEpsilonENN.ne' hFactorTop
  have hBad := mixedExactCycleLocalPilot_scaledBadProbability_uniform
    theta H hHoeffding (ENNReal.ofReal epsilon / factor) hThreshold
  filter_upwards [hBad] with n hBadN
  intro h hBall
  let probability :=
    (pauliPilotConsistencyMeasure
      (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h))
      (polynomialPilotBadEvent
        (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h) n)
  have hNPositive : 0 < mixedUniformLocalExactCycleN n := by
    rw [mixedUniformLocalExactCycleN_eq]
    unfold polynomialScheduleM
    positivity
  have hProbabilityScaled :
      probability ≤ (mixedUniformLocalExactCycleN n : ENNReal) * probability := by
    calc
      probability = 1 * probability := by simp
      _ ≤ (mixedUniformLocalExactCycleN n : ENNReal) * probability := by
        gcongr
        exact_mod_cast hNPositive
  have hConstant : ENNReal.ofReal C ≤ factor := by
    dsimp [factor]
    exact le_add_right le_rfl
  calc
    ENNReal.ofReal C * probability ≤
        factor * ((mixedUniformLocalExactCycleN n : ENNReal) * probability) :=
      mul_le_mul' hConstant hProbabilityScaled
    _ < factor * (ENNReal.ofReal epsilon / factor) :=
      by
        simpa [probability, mul_comm] using
          ENNReal.mul_lt_mul_left hFactorZero hFactorTop (hBadN h hBall)
    _ = ENNReal.ofReal epsilon :=
      ENNReal.mul_div_cancel hFactorZero hFactorTop

/-- Uniform final-stage expected quadratic risk over every bounded local
direction. -/
theorem mixedExactCycleLocal_uniform_finalStageQuadraticRisk_le
    (b theta : RLSVector 3) (H epsilon : ℝ)
    (hH : 0 ≤ H)
    (hPositive : 0 < QubitOracle.blochNormSq theta)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hHoeffding : MixedExactCycleUniformFiniteHoeffdingContract theta H)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ n in atTop, ∀ h : RLSVector 3,
      MixedLocalDirectionBall H h →
        mixedPolynomialFinalStageExpectedScaledQuadraticRisk
            (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h) b n <
          ENNReal.ofReal (9 / 4 + epsilon) := by
  have hHalf : 0 < epsilon / 2 := by linarith
  have hGood :=
    mixedExactCycleLocalPolynomialGood_uniform_localQuadraticRisk
      b theta H (epsilon / 2) hH hPositive hInterior hSeed hHalf
  have hGlobal :=
    mixedExactCycleLocal_uniform_quadraticRisk_globalBound
      theta H hH hInterior
  have hBad := mixedExactCycleLocalPilot_badContribution_uniform
    theta H (mixedExactCycleUniformQuadraticRiskBound theta) (epsilon / 2)
    (mixedExactCycleUniformQuadraticRiskBound_nonnegative theta hInterior)
    hHoeffding hHalf
  have hMargin :=
    mixedExactCycleLocal_uniform_remainder_margin theta H hInterior
  filter_upwards [hGood, hGlobal, hBad, hMargin] with
      n hGoodN hGlobalN hBadN hMarginN
  intro h hBall
  let z := mixedLocalAlternative theta mixedUniformLocalExactCycleN n h
  let bad := polynomialPilotBadEvent z n
  let f : PauliPilotConsistencySampleSpace → ENNReal := fun omega =>
    ENNReal.ofReal
      (mixedFrameConditionalScaledQuadraticRisk
        (q := mixedUniformLocalExactCycleQFinal n) z
        (mixedPilotSelectedLocalFrame b (polynomialPilotEstimator n omega)))
  have hLocalInterior : QubitOracle.blochNormSq z < 1 := by
    have := (hMarginN h hBall).2
    dsimp [z]
    linarith
  have hPhysical : PauliPilotPhysicalBloch z := by
    simpa [PauliPilotPhysicalBloch, QubitOracle.blochNormSq] using
      le_of_lt hLocalInterior
  letI : IsProbabilityMeasure (pauliPilotConsistencyMeasure z) :=
    pauliPilotConsistencyMeasure_isProbability z hPhysical
  have hSplit := lintegral_le_const_add_const_mul_measure_of_good
    (pauliPilotConsistencyMeasure z) bad
    (by simpa [bad] using mixedUniformPolynomialPilotBadEvent_measurable z n)
    f (ENNReal.ofReal (9 / 4 + epsilon / 2))
    (ENNReal.ofReal (mixedExactCycleUniformQuadraticRiskBound theta))
    (fun omega hOmega => by
      apply ENNReal.ofReal_le_ofReal
      exact le_of_lt (hGoodN h hBall omega (by
        simpa [MixedExactCycleLocalPolynomialPilotGood, bad, z] using hOmega)))
    (fun omega => by
      apply ENNReal.ofReal_le_ofReal
      exact hGlobalN h hBall
        (mixedPilotSelectedLocalFrame b (polynomialPilotEstimator n omega))
        (mixedPilotSelectedLocalFrame_orthonormal _ _))
  have hIntegral :
      (∫⁻ omega, f omega ∂pauliPilotConsistencyMeasure z) <
        ENNReal.ofReal (9 / 4 + epsilon) := by
    calc
      (∫⁻ omega, f omega ∂pauliPilotConsistencyMeasure z) ≤
          ENNReal.ofReal (9 / 4 + epsilon / 2) +
            ENNReal.ofReal (mixedExactCycleUniformQuadraticRiskBound theta) *
              (pauliPilotConsistencyMeasure z) bad := hSplit
      _ < ENNReal.ofReal (9 / 4 + epsilon / 2) +
            ENNReal.ofReal (epsilon / 2) :=
        ENNReal.add_lt_add_left (by simp) (hBadN h hBall)
      _ = ENNReal.ofReal (9 / 4 + epsilon) := by
        rw [← ENNReal.ofReal_add (by linarith :
          0 ≤ (9 / 4 : ℝ) + epsilon / 2) (le_of_lt hHalf)]
        congr 1
        ring
  change mixedPolynomialFinitePilotAverageScaledRisk
      z b mixedPolynomialQuadraticQFinal n <
    ENNReal.ofReal (9 / 4 + epsilon)
  rw [mixedPolynomialFinitePilotAverageScaledRisk_eq_lintegral
    z b mixedPolynomialQuadraticQFinal hPhysical n]
  simpa [f, z, mixedPolynomialPilotConditionalScaledLoss] using hIntegral

/-- Finite pilot expectation preserves a uniform absolute-difference bound. -/
theorem pauliPilotFiniteExpectation_abs_sub_le_const_uniform
    {q : ℕ} (theta : RLSVector 3)
    (hPhysical : PauliPilotPhysicalBloch theta)
    (f g : PauliPilotPath q → ℝ) (c : ℝ)
    (hPointwise : ∀ pilot, |f pilot - g pilot| ≤ c) :
    |pauliPilotFiniteExpectation theta f -
        pauliPilotFiniteExpectation theta g| ≤ c := by
  unfold pauliPilotFiniteExpectation
  rw [← Finset.sum_sub_distrib]
  have hRewrite :
      (∑ pilot : PauliPilotPath q,
        (pauliPilotPathMass theta pilot * f pilot -
          pauliPilotPathMass theta pilot * g pilot)) =
        ∑ pilot : PauliPilotPath q,
          pauliPilotPathMass theta pilot * (f pilot - g pilot) := by
    apply Finset.sum_congr rfl
    intro pilot _hpilot
    ring
  rw [hRewrite]
  calc
    |∑ pilot : PauliPilotPath q,
      pauliPilotPathMass theta pilot * (f pilot - g pilot)| ≤
        ∑ pilot : PauliPilotPath q,
          |pauliPilotPathMass theta pilot * (f pilot - g pilot)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ pilot : PauliPilotPath q,
        pauliPilotPathMass theta pilot * |f pilot - g pilot| := by
      apply Finset.sum_congr rfl
      intro pilot _hpilot
      rw [abs_mul,
        abs_of_nonneg
          (pauliPilotPathMass_nonnegative theta hPhysical pilot)]
    _ ≤ ∑ pilot : PauliPilotPath q,
        pauliPilotPathMass theta pilot * c := by
      exact Finset.sum_le_sum fun pilot _ =>
        mul_le_mul_of_nonneg_left (hPointwise pilot)
          (pauliPilotPathMass_nonnegative theta hPhysical pilot)
    _ = c := by
      rw [← Finset.sum_mul, pauliPilotPathMass_sum_one]
      ring

/-- Uniform final-stage safeguarded squared-Bures risk. -/
theorem mixedExactCycleLocal_uniform_finalStageExactBuresRisk_le
    (b theta : RLSVector 3) (H epsilon : ℝ)
    (hH : 0 ≤ H)
    (hPositive : 0 < QubitOracle.blochNormSq theta)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hHoeffding : MixedExactCycleUniformFiniteHoeffdingContract theta H)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ n in atTop, ∀ h : RLSVector 3,
      MixedLocalDirectionBall H h →
        mixedPolynomialFinalStageExpectedScaledExactBuresRisk
            (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h) b n <
          ENNReal.ofReal (9 / 4 + epsilon) := by
  have hHalf : 0 < epsilon / 2 := by linarith
  have hQuadratic :=
    mixedExactCycleLocal_uniform_finalStageQuadraticRisk_le
      b theta H (epsilon / 2) hH hPositive hInterior hSeed hHoeffding hHalf
  have hRate :=
    mixedExactCycleLocal_uniform_BuresTransferRate_tendsto_zero
      theta H hInterior (epsilon / 2) hHalf
  have hMargin :=
    mixedExactCycleLocal_uniform_remainder_margin theta H hInterior
  filter_upwards [hQuadratic, hRate, hMargin] with
      n hQuadraticN hRateN hMarginN
  intro h hBall
  let z := mixedLocalAlternative theta mixedUniformLocalExactCycleN n h
  have hLocalInterior : QubitOracle.blochNormSq z < 1 := by
    have := (hMarginN h hBall).2
    dsimp [z]
    linarith
  have hPhysical : PauliPilotPhysicalBloch z := by
    simpa [PauliPilotPhysicalBloch, QubitOracle.blochNormSq] using
      le_of_lt hLocalInterior
  have hQuadraticENN := hQuadraticN h hBall
  rw [mixedPolynomialFinalStageExpectedScaledQuadraticRisk_eq_ofReal_real
    z b hLocalInterior hPhysical n] at hQuadraticENN
  have hQuadraticReal :
      mixedPolynomialFinalStageExpectedScaledQuadraticRiskReal z b n <
        9 / 4 + epsilon / 2 := by
    rw [ENNReal.ofReal_lt_ofReal_iff (by linarith :
      0 < (9 / 4 : ℝ) + epsilon / 2)] at hQuadraticENN
    exact hQuadraticENN
  have hDifference := mixedPolynomialFinalStageExactBures_abs_sub_quadraticReal_le
    z b hLocalInterior hPhysical n
  have hRateSmall := hRateN h hBall
  have hExactReal :
      mixedPolynomialFinalStageExpectedScaledExactBuresRiskReal z b n <
        9 / 4 + epsilon := by
    rw [abs_le] at hDifference
    linarith
  unfold mixedPolynomialFinalStageExpectedScaledExactBuresRisk
  rw [ENNReal.ofReal_lt_ofReal_iff (by linarith :
    0 < (9 / 4 : ℝ) + epsilon)]
  exact hExactReal

/-- Finite-pilot ordinary-infidelity and safeguarded squared-Bures averages
differ by at most the frame-uniform second-moment rate. -/
theorem mixedPolynomialFinalStageOrdinaryInfidelity_abs_sub_exactBuresReal_le
    (theta b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hPhysical : PauliPilotPhysicalBloch theta) (n : ℕ) :
    |mixedPolynomialFinalStageExpectedScaledOrdinaryInfidelityRiskReal theta b n -
      mixedPolynomialFinalStageExpectedScaledExactBuresRiskReal theta b n| ≤
        mixedFrameScaledBuresSecondMomentRate theta
          (mixedPolynomialQuadraticQFinal n) / 4 := by
  rw [mixedPolynomialFinalStageExpectedScaledOrdinaryInfidelityRiskReal_eq_pilotAverage
      theta b hPhysical n,
    mixedPolynomialFinalStageExpectedScaledExactBuresRiskReal_eq_pilotAverage]
  exact pauliPilotFiniteExpectation_abs_sub_le_const_uniform
    theta hPhysical _ _ _ (fun pilot =>
      mixedFrameConditionalOrdinaryInfidelity_abs_sub_bures_le
        (mixedPolynomialQuadraticQFinal_pos n) theta hInterior hPhysical
        (mixedPilotSelectedLocalFrame b (pauliPilotEstimate pilot))
        (mixedPilotSelectedLocalFrame_orthonormal _ _))

/-- Uniform final-stage ordinary-infidelity risk. -/
theorem mixedExactCycleLocal_uniform_finalStageOrdinaryInfidelityRisk_le
    (b theta : RLSVector 3) (H epsilon : ℝ)
    (hH : 0 ≤ H)
    (hPositive : 0 < QubitOracle.blochNormSq theta)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hHoeffding : MixedExactCycleUniformFiniteHoeffdingContract theta H)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ n in atTop, ∀ h : RLSVector 3,
      MixedLocalDirectionBall H h →
        mixedPolynomialFinalStageExpectedScaledOrdinaryInfidelityRisk
            (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h) b n <
          ENNReal.ofReal (9 / 4 + epsilon) := by
  have hHalf : 0 < epsilon / 2 := by linarith
  have hTwice : 0 < 2 * epsilon := by positivity
  have hBures :=
    mixedExactCycleLocal_uniform_finalStageExactBuresRisk_le
      b theta H (epsilon / 2) hH hPositive hInterior hSeed hHoeffding hHalf
  have hSecond :=
    mixedExactCycleLocal_uniform_BuresSecondMomentRate_tendsto_zero
      theta H hInterior (2 * epsilon) hTwice
  have hMargin :=
    mixedExactCycleLocal_uniform_remainder_margin theta H hInterior
  filter_upwards [hBures, hSecond, hMargin] with
      n hBuresN hSecondN hMarginN
  intro h hBall
  let z := mixedLocalAlternative theta mixedUniformLocalExactCycleN n h
  have hLocalInterior : QubitOracle.blochNormSq z < 1 := by
    have := (hMarginN h hBall).2
    dsimp [z]
    linarith
  have hPhysical : PauliPilotPhysicalBloch z := by
    simpa [PauliPilotPhysicalBloch, QubitOracle.blochNormSq] using
      le_of_lt hLocalInterior
  have hBuresENN := hBuresN h hBall
  unfold mixedPolynomialFinalStageExpectedScaledExactBuresRisk at hBuresENN
  have hBuresReal :
      mixedPolynomialFinalStageExpectedScaledExactBuresRiskReal z b n <
        9 / 4 + epsilon / 2 := by
    rw [ENNReal.ofReal_lt_ofReal_iff (by linarith :
      0 < (9 / 4 : ℝ) + epsilon / 2)] at hBuresENN
    exact hBuresENN
  have hDifference :=
    mixedPolynomialFinalStageOrdinaryInfidelity_abs_sub_exactBuresReal_le
      z b hLocalInterior hPhysical n
  have hSecondSmall := hSecondN h hBall
  have hOrdinaryReal :
      mixedPolynomialFinalStageExpectedScaledOrdinaryInfidelityRiskReal z b n <
        9 / 4 + epsilon := by
    rw [abs_le] at hDifference
    linarith
  unfold mixedPolynomialFinalStageExpectedScaledOrdinaryInfidelityRisk
  rw [ENNReal.ofReal_lt_ofReal_iff (by linarith :
    0 < (9 / 4 : ℝ) + epsilon)]
  exact hOrdinaryReal

/-- Both exact losses satisfy the uniform total-observation-scaled upper
bound. -/
theorem mixedExactCycleLocal_uniform_totalExactRisk_le
    (b theta : RLSVector 3) (H epsilon : ℝ)
    (hH : 0 ≤ H)
    (hPositive : 0 < QubitOracle.blochNormSq theta)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hHoeffding : MixedExactCycleUniformFiniteHoeffdingContract theta H)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ n in atTop, ∀ loss : MixedUniformLocalExactLoss,
      ∀ h : RLSVector 3, MixedLocalDirectionBall H h →
        mixedUniformLocalTotalScaledExactRisk loss
            (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h) b n <
          ENNReal.ofReal (9 / 4 + epsilon) := by
  let A : ℝ := 9 / 4 + epsilon / 2
  let delta : ℝ := (epsilon / 2) / A
  have hA : 0 < A := by dsimp [A]; linarith
  have hDelta : 0 < delta := by dsimp [delta]; positivity
  have hHalf : 0 < epsilon / 2 := by linarith
  have hBures :=
    mixedExactCycleLocal_uniform_finalStageExactBuresRisk_le
      b theta H (epsilon / 2) hH hPositive hInterior hSeed hHoeffding hHalf
  have hOrdinary :=
    mixedExactCycleLocal_uniform_finalStageOrdinaryInfidelityRisk_le
      b theta H (epsilon / 2) hH hPositive hInterior hSeed hHoeffding hHalf
  have hRatio : ∀ᶠ n in atTop,
      mixedPolynomialExactCycleTotalToFinalRatio n < 1 + delta :=
    (tendsto_order.1 mixedPolynomialExactCycleTotalToFinalRatio_tendsto_one).2
      (1 + delta) (by linarith)
  filter_upwards [hBures, hOrdinary, hRatio] with
      n hBuresN hOrdinaryN hRatioN
  intro loss h hBall
  have hFactorPos : 0 < ENNReal.ofReal (1 + delta) :=
    ENNReal.ofReal_pos.mpr (by linarith)
  have hFactorTop : ENNReal.ofReal (1 + delta) ≠ ⊤ := by simp
  have hProduct : ∀ finalRisk : ENNReal,
      finalRisk < ENNReal.ofReal A →
      ENNReal.ofReal (mixedPolynomialExactCycleTotalToFinalRatio n) * finalRisk <
        ENNReal.ofReal (9 / 4 + epsilon) := by
    intro finalRisk hFinal
    calc
      ENNReal.ofReal (mixedPolynomialExactCycleTotalToFinalRatio n) * finalRisk ≤
          ENNReal.ofReal (1 + delta) * finalRisk := by
        simpa [mul_comm] using
          mul_le_mul_right
            (ENNReal.ofReal_le_ofReal (le_of_lt hRatioN)) finalRisk
      _ < ENNReal.ofReal (1 + delta) * ENNReal.ofReal A := by
        simpa [mul_comm] using
          ENNReal.mul_lt_mul_left hFactorPos.ne' hFactorTop hFinal
      _ = ENNReal.ofReal (9 / 4 + epsilon) := by
        rw [← ENNReal.ofReal_mul (by linarith : 0 ≤ 1 + delta)]
        congr 1
        dsimp [delta, A]
        field_simp [ne_of_gt hA]
        ring
  cases loss with
  | squaredBures =>
      unfold mixedUniformLocalTotalScaledExactRisk
        mixedPolynomialTotalObservationScaledExpectedExactBuresRisk
      exact hProduct _ (by simpa [A] using hBuresN h hBall)
  | ordinaryInfidelity =>
      unfold mixedUniformLocalTotalScaledExactRisk
        mixedPolynomialTotalObservationScaledExpectedOrdinaryInfidelityRisk
      exact hProduct _ (by simpa [A] using hOrdinaryN h hBall)

/-- The former exact-loss averaging contract is now a theorem under the
explicit uniform finite Hoeffding condition. -/
theorem mixedExactCycleUniformExactLossAveragingBridge_closed
    (b theta : RLSVector 3) (H : ℝ)
    (hH : 0 ≤ H)
    (hPositive : 0 < QubitOracle.blochNormSq theta)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hHoeffding : MixedExactCycleUniformFiniteHoeffdingContract theta H) :
    MixedExactCycleUniformExactLossAveragingBridge theta b H := by
  intro epsilon hepsilon _hFrozenCenter
  have hTotal := mixedExactCycleLocal_uniform_totalExactRisk_le
    b theta H (2 * epsilon) hH hPositive hInterior hSeed hHoeffding
      (by positivity)
  filter_upwards [hTotal] with n hTotalN
  intro loss h hBall
  exact le_of_lt (by simpa [mul_assoc] using hTotalN loss h hBall)

/-- Fully closed non-LAN probability-envelope endpoint for the concrete
mixed-qubit exact-cycle protocol. -/
theorem mixedUniformLocalProbabilityEnvelope_exactCycle_closed
    (theta b : RLSVector 3) (H : ℝ)
    (hH : 0 ≤ H)
    (hPositive : 0 < QubitOracle.blochNormSq theta)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hHoeffding : MixedExactCycleUniformFiniteHoeffdingContract theta H) :
    MixedUniformLocalProbabilityEnvelope theta b
      mixedUniformLocalExactCycleN H mixedUniformLocalExactCycleQFinal :=
  mixedUniformLocalProbabilityEnvelope_exactCycle_reduction
    theta b H hH hPositive hInterior hSeed
      (mixedExactCycleUniformExactLossAveragingBridge_closed
        b theta H hH hPositive hInterior hSeed hHoeffding)

end

end QubitOracle.Paper
