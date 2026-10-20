import QubitOracle.Paper.OneQubitPureLinearEstimatorFourthMomentClosed

open Filter MeasureTheory Topology

namespace QubitOracle.Paper.OneQubitPureLinearEstimatorBuresRiskClosed

/-!
# Closing the pure linear-estimator chart-Bures risk

The retained pointwise theorem determines the chart-Bures expression used in
this file.  Packaging that expression with its proof lets us give it a local
name without duplicating or guessing its internal definition.
-/

/-- Named concrete chart-Bures squared loss for the finite linear estimator. -/
noncomputable def pureLinearChartBuresSq
    (q : ℕ)
    (omega :
      QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q) : ℝ :=
  QubitOracle.Paper.pureQubitChartBuresSq
    (QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearEstimator q omega)

theorem pureLinearChartBuresSq_remainder_bounds
    {q : ℕ} (hq : 0 < q)
    (omega :
      QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q) :
    0 ≤
        pureLinearChartBuresSq q omega -
          QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearQuadraticLoss
            q omega ∧
      pureLinearChartBuresSq q omega -
          QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearQuadraticLoss
            q omega ≤
        QubitOracle.Paper.OneQubitPureLinearEstimatorFourthMoment.pureLinearSquaredRadius
            q omega ^ 2 /
          16 := by
  simpa only [pureLinearChartBuresSq,
    QubitOracle.Paper.OneQubitPureLinearEstimatorFourthMoment.pureLinearSquaredRadius,
    QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearEstimator_tangentRadiusSq_eq]
    using
      (QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearChartBuresSq_remainder_bounds
        hq omega)

private theorem measurable_of_fintype_domain
    {Omega Beta : Type*} [MeasurableSpace Omega]
    [MeasurableSingletonClass Omega] [Fintype Omega]
    [MeasurableSpace Beta] (f : Omega → Beta) : Measurable f := by
  exact measurable_of_finite f

private theorem finite_integrable_of_measurable
    {Omega : Type*} [MeasurableSpace Omega]
    [MeasurableSingletonClass Omega] [Finite Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {f : Omega → ℝ} (hf : Measurable f) : Integrable f mu := by
  exact Integrable.of_finite

/-- Expected concrete chart-Bures squared loss. -/
noncomputable def pureLinearExpectedChartBuresSq (q : ℕ) : ℝ :=
  ∫ omega, pureLinearChartBuresSq q omega
    ∂QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q

/-- Expected nonnegative difference between chart-Bures loss and its quadratic
part. -/
noncomputable def pureLinearExpectedChartBuresSqRemainder (q : ℕ) : ℝ :=
  ∫ omega,
      pureLinearChartBuresSq q omega -
        QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearQuadraticLoss
          q omega
    ∂QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q

/-- Total-shot-scaled chart-Bures remainder. -/
noncomputable def pureLinearScaledExpectedChartBuresSqRemainder (q : ℕ) : ℝ :=
  (QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearTotalShots q : ℝ) *
    pureLinearExpectedChartBuresSqRemainder q

/-- Total-shot-scaled expected chart-Bures squared risk. -/
noncomputable def pureLinearScaledExpectedChartBuresSq (q : ℕ) : ℝ :=
  (QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearTotalShots q : ℝ) *
    pureLinearExpectedChartBuresSq q

/-- Integrating the retained pointwise bound gives the exact expected
remainder bounds. -/
theorem pureLinearExpectedChartBuresSqRemainder_bounds
    {q : ℕ} (hq : 0 < q) :
    0 ≤ pureLinearExpectedChartBuresSqRemainder q ∧
      pureLinearExpectedChartBuresSqRemainder q ≤
        ∫ omega,
            QubitOracle.Paper.OneQubitPureLinearEstimatorFourthMoment.pureLinearSquaredRadius
                q omega ^ 2 /
              16
          ∂QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q := by
  let mu :=
    QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q
  let remainder :
      QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q → ℝ :=
    fun omega =>
      pureLinearChartBuresSq q omega -
        QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearQuadraticLoss
          q omega
  let upper :
      QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q → ℝ :=
    fun omega =>
      QubitOracle.Paper.OneQubitPureLinearEstimatorFourthMoment.pureLinearSquaredRadius
          q omega ^ 2 /
        16
  have hRemainderMeasurable : Measurable remainder :=
    measurable_of_fintype_domain remainder
  have hUpperMeasurable : Measurable upper :=
    measurable_of_fintype_domain upper
  have hRemainderIntegrable : Integrable remainder mu :=
    finite_integrable_of_measurable mu hRemainderMeasurable
  have hUpperIntegrable : Integrable upper mu :=
    finite_integrable_of_measurable mu hUpperMeasurable
  have hnonnegative : ∀ᵐ omega ∂mu, 0 ≤ remainder omega :=
    Filter.Eventually.of_forall fun omega =>
      (pureLinearChartBuresSq_remainder_bounds hq omega).1
  have hle : ∀ᵐ omega ∂mu, remainder omega ≤ upper omega :=
    Filter.Eventually.of_forall fun omega =>
      (pureLinearChartBuresSq_remainder_bounds hq omega).2
  constructor
  · simpa only [pureLinearExpectedChartBuresSqRemainder, mu, remainder] using
      integral_nonneg_of_ae hnonnegative
  · simpa only [pureLinearExpectedChartBuresSqRemainder, mu, remainder, upper] using
      integral_mono_ae hRemainderIntegrable hUpperIntegrable hle

private theorem pureLinearScaledRemainderUpper_eq_envelope (q : ℕ) :
    (QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearTotalShots q : ℝ) *
        (∫ omega,
            QubitOracle.Paper.OneQubitPureLinearEstimatorFourthMoment.pureLinearSquaredRadius
                q omega ^ 2 /
              16
          ∂QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q) =
      QubitOracle.Paper.OneQubitPureLinearEstimatorFourthMoment.pureLinearScaledBuresRemainderEnvelope
        q := by
  rw [integral_div]
  simp only [
    QubitOracle.Paper.OneQubitPureLinearEstimatorFourthMoment.pureLinearScaledBuresRemainderEnvelope]
  ring

/-- The concrete scaled expected Bures remainder is squeezed by the closed
fourth-order envelope. -/
theorem pureLinearScaledExpectedChartBuresSqRemainder_bounds
    {q : ℕ} (hq : 0 < q) :
    0 ≤ pureLinearScaledExpectedChartBuresSqRemainder q ∧
      pureLinearScaledExpectedChartBuresSqRemainder q ≤
        QubitOracle.Paper.OneQubitPureLinearEstimatorFourthMoment.pureLinearScaledBuresRemainderEnvelope
          q := by
  have hN :
      0 ≤
        (QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearTotalShots q : ℝ) := by
    positivity
  have hExpected := pureLinearExpectedChartBuresSqRemainder_bounds hq
  constructor
  · exact mul_nonneg hN hExpected.1
  · calc
      pureLinearScaledExpectedChartBuresSqRemainder q ≤
          (QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearTotalShots q : ℝ) *
            (∫ omega,
                QubitOracle.Paper.OneQubitPureLinearEstimatorFourthMoment.pureLinearSquaredRadius
                    q omega ^ 2 /
                  16
              ∂QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q) := by
                exact mul_le_mul_of_nonneg_left hExpected.2 hN
      _ =
          QubitOracle.Paper.OneQubitPureLinearEstimatorFourthMoment.pureLinearScaledBuresRemainderEnvelope
            q := pureLinearScaledRemainderUpper_eq_envelope q

/-- Exact decomposition of scaled chart-Bures risk into the already exact
quadratic value one and the scaled remainder. -/
theorem pureLinearScaledExpectedChartBuresSq_eq_one_add_remainder
    {q : ℕ} (hq : 0 < q) :
    pureLinearScaledExpectedChartBuresSq q =
      1 + pureLinearScaledExpectedChartBuresSqRemainder q := by
  let mu :=
    QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q
  let quadratic :
      QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q → ℝ :=
    QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearQuadraticLoss q
  let remainder :
      QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q → ℝ :=
    fun omega => pureLinearChartBuresSq q omega - quadratic omega
  have hQuadraticMeasurable : Measurable quadratic :=
    measurable_of_fintype_domain quadratic
  have hRemainderMeasurable : Measurable remainder :=
    measurable_of_fintype_domain remainder
  have hQuadraticIntegrable : Integrable quadratic mu :=
    finite_integrable_of_measurable mu hQuadraticMeasurable
  have hRemainderIntegrable : Integrable remainder mu :=
    finite_integrable_of_measurable mu hRemainderMeasurable
  have hintegral :
      pureLinearExpectedChartBuresSq q =
        (∫ omega,
            QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearQuadraticLoss
              q omega
          ∂QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q) +
          pureLinearExpectedChartBuresSqRemainder q := by
    calc
      pureLinearExpectedChartBuresSq q =
          ∫ omega, quadratic omega + remainder omega ∂mu := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun omega => by
              simp only [pureLinearExpectedChartBuresSq, quadratic, remainder, mu]
              ring
      _ = (∫ omega, quadratic omega ∂mu) +
          (∫ omega, remainder omega ∂mu) :=
        integral_add hQuadraticIntegrable hRemainderIntegrable
      _ =
          (∫ omega,
              QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearQuadraticLoss
                q omega
            ∂QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q) +
            pureLinearExpectedChartBuresSqRemainder q := by
              rfl
  calc
    pureLinearScaledExpectedChartBuresSq q =
        (QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearTotalShots q : ℝ) *
          ((∫ omega,
              QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearQuadraticLoss
                q omega
            ∂QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q) +
            pureLinearExpectedChartBuresSqRemainder q) := by
              rw [pureLinearScaledExpectedChartBuresSq, hintegral]
    _ =
        (QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearTotalShots q : ℝ) *
            (∫ omega,
                QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearQuadraticLoss
                  q omega
              ∂QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q) +
          pureLinearScaledExpectedChartBuresSqRemainder q := by
            simp only [pureLinearScaledExpectedChartBuresSqRemainder]
            ring
    _ = 1 + pureLinearScaledExpectedChartBuresSqRemainder q := by
          rw [
            QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearScaledExpectedQuadraticLoss_eq_one
              hq]

/-- The concrete total-shot-scaled expected chart-Bures squared risk converges
unconditionally to the optimal value one. -/
theorem pureLinearScaledExpectedChartBuresSq_tendsto_one :
    Tendsto pureLinearScaledExpectedChartBuresSq atTop (𝓝 1) := by
  have hRemainderNonnegative :
      ∀ᶠ q : ℕ in atTop,
        0 ≤ pureLinearScaledExpectedChartBuresSqRemainder q := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with q hq
    exact (pureLinearScaledExpectedChartBuresSqRemainder_bounds hq).1
  have hRemainderUpper :
      ∀ᶠ q : ℕ in atTop,
        pureLinearScaledExpectedChartBuresSqRemainder q ≤
          QubitOracle.Paper.OneQubitPureLinearEstimatorFourthMoment.pureLinearScaledBuresRemainderEnvelope
            q := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with q hq
    exact (pureLinearScaledExpectedChartBuresSqRemainder_bounds hq).2
  have hRemainderZero :
      Tendsto pureLinearScaledExpectedChartBuresSqRemainder atTop (𝓝 0) :=
    Filter.Tendsto.squeeze' tendsto_const_nhds
      QubitOracle.Paper.OneQubitPureLinearEstimatorFourthMomentClosed.pureLinearScaledBuresRemainderEnvelope_tendsto_zero_closed
      hRemainderNonnegative hRemainderUpper
  have hOnePlus :
      Tendsto
        (fun q : ℕ => 1 + pureLinearScaledExpectedChartBuresSqRemainder q)
        atTop (𝓝 1) := by
    simpa using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add hRemainderZero
  have heq :
      pureLinearScaledExpectedChartBuresSq =ᶠ[atTop]
        (fun q : ℕ => 1 + pureLinearScaledExpectedChartBuresSqRemainder q) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with q hq
    exact pureLinearScaledExpectedChartBuresSq_eq_one_add_remainder hq
  exact hOnePlus.congr' heq.symm

end QubitOracle.Paper.OneQubitPureLinearEstimatorBuresRiskClosed
