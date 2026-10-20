import QubitOracle.Paper.OneQubitPureLinearEstimatorBuresRiskClosed
import QubitOracle.Paper.OneQubitPureLinearEstimatorFourthMomentClosed
import QubitOracle.Paper.OneQubitPureBuresFidelityRiskTransfer

/-!
# Pure one-qubit Bures and fidelity risk endpoints

The scope is the concrete north-pole `Fin 2` tangent estimator with `q`
independent fair outcomes on each of the two tangent Pauli axes.  Its total
sample size is `2q`.  For positive `q`, every realization has tangent squared
radius at most two, and therefore remains inside the existing radius-four
physical chart.
-/

open scoped BigOperators ENNReal
open Filter MeasureTheory Topology

namespace QubitOracle
namespace Paper

/-! ## Exact loss conventions for the concrete chart estimator -/

/-- Ordinary fidelity `F` of the chart estimate with the north-pole truth. -/
noncomputable def pureLinearChartOrdinaryFidelity
    (q : ℕ)
    (omega :
      OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q) : ℝ :=
  pureQubitChartOverlap
    (OneQubitPureLinearEstimatorRisk.pureLinearEstimator q omega)

/-- Root fidelity `sqrt F`. -/
noncomputable def pureLinearChartRootFidelity
    (q : ℕ)
    (omega :
      OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q) : ℝ :=
  Real.sqrt (pureLinearChartOrdinaryFidelity q omega)

/-- Root infidelity `1 - sqrt F`. -/
noncomputable def pureLinearChartRootInfidelity
    (q : ℕ)
    (omega :
      OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q) : ℝ :=
  1 - pureLinearChartRootFidelity q omega

/-- Ordinary infidelity `1 - F`. -/
noncomputable def pureLinearChartOrdinaryInfidelity
    (q : ℕ)
    (omega :
      OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q) : ℝ :=
  1 - pureLinearChartOrdinaryFidelity q omega

/-- The retained exact squared-Bures loss. -/
noncomputable def pureLinearChartSquaredBuresLoss
    (q : ℕ)
    (omega :
      OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q) : ℝ :=
  OneQubitPureLinearEstimatorBuresRiskClosed.pureLinearChartBuresSq q omega

/-- The retained loss is exactly the finite-dimensional pure-chart loss, not
a parallel surrogate. -/
theorem pureLinearChartSquaredBuresLoss_eq_geometry
    (q : ℕ)
    (omega :
      OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q) :
    pureLinearChartSquaredBuresLoss q omega =
      pureQubitChartBuresSq
        (OneQubitPureLinearEstimatorRisk.pureLinearEstimator q omega) := by
  rfl

/-- The estimator's chart radius is the fourth-moment module's squared-radius
random variable. -/
theorem pureLinearEstimator_radiusSq_eq_squaredRadius
    (q : ℕ)
    (omega :
      OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q) :
    tangentRadiusSq
        (OneQubitPureLinearEstimatorRisk.pureLinearEstimator q omega) =
      OneQubitPureLinearEstimatorFourthMoment.pureLinearSquaredRadius
        q omega := by
  rw [OneQubitPureLinearEstimatorRisk.pureLinearEstimator_tangentRadiusSq_eq]
  rfl

/-- For positive `q`, the concrete estimator's overlap is in `[0,1]`; this is
the existing physical chart safeguard. -/
theorem pureLinearChartOrdinaryFidelity_mem_Icc
    {q : ℕ} (hq : 0 < q)
    (omega :
      OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q) :
    pureLinearChartOrdinaryFidelity q omega ∈ Set.Icc 0 1 := by
  let h := OneQubitPureLinearEstimatorRisk.pureLinearEstimator q omega
  have hRadius0 : 0 ≤ tangentRadiusSq h := tangentRadiusSq_nonneg h
  have hRadius2 : tangentRadiusSq h ≤ 2 :=
    OneQubitPureLinearEstimatorRisk.pureLinearEstimator_tangentRadiusSq_le_two
      hq omega
  have hChart : tangentRadiusSq h ≤ 4 :=
    OneQubitPureLinearEstimatorRisk.pureLinearEstimator_in_pureChart hq omega
  rw [pureLinearChartOrdinaryFidelity, pureQubitChartOverlap_eq h hChart]
  constructor <;> nlinarith

/-- Exact ordinary-fidelity formula. -/
theorem pureLinearChartOrdinaryFidelity_eq
    {q : ℕ} (hq : 0 < q)
    (omega :
      OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q) :
    pureLinearChartOrdinaryFidelity q omega =
      1 -
        OneQubitPureLinearEstimatorFourthMoment.pureLinearSquaredRadius
          q omega / 4 := by
  let h := OneQubitPureLinearEstimatorRisk.pureLinearEstimator q omega
  rw [pureLinearChartOrdinaryFidelity,
    pureQubitChartOverlap_eq h
      (OneQubitPureLinearEstimatorRisk.pureLinearEstimator_in_pureChart
        hq omega),
    pureLinearEstimator_radiusSq_eq_squaredRadius]

/-- Exact root-fidelity formula. -/
theorem pureLinearChartRootFidelity_eq
    {q : ℕ} (hq : 0 < q)
    (omega :
      OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q) :
    pureLinearChartRootFidelity q omega =
      Real.sqrt
        (1 -
          OneQubitPureLinearEstimatorFourthMoment.pureLinearSquaredRadius
            q omega / 4) := by
  rw [pureLinearChartRootFidelity,
    pureLinearChartOrdinaryFidelity_eq hq omega]

/-- Exact root-infidelity formula. -/
theorem pureLinearChartRootInfidelity_eq
    {q : ℕ} (hq : 0 < q)
    (omega :
      OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q) :
    pureLinearChartRootInfidelity q omega =
      1 - Real.sqrt
        (1 -
          OneQubitPureLinearEstimatorFourthMoment.pureLinearSquaredRadius
            q omega / 4) := by
  rw [pureLinearChartRootInfidelity,
    pureLinearChartRootFidelity_eq hq omega]

/-- Ordinary infidelity is exactly the local quadratic loss. -/
theorem pureLinearChartOrdinaryInfidelity_eq_quadratic
    {q : ℕ} (hq : 0 < q)
    (omega :
      OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q) :
    pureLinearChartOrdinaryInfidelity q omega =
      OneQubitPureLinearEstimatorRisk.pureLinearQuadraticLoss q omega := by
  unfold pureLinearChartOrdinaryInfidelity pureLinearChartOrdinaryFidelity
  simpa [pureQubitChartInfidelity, pureInfidelityFromOverlap] using
    (OneQubitPureLinearEstimatorRisk.pureLinearChartInfidelity_eq_quadraticLoss
      hq omega)

/-- Exact squared-Bures formula. -/
theorem pureLinearChartSquaredBuresLoss_eq_two_mul_rootInfidelity
    (q : ℕ)
    (omega :
      OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q) :
    pureLinearChartSquaredBuresLoss q omega =
      2 * pureLinearChartRootInfidelity q omega := by
  rw [pureLinearChartSquaredBuresLoss_eq_geometry]
  rfl

/-- Exact fidelity-convention identity
`1-F = B-B^2/4`. -/
theorem pureLinearChartOrdinaryInfidelity_eq_bures_sub_quarter_sq
    {q : ℕ} (hq : 0 < q)
    (omega :
      OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q) :
    pureLinearChartOrdinaryInfidelity q omega =
      pureLinearChartSquaredBuresLoss q omega -
        pureLinearChartSquaredBuresLoss q omega ^ 2 / 4 := by
  have hOverlap := pureLinearChartOrdinaryFidelity_mem_Icc hq omega
  unfold pureLinearChartOrdinaryInfidelity
  rw [pureLinearChartSquaredBuresLoss_eq_geometry]
  exact pureInfidelityFromOverlap_eq_buresSq_sub_quarter_sq hOverlap.1

/-! ## Fourth-moment control of `E[B^2]` -/

/-- Pointwise fourth-moment envelope.  The retained Bures remainder and the
radius bound `r^2 <= 2` imply `B <= 3 r^2 / 8`; hence
`B^2 <= 9 (r^2)^2 / 64`. -/
theorem pureLinearChartSquaredBuresLoss_sq_le_fourthEnvelope
    {q : ℕ} (hq : 0 < q)
    (omega :
      OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q) :
    pureLinearChartSquaredBuresLoss q omega ^ 2 ≤
      (9 / 64 : ℝ) *
        OneQubitPureLinearEstimatorFourthMoment.pureLinearSquaredRadius
          q omega ^ 2 := by
  let radiusSq :=
    OneQubitPureLinearEstimatorFourthMoment.pureLinearSquaredRadius q omega
  let B := pureLinearChartSquaredBuresLoss q omega
  have hRadius0 : 0 ≤ radiusSq := by
    dsimp [radiusSq]
    unfold OneQubitPureLinearEstimatorFourthMoment.pureLinearSquaredRadius
    positivity
  have hRadius2 : radiusSq ≤ 2 := by
    calc
      radiusSq = tangentRadiusSq
          (OneQubitPureLinearEstimatorRisk.pureLinearEstimator q omega) := by
        simpa [radiusSq] using
          (pureLinearEstimator_radiusSq_eq_squaredRadius q omega).symm
      _ ≤ 2 :=
        OneQubitPureLinearEstimatorRisk.pureLinearEstimator_tangentRadiusSq_le_two
          hq omega
  have hQuadratic :
      OneQubitPureLinearEstimatorRisk.pureLinearQuadraticLoss q omega =
        radiusSq / 4 := by
    rw [OneQubitPureLinearEstimatorRisk.pureLinearQuadraticLoss,
      pureQubitQuadraticLossReal,
      pureLinearEstimator_radiusSq_eq_squaredRadius]
  have hRemainderRaw :=
    OneQubitPureLinearEstimatorBuresRiskClosed.pureLinearChartBuresSq_remainder_bounds
      hq omega
  rw [hQuadratic] at hRemainderRaw
  have hRemainder :
      0 ≤ B - radiusSq / 4 ∧
        B - radiusSq / 4 ≤ radiusSq ^ 2 / 16 := by
    simpa [B, radiusSq, pureLinearChartSquaredBuresLoss] using
      hRemainderRaw
  have hB0 : 0 ≤ B := by
    nlinarith [hRemainder.1]
  have hBUpper : B ≤ 3 * radiusSq / 8 := by
    have hProduct : 0 ≤ radiusSq * (2 - radiusSq) :=
      mul_nonneg hRadius0 (sub_nonneg.mpr hRadius2)
    nlinarith [hRemainder.2, hProduct]
  have hUpper0 : 0 ≤ 3 * radiusSq / 8 := by positivity
  have hSquareProduct :
      0 ≤ (3 * radiusSq / 8 - B) * (B + 3 * radiusSq / 8) :=
    mul_nonneg (sub_nonneg.mpr hBUpper) (add_nonneg hB0 hUpper0)
  have hSquare : B ^ 2 ≤ (9 / 64 : ℝ) * radiusSq ^ 2 := by
    nlinarith [hSquareProduct]
  simpa [B, radiusSq] using hSquare

private theorem pure_fintype_measurable
    {Alpha Beta : Type*} [MeasurableSpace Alpha]
    [MeasurableSingletonClass Alpha] [Fintype Alpha]
    [MeasurableSpace Beta] (f : Alpha → Beta) : Measurable f := by
  exact measurable_of_finite f

private theorem pure_finite_integrable
    {Alpha : Type*} [MeasurableSpace Alpha]
    [MeasurableSingletonClass Alpha] [Fintype Alpha]
    (mu : Measure Alpha) [IsFiniteMeasure mu]
    {f : Alpha → ℝ} (_hf : Measurable f) : Integrable f mu := by
  exact Integrable.of_finite

/-- Expected square of the exact squared-Bures loss. -/
noncomputable def pureLinearExpectedChartSquaredBuresSecondMoment
    (q : ℕ) : ℝ :=
  ∫ omega,
      pureLinearChartSquaredBuresLoss q omega ^ 2
    ∂OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q

/-- Total-shot-scaled expected square of squared Bures. -/
noncomputable def pureLinearScaledExpectedChartSquaredBuresSecondMoment
    (q : ℕ) : ℝ :=
  (OneQubitPureLinearEstimatorRisk.pureLinearTotalShots q : ℝ) *
    pureLinearExpectedChartSquaredBuresSecondMoment q

/-- Exact explicit upper rate obtained from the closed fourth moment. -/
noncomputable def pureLinearScaledExpectedChartSquaredBuresSecondMomentRate
    (q : ℕ) : ℝ :=
  (9 / 4 : ℝ) * ((q : ℝ)⁻¹) -
    (9 / 8 : ℝ) * ((q : ℝ)⁻¹) ^ 2

theorem pureLinearScaledExpectedChartSquaredBuresSecondMoment_bounds
    {q : ℕ} (hq : 0 < q) :
    0 ≤ pureLinearScaledExpectedChartSquaredBuresSecondMoment q ∧
      pureLinearScaledExpectedChartSquaredBuresSecondMoment q ≤
        pureLinearScaledExpectedChartSquaredBuresSecondMomentRate q := by
  let mu := OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q
  let B2 : OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q → ℝ :=
    fun omega => pureLinearChartSquaredBuresLoss q omega ^ 2
  let upper : OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q → ℝ :=
    fun omega => (9 / 64 : ℝ) *
      OneQubitPureLinearEstimatorFourthMoment.pureLinearSquaredRadius
        q omega ^ 2
  have hB2Measurable : Measurable B2 := pure_fintype_measurable B2
  have hUpperMeasurable : Measurable upper := pure_fintype_measurable upper
  have hB2Integrable : Integrable B2 mu :=
    pure_finite_integrable mu hB2Measurable
  have hUpperIntegrable : Integrable upper mu :=
    pure_finite_integrable mu hUpperMeasurable
  have hB2Nonnegative : ∀ᵐ omega ∂mu, 0 ≤ B2 omega :=
    Filter.Eventually.of_forall fun omega => sq_nonneg _
  have hPointwise : ∀ᵐ omega ∂mu, B2 omega ≤ upper omega :=
    Filter.Eventually.of_forall fun omega =>
      pureLinearChartSquaredBuresLoss_sq_le_fourthEnvelope hq omega
  have hIntegralNonnegative :
      0 ≤ pureLinearExpectedChartSquaredBuresSecondMoment q := by
    simpa [pureLinearExpectedChartSquaredBuresSecondMoment, B2, mu] using
      integral_nonneg_of_ae hB2Nonnegative
  have hIntegralUpper :
      pureLinearExpectedChartSquaredBuresSecondMoment q ≤
        (9 / 64 : ℝ) *
          (8 / (q : ℝ) ^ 2 - 4 / (q : ℝ) ^ 3) := by
    calc
      pureLinearExpectedChartSquaredBuresSecondMoment q ≤
          ∫ omega, upper omega ∂mu := by
        simpa [pureLinearExpectedChartSquaredBuresSecondMoment, B2, mu] using
          integral_mono_ae hB2Integrable hUpperIntegrable hPointwise
      _ = (9 / 64 : ℝ) *
          (∫ omega,
            OneQubitPureLinearEstimatorFourthMoment.pureLinearSquaredRadius
              q omega ^ 2 ∂mu) := by
        unfold upper
        rw [integral_const_mul]
      _ = (9 / 64 : ℝ) *
          (8 / (q : ℝ) ^ 2 - 4 / (q : ℝ) ^ 3) := by
        rw [OneQubitPureLinearEstimatorFourthMomentClosed.pureLinearSquaredRadius_fourthMoment_closed
          hq]
  have hShots :
      0 ≤ (OneQubitPureLinearEstimatorRisk.pureLinearTotalShots q : ℝ) := by
    positivity
  constructor
  · unfold pureLinearScaledExpectedChartSquaredBuresSecondMoment
    exact mul_nonneg hShots hIntegralNonnegative
  · calc
      pureLinearScaledExpectedChartSquaredBuresSecondMoment q ≤
          (OneQubitPureLinearEstimatorRisk.pureLinearTotalShots q : ℝ) *
            ((9 / 64 : ℝ) *
              (8 / (q : ℝ) ^ 2 - 4 / (q : ℝ) ^ 3)) := by
        exact mul_le_mul_of_nonneg_left hIntegralUpper hShots
      _ = pureLinearScaledExpectedChartSquaredBuresSecondMomentRate q := by
        have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
        unfold OneQubitPureLinearEstimatorRisk.pureLinearTotalShots
          pureLinearScaledExpectedChartSquaredBuresSecondMomentRate
        simp only [Nat.cast_mul, Nat.cast_ofNat]
        field_simp [hqR]
        ring

theorem pureLinearScaledExpectedChartSquaredBuresSecondMomentRate_tendsto_zero :
    Tendsto pureLinearScaledExpectedChartSquaredBuresSecondMomentRate
      atTop (nhds 0) := by
  have hInv : Tendsto (fun q : ℕ => ((q : ℝ)⁻¹)) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hNineQuarter :
      Tendsto (fun _ : ℕ => (9 / 4 : ℝ)) atTop (nhds (9 / 4 : ℝ)) :=
    tendsto_const_nhds
  have hNineEighth :
      Tendsto (fun _ : ℕ => (9 / 8 : ℝ)) atTop (nhds (9 / 8 : ℝ)) :=
    tendsto_const_nhds
  have hFirst :
      Tendsto (fun q : ℕ => (9 / 4 : ℝ) * ((q : ℝ)⁻¹))
        atTop (nhds 0) := by
    simpa using hNineQuarter.mul hInv
  have hSecond :
      Tendsto (fun q : ℕ => (9 / 8 : ℝ) * ((q : ℝ)⁻¹) ^ 2)
        atTop (nhds 0) := by
    simpa using hNineEighth.mul (hInv.pow 2)
  unfold pureLinearScaledExpectedChartSquaredBuresSecondMomentRate
  simpa only [sub_zero] using hFirst.sub hSecond

/-- Total-shot-scaled `E[B^2]` vanishes. -/
theorem pureLinearScaledExpectedChartSquaredBuresSecondMoment_tendsto_zero :
    Tendsto pureLinearScaledExpectedChartSquaredBuresSecondMoment
      atTop (nhds 0) := by
  have hLower : ∀ᶠ q : ℕ in atTop,
      0 ≤ pureLinearScaledExpectedChartSquaredBuresSecondMoment q := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with q hq
    exact (pureLinearScaledExpectedChartSquaredBuresSecondMoment_bounds hq).1
  have hUpper : ∀ᶠ q : ℕ in atTop,
      pureLinearScaledExpectedChartSquaredBuresSecondMoment q ≤
        pureLinearScaledExpectedChartSquaredBuresSecondMomentRate q := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with q hq
    exact (pureLinearScaledExpectedChartSquaredBuresSecondMoment_bounds hq).2
  exact Filter.Tendsto.squeeze' tendsto_const_nhds
    pureLinearScaledExpectedChartSquaredBuresSecondMomentRate_tendsto_zero
    hLower hUpper

/-! ## Scaled risk conventions -/

/-- Total-shot-scaled exact squared-Bures risk. -/
noncomputable def pureLinearScaledExpectedSquaredBuresRisk (q : ℕ) : ℝ :=
  OneQubitPureLinearEstimatorBuresRiskClosed.pureLinearScaledExpectedChartBuresSq q

/-- Total-shot-scaled root-infidelity risk. -/
noncomputable def pureLinearScaledExpectedRootInfidelityRisk (q : ℕ) : ℝ :=
  (OneQubitPureLinearEstimatorRisk.pureLinearTotalShots q : ℝ) *
    (∫ omega,
      pureLinearChartRootInfidelity q omega
      ∂OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q)

/-- Total-shot-scaled ordinary-infidelity risk. -/
noncomputable def pureLinearScaledExpectedOrdinaryInfidelityRisk (q : ℕ) : ℝ :=
  (OneQubitPureLinearEstimatorRisk.pureLinearTotalShots q : ℝ) *
    (∫ omega,
      pureLinearChartOrdinaryInfidelity q omega
      ∂OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q)

/-- Squared Bures is exactly twice root infidelity after expectation and total
shot scaling. -/
theorem pureLinearScaledExpectedSquaredBuresRisk_eq_two_mul_rootInfidelity
    (q : ℕ) :
    pureLinearScaledExpectedSquaredBuresRisk q =
      2 * pureLinearScaledExpectedRootInfidelityRisk q := by
  let mu := OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q
  have hRootMeasurable : Measurable
      (pureLinearChartRootInfidelity q) :=
    pure_fintype_measurable _
  unfold pureLinearScaledExpectedSquaredBuresRisk
    OneQubitPureLinearEstimatorBuresRiskClosed.pureLinearScaledExpectedChartBuresSq
    OneQubitPureLinearEstimatorBuresRiskClosed.pureLinearExpectedChartBuresSq
    pureLinearScaledExpectedRootInfidelityRisk
  have hIntegral :
      (∫ omega, pureLinearChartSquaredBuresLoss q omega ∂mu) =
        2 * (∫ omega, pureLinearChartRootInfidelity q omega ∂mu) := by
    calc
      (∫ omega, pureLinearChartSquaredBuresLoss q omega ∂mu) =
          ∫ omega, 2 * pureLinearChartRootInfidelity q omega ∂mu := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall
          (pureLinearChartSquaredBuresLoss_eq_two_mul_rootInfidelity q)
      _ = 2 * (∫ omega,
          pureLinearChartRootInfidelity q omega ∂mu) := by
        rw [integral_const_mul]
  change
    (OneQubitPureLinearEstimatorRisk.pureLinearTotalShots q : ℝ) *
        (∫ omega, pureLinearChartSquaredBuresLoss q omega ∂mu) = _
  rw [hIntegral]
  ring

/-- Integrated exact identity
`scaled(1-F) = scaled(B) - scaled(B^2)/4`. -/
theorem pureLinearScaledExpectedOrdinaryInfidelity_eq_bures_sub_secondMoment
    {q : ℕ} (hq : 0 < q) :
    pureLinearScaledExpectedOrdinaryInfidelityRisk q =
      pureLinearScaledExpectedSquaredBuresRisk q -
        pureLinearScaledExpectedChartSquaredBuresSecondMoment q / 4 := by
  let mu := OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q
  let B : OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q → ℝ :=
    pureLinearChartSquaredBuresLoss q
  let B2 : OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q → ℝ :=
    fun omega => B omega ^ 2
  have hBMeasurable : Measurable B := pure_fintype_measurable B
  have hB2Measurable : Measurable B2 := pure_fintype_measurable B2
  have hBIntegrable : Integrable B mu :=
    pure_finite_integrable mu hBMeasurable
  have hB2Integrable : Integrable B2 mu :=
    pure_finite_integrable mu hB2Measurable
  have hIntegral :
      (∫ omega, pureLinearChartOrdinaryInfidelity q omega ∂mu) =
        (∫ omega, B omega ∂mu) - (∫ omega, B2 omega ∂mu) / 4 := by
    calc
      (∫ omega, pureLinearChartOrdinaryInfidelity q omega ∂mu) =
          ∫ omega, B omega - B2 omega / 4 ∂mu := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun omega => by
          simpa [B, B2] using
            pureLinearChartOrdinaryInfidelity_eq_bures_sub_quarter_sq
              hq omega
      _ = (∫ omega, B omega ∂mu) -
          (∫ omega, B2 omega / 4 ∂mu) :=
        integral_sub hBIntegrable
          (hB2Integrable.div_const 4)
      _ = (∫ omega, B omega ∂mu) -
          (∫ omega, B2 omega ∂mu) / 4 := by
        rw [integral_div]
  unfold pureLinearScaledExpectedOrdinaryInfidelityRisk
    pureLinearScaledExpectedSquaredBuresRisk
    OneQubitPureLinearEstimatorBuresRiskClosed.pureLinearScaledExpectedChartBuresSq
    OneQubitPureLinearEstimatorBuresRiskClosed.pureLinearExpectedChartBuresSq
    pureLinearScaledExpectedChartSquaredBuresSecondMoment
    pureLinearExpectedChartSquaredBuresSecondMoment
  change
    (OneQubitPureLinearEstimatorRisk.pureLinearTotalShots q : ℝ) *
        (∫ omega, pureLinearChartOrdinaryInfidelity q omega ∂mu) = _
  rw [hIntegral]
  simp only [B, B2, mu, pureLinearChartSquaredBuresLoss]
  ring

/-- The finite-`q` ordinary-infidelity scaled risk is already exactly one. -/
theorem pureLinearScaledExpectedOrdinaryInfidelityRisk_eq_one
    {q : ℕ} (hq : 0 < q) :
    pureLinearScaledExpectedOrdinaryInfidelityRisk q = 1 := by
  unfold pureLinearScaledExpectedOrdinaryInfidelityRisk
  simpa [pureLinearChartOrdinaryInfidelity,
    pureLinearChartOrdinaryFidelity, pureQubitChartInfidelity,
    pureInfidelityFromOverlap] using
    (OneQubitPureLinearEstimatorRisk.pureLinearScaledExpectedChartInfidelity_eq_one
      hq)

/-! ## Pure-qubit endpoints -/

/-- Total-shot-scaled exact squared-Bures risk tends to one. -/
theorem pureLinearScaledExpectedSquaredBuresRisk_tendsto_one :
    Tendsto pureLinearScaledExpectedSquaredBuresRisk atTop (nhds 1) := by
  exact
    OneQubitPureLinearEstimatorBuresRiskClosed.pureLinearScaledExpectedChartBuresSq_tendsto_one

/-- Total-shot-scaled root-infidelity risk tends to one half. -/
theorem pureLinearScaledExpectedRootInfidelityRisk_tendsto_one_half :
    Tendsto pureLinearScaledExpectedRootInfidelityRisk
      atTop (nhds (1 / 2 : ℝ)) := by
  have hBures := pureLinearScaledExpectedSquaredBuresRisk_tendsto_one
  have hHalf : Tendsto
      (fun q => (2 : ℝ)⁻¹ * pureLinearScaledExpectedSquaredBuresRisk q)
      atTop (nhds (1 / 2 : ℝ)) := by
    convert tendsto_const_nhds.mul hBures using 1 <;> norm_num
  refine Filter.Tendsto.congr' ?_ hHalf
  exact Eventually.of_forall fun q => by
    change (2 : ℝ)⁻¹ * pureLinearScaledExpectedSquaredBuresRisk q =
      pureLinearScaledExpectedRootInfidelityRisk q
    rw [pureLinearScaledExpectedSquaredBuresRisk_eq_two_mul_rootInfidelity]
    ring

/-- Total-shot-scaled ordinary infidelity tends to one, obtained from the
exact Bures identity and the vanishing `B^2` term. -/
theorem pureLinearScaledExpectedOrdinaryInfidelityRisk_tendsto_one :
    Tendsto pureLinearScaledExpectedOrdinaryInfidelityRisk atTop (nhds 1) := by
  have hBures := pureLinearScaledExpectedSquaredBuresRisk_tendsto_one
  have hSecond :=
    pureLinearScaledExpectedChartSquaredBuresSecondMoment_tendsto_zero
  have hQuarter : Tendsto
      (fun q => pureLinearScaledExpectedChartSquaredBuresSecondMoment q / 4)
      atTop (nhds 0) := by
    have hQuarterConstant :
        Tendsto (fun _ : ℕ => (4 : ℝ)⁻¹) atTop (nhds (4 : ℝ)⁻¹) :=
      tendsto_const_nhds
    simpa [div_eq_mul_inv, mul_comm] using
      hQuarterConstant.mul hSecond
  have hDifference : Tendsto
      (fun q => pureLinearScaledExpectedSquaredBuresRisk q -
        pureLinearScaledExpectedChartSquaredBuresSecondMoment q / 4)
      atTop (nhds 1) := by
    simpa using hBures.sub hQuarter
  refine Filter.Tendsto.congr' ?_ hDifference
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with q hq
  exact
    (pureLinearScaledExpectedOrdinaryInfidelity_eq_bures_sub_secondMoment
      hq).symm

namespace Label

/-- Paper-facing pure one-qubit squared-Bures optimal endpoint for the concrete
north-pole two-axis estimator. -/
theorem thm_pure_qubit_linear_bures_optimal_endpoint :
    Tendsto pureLinearScaledExpectedSquaredBuresRisk atTop (nhds 1) :=
  pureLinearScaledExpectedSquaredBuresRisk_tendsto_one

/-- Paper-facing pure one-qubit ordinary-fidelity optimal endpoint.  The loss
is `1-F`, not root infidelity. -/
theorem thm_pure_qubit_linear_fidelity_optimal_endpoint :
    Tendsto pureLinearScaledExpectedOrdinaryInfidelityRisk atTop (nhds 1) :=
  pureLinearScaledExpectedOrdinaryInfidelityRisk_tendsto_one

end Label

end Paper
end QubitOracle
