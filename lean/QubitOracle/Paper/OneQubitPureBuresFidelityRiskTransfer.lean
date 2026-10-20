import QubitOracle.Paper.PureBuresLocal
import QubitOracle.Paper.PureStateFoundations
import QubitOracle.Paper.EventLIntegralCore

open scoped ENNReal Topology BigOperators
open Filter MeasureTheory Set

namespace QubitOracle.Paper

noncomputable section

/-!
# Pure one-qubit Bures and infidelity risk transfer

This module deliberately keeps squared Bures loss and infidelity separate.
For a scalar squared overlap `F`, the losses are

* infidelity: `1 - F`;
* squared Bures loss: `2 * (1 - sqrt F)`.

Their exact bridge is proved before either asymptotic endpoint is stated.  In
the clean rank-one chart with `TangentIndex 1`, root-`N` infidelity is exactly
its quadratic form, whereas root-`N` squared Bures loss has a nonnegative
fourth-order remainder bounded by `||h||^4 / (16 N)`.

The good event uses this local chart.  On the bad event the fallback is an
arbitrary normalized pure one-qubit state, so its physical infidelity is at
most one and its squared Bures loss is at most two.  A probability envelope of
order `N⁻²` makes both root-`N` fallback contributions vanish.
-/

abbrev PureQubitTangent := TangentIndex 1 → ℝ
abbrev PureQubitStateVector := Fin 2 → ℂ

/-! ## Exact scalar overlap/loss identities -/

def pureInfidelityFromOverlap (overlap : ℝ) : ℝ :=
  1 - overlap

def pureBuresSqFromOverlap (overlap : ℝ) : ℝ :=
  2 * (1 - Real.sqrt overlap)

theorem pureInfidelityFromOverlap_eq_one_sub
    (overlap : ℝ) :
    pureInfidelityFromOverlap overlap = 1 - overlap := rfl

theorem pureBuresSqFromOverlap_eq_two_mul_one_sub_sqrt
    (overlap : ℝ) :
    pureBuresSqFromOverlap overlap =
      2 * (1 - Real.sqrt overlap) := rfl

/-- Exact bridge between infidelity and squared Bures loss.  If `B` denotes
`squared Bures loss`, then infidelity is `B - B²/4`. -/
theorem pureInfidelityFromOverlap_eq_buresSq_sub_quarter_sq
    {overlap : ℝ} (hoverlap : 0 ≤ overlap) :
    pureInfidelityFromOverlap overlap =
      pureBuresSqFromOverlap overlap -
        pureBuresSqFromOverlap overlap ^ 2 / 4 := by
  have hsqrt := Real.sq_sqrt hoverlap
  unfold pureInfidelityFromOverlap pureBuresSqFromOverlap
  nlinarith

theorem pureLosses_nonnegative_and_bounded
    {overlap : ℝ} (hzero : 0 ≤ overlap) (hone : overlap ≤ 1) :
    (0 ≤ pureInfidelityFromOverlap overlap ∧
        pureInfidelityFromOverlap overlap ≤ 1) ∧
      (0 ≤ pureBuresSqFromOverlap overlap ∧
        pureBuresSqFromOverlap overlap ≤ 2) := by
  have hsqrt0 : 0 ≤ Real.sqrt overlap := Real.sqrt_nonneg overlap
  have hsqrtSq : (Real.sqrt overlap) ^ 2 = overlap :=
    Real.sq_sqrt hzero
  have hsqrtOne : Real.sqrt overlap ≤ 1 := by
    nlinarith
  unfold pureInfidelityFromOverlap pureBuresSqFromOverlap
  constructor <;> constructor <;> nlinarith

/-! ## Normalized one-qubit states and north-pole overlap -/

/-- Squared overlap of a pure one-qubit vector with the north-pole reference
ray `(1,0)`. -/
def pureQubitNorthPoleOverlap (psi : PureQubitStateVector) : ℝ :=
  Complex.normSq (psi 0)

theorem pureQubitNorthPoleOverlap_mem_unitInterval
    (psi : PureQubitStateVector)
    (hnormalized : pureStateNormSq psi = 1) :
    0 ≤ pureQubitNorthPoleOverlap psi ∧
      pureQubitNorthPoleOverlap psi ≤ 1 := by
  have hzero : 0 ≤ Complex.normSq (psi 0) := Complex.normSq_nonneg _
  have hone : 0 ≤ Complex.normSq (psi 1) := Complex.normSq_nonneg _
  have hsum :
      Complex.normSq (psi 0) + Complex.normSq (psi 1) = 1 := by
    simpa [pureStateNormSq, Fin.sum_univ_succ] using hnormalized
  unfold pureQubitNorthPoleOverlap
  constructor
  · exact hzero
  · nlinarith

def pureQubitStateInfidelity (psi : PureQubitStateVector) : ℝ :=
  pureInfidelityFromOverlap (pureQubitNorthPoleOverlap psi)

def pureQubitStateBuresSq (psi : PureQubitStateVector) : ℝ :=
  pureBuresSqFromOverlap (pureQubitNorthPoleOverlap psi)

theorem pureQubitState_infidelity_bures_exact
    (psi : PureQubitStateVector)
    (hnormalized : pureStateNormSq psi = 1) :
    pureQubitStateInfidelity psi =
      pureQubitStateBuresSq psi - pureQubitStateBuresSq psi ^ 2 / 4 := by
  exact pureInfidelityFromOverlap_eq_buresSq_sub_quarter_sq
    (pureQubitNorthPoleOverlap_mem_unitInterval psi hnormalized).1

theorem pureQubitState_losses_bounds
    (psi : PureQubitStateVector)
    (hnormalized : pureStateNormSq psi = 1) :
    (0 ≤ pureQubitStateInfidelity psi ∧
        pureQubitStateInfidelity psi ≤ 1) ∧
      (0 ≤ pureQubitStateBuresSq psi ∧
        pureQubitStateBuresSq psi ≤ 2) := by
  exact pureLosses_nonnegative_and_bounded
    (pureQubitNorthPoleOverlap_mem_unitInterval psi hnormalized).1
    (pureQubitNorthPoleOverlap_mem_unitInterval psi hnormalized).2

/-! ## Clean rank-one local chart -/

/-- Squared overlap with the reference ray in the clean rank-one chart. -/
def pureQubitChartOverlap (h : PureQubitTangent) : ℝ :=
  chartFidelity h

def pureQubitChartInfidelity (h : PureQubitTangent) : ℝ :=
  pureInfidelityFromOverlap (pureQubitChartOverlap h)

def pureQubitChartBuresSq (h : PureQubitTangent) : ℝ :=
  pureBuresSqFromOverlap (pureQubitChartOverlap h)

theorem pureQubitChartOverlap_eq
    (h : PureQubitTangent) (hchart : tangentRadiusSq h ≤ 4) :
    pureQubitChartOverlap h = 1 - tangentRadiusSq h / 4 := by
  exact chartFidelity_eq h hchart

theorem pureQubitChartInfidelity_eq_quadratic
    (h : PureQubitTangent) (hchart : tangentRadiusSq h ≤ 4) :
    pureQubitChartInfidelity h = tangentRadiusSq h / 4 := by
  rw [pureQubitChartInfidelity, pureInfidelityFromOverlap,
    pureQubitChartOverlap_eq h hchart]
  ring

theorem pureQubitChartBuresSq_eq_buresChartLoss
    (h : PureQubitTangent) :
    pureQubitChartBuresSq h = buresChartLoss h := rfl

theorem pureQubitChart_infidelity_bures_exact
    (h : PureQubitTangent) (hchart : tangentRadiusSq h ≤ 4) :
    pureQubitChartInfidelity h =
      pureQubitChartBuresSq h - pureQubitChartBuresSq h ^ 2 / 4 := by
  apply pureInfidelityFromOverlap_eq_buresSq_sub_quarter_sq
  rw [pureQubitChartOverlap_eq h hchart]
  have hnonnegative := tangentRadiusSq_nonneg h
  linarith

/-! ## Root-N scaling and exact local remainders -/

def pureNaturalSampleSize (n : ℕ) : ℕ := n + 1

def pureNaturalSampleSizeReal (n : ℕ) : ℝ :=
  pureNaturalSampleSize n

def pureRootScale (n : ℕ) : ℝ :=
  (Real.sqrt (pureNaturalSampleSizeReal n))⁻¹

lemma pureNaturalSampleSize_pos (n : ℕ) :
    0 < pureNaturalSampleSize n := by
  simp [pureNaturalSampleSize]

lemma pureNaturalSampleSizeReal_pos (n : ℕ) :
    0 < pureNaturalSampleSizeReal n := by
  unfold pureNaturalSampleSizeReal
  exact_mod_cast pureNaturalSampleSize_pos n

lemma pureRootScale_sq (n : ℕ) :
    pureRootScale n ^ 2 = (pureNaturalSampleSizeReal n)⁻¹ := by
  unfold pureRootScale
  rw [inv_pow, Real.sq_sqrt (pureNaturalSampleSizeReal_pos n).le]

lemma pureNaturalSampleSize_mul_rootScale_sq (n : ℕ) :
    pureNaturalSampleSizeReal n * pureRootScale n ^ 2 = 1 := by
  rw [pureRootScale_sq]
  exact mul_inv_cancel₀ (ne_of_gt (pureNaturalSampleSizeReal_pos n))

lemma pureNaturalSampleSize_mul_rootScale_pow_four (n : ℕ) :
    pureNaturalSampleSizeReal n * pureRootScale n ^ 4 =
      (pureNaturalSampleSizeReal n)⁻¹ := by
  calc
    pureNaturalSampleSizeReal n * pureRootScale n ^ 4 =
        pureNaturalSampleSizeReal n * (pureRootScale n ^ 2) ^ 2 := by ring
    _ = pureNaturalSampleSizeReal n *
        ((pureNaturalSampleSizeReal n)⁻¹) ^ 2 := by
      rw [pureRootScale_sq]
    _ = (pureNaturalSampleSizeReal n)⁻¹ := by
      field_simp [ne_of_gt (pureNaturalSampleSizeReal_pos n)]

def pureRootNInfidelityLossReal
    (n : ℕ) (h : PureQubitTangent) : ℝ :=
  pureNaturalSampleSizeReal n *
    pureQubitChartInfidelity (pureRootScale n • h)

def pureRootNBuresSqLossReal
    (n : ℕ) (h : PureQubitTangent) : ℝ :=
  pureNaturalSampleSizeReal n *
    pureQubitChartBuresSq (pureRootScale n • h)

def pureQubitQuadraticLossReal (h : PureQubitTangent) : ℝ :=
  tangentRadiusSq h / 4

def pureBuresFourthRateReal (n : ℕ) : ℝ :=
  (pureNaturalSampleSizeReal n)⁻¹ / 16

theorem pureRootNInfidelityLossReal_eq_quadratic
    (n : ℕ) (h : PureQubitTangent)
    (hchart : pureRootScale n ^ 2 * tangentRadiusSq h ≤ 4) :
    pureRootNInfidelityLossReal n h = pureQubitQuadraticLossReal h := by
  have hscaled : tangentRadiusSq (pureRootScale n • h) ≤ 4 := by
    rw [tangentRadiusSq_smul]
    exact hchart
  rw [pureRootNInfidelityLossReal,
    pureQubitChartInfidelity_eq_quadratic _ hscaled,
    tangentRadiusSq_smul]
  unfold pureQubitQuadraticLossReal
  calc
    pureNaturalSampleSizeReal n *
        (pureRootScale n ^ 2 * tangentRadiusSq h / 4) =
      (pureNaturalSampleSizeReal n * pureRootScale n ^ 2) *
        tangentRadiusSq h / 4 := by ring
    _ = tangentRadiusSq h / 4 := by
      rw [pureNaturalSampleSize_mul_rootScale_sq]
      ring

/-- Root-`N` squared Bures loss equals the pure quadratic loss plus a
nonnegative remainder of order `||h||⁴/N`. -/
theorem pureRootNBuresSqLossReal_remainder_bounds
    (n : ℕ) (h : PureQubitTangent)
    (hchart : pureRootScale n ^ 2 * tangentRadiusSq h ≤ 4) :
    0 ≤ pureRootNBuresSqLossReal n h - pureQubitQuadraticLossReal h ∧
      pureRootNBuresSqLossReal n h - pureQubitQuadraticLossReal h ≤
        pureBuresFourthRateReal n * tangentRadiusSq h ^ 2 := by
  have hb := buresChartLoss_smul_remainder_bounds
    (pureRootScale n) h hchart
  have hNnonnegative : 0 ≤ pureNaturalSampleSizeReal n :=
    (pureNaturalSampleSizeReal_pos n).le
  have hlower := mul_nonneg hNnonnegative hb.1
  have hupper := mul_le_mul_of_nonneg_left hb.2 hNnonnegative
  have hrewrite :
      pureRootNBuresSqLossReal n h - pureQubitQuadraticLossReal h =
        pureNaturalSampleSizeReal n *
          (buresChartLoss (pureRootScale n • h) -
            pureRootScale n ^ 2 * tangentRadiusSq h / 4) := by
    rw [pureRootNBuresSqLossReal,
      pureQubitChartBuresSq_eq_buresChartLoss]
    unfold pureQubitQuadraticLossReal
    linear_combination (tangentRadiusSq h / 4) *
      pureNaturalSampleSize_mul_rootScale_sq n
  constructor
  · rw [hrewrite]
    exact hlower
  · rw [hrewrite]
    calc
      pureNaturalSampleSizeReal n *
          (buresChartLoss (pureRootScale n • h) -
            pureRootScale n ^ 2 * tangentRadiusSq h / 4) ≤
        pureNaturalSampleSizeReal n *
          (pureRootScale n ^ 4 * tangentRadiusSq h ^ 2 / 16) := hupper
      _ = pureBuresFourthRateReal n * tangentRadiusSq h ^ 2 := by
        unfold pureBuresFourthRateReal
        rw [show
          pureNaturalSampleSizeReal n *
              (pureRootScale n ^ 4 * tangentRadiusSq h ^ 2 / 16) =
            (pureNaturalSampleSizeReal n * pureRootScale n ^ 4) *
              tangentRadiusSq h ^ 2 / 16 by ring]
        rw [pureNaturalSampleSize_mul_rootScale_pow_four]
        ring

/-- Root-`N` exact loss bridge. This is stated separately so that no Bures
endpoint can silently be relabelled as an infidelity endpoint. -/
theorem pureRootN_infidelity_bures_exact
    (n : ℕ) (h : PureQubitTangent)
    (hchart : pureRootScale n ^ 2 * tangentRadiusSq h ≤ 4) :
    pureRootNInfidelityLossReal n h =
      pureRootNBuresSqLossReal n h -
        pureNaturalSampleSizeReal n *
          pureQubitChartBuresSq (pureRootScale n • h) ^ 2 / 4 := by
  have hscaled : tangentRadiusSq (pureRootScale n • h) ≤ 4 := by
    rw [tangentRadiusSq_smul]
    exact hchart
  rw [pureRootNInfidelityLossReal, pureRootNBuresSqLossReal,
    pureQubitChart_infidelity_bures_exact _ hscaled]
  ring

/-! ## ENNReal pointwise and good-event transfer -/

def pureRootNInfidelityLoss
    (n : ℕ) (h : PureQubitTangent) : ℝ≥0∞ :=
  ENNReal.ofReal (pureRootNInfidelityLossReal n h)

def pureRootNBuresSqLoss
    (n : ℕ) (h : PureQubitTangent) : ℝ≥0∞ :=
  ENNReal.ofReal (pureRootNBuresSqLossReal n h)

def pureQubitQuadraticLoss (h : PureQubitTangent) : ℝ≥0∞ :=
  ENNReal.ofReal (pureQubitQuadraticLossReal h)

def pureQubitFourthRadiusMoment (h : PureQubitTangent) : ℝ≥0∞ :=
  ENNReal.ofReal (tangentRadiusSq h ^ 2)

def pureBuresFourthRate (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (pureBuresFourthRateReal n)

private theorem pureBuresRemainderENNReal_eq
    (n : ℕ) (h : PureQubitTangent) :
    ENNReal.ofReal
        (pureBuresFourthRateReal n * tangentRadiusSq h ^ 2) =
      pureBuresFourthRate n * pureQubitFourthRadiusMoment h := by
  have hrate : 0 ≤ pureBuresFourthRateReal n := by
    unfold pureBuresFourthRateReal
    exact div_nonneg
      (inv_nonneg.mpr (pureNaturalSampleSizeReal_pos n).le) (by norm_num)
  rw [ENNReal.ofReal_mul hrate]
  rfl

theorem pureRootNInfidelityLoss_eq_quadratic
    (n : ℕ) (h : PureQubitTangent)
    (hchart : pureRootScale n ^ 2 * tangentRadiusSq h ≤ 4) :
    pureRootNInfidelityLoss n h = pureQubitQuadraticLoss h := by
  exact congrArg ENNReal.ofReal
    (pureRootNInfidelityLossReal_eq_quadratic n h hchart)

theorem pureRootNBuresSqLoss_pointwise_bounds
    (n : ℕ) (h : PureQubitTangent)
    (hchart : pureRootScale n ^ 2 * tangentRadiusSq h ≤ 4) :
    pureQubitQuadraticLoss h ≤ pureRootNBuresSqLoss n h ∧
      pureRootNBuresSqLoss n h ≤
        pureQubitQuadraticLoss h +
          pureBuresFourthRate n * pureQubitFourthRadiusMoment h := by
  have hb := pureRootNBuresSqLossReal_remainder_bounds n h hchart
  have hquadratic : 0 ≤ pureQubitQuadraticLossReal h := by
    unfold pureQubitQuadraticLossReal
    exact div_nonneg (tangentRadiusSq_nonneg h) (by norm_num)
  have hrate : 0 ≤ pureBuresFourthRateReal n := by
    unfold pureBuresFourthRateReal
    exact div_nonneg
      (inv_nonneg.mpr (pureNaturalSampleSizeReal_pos n).le) (by norm_num)
  have hmoment : 0 ≤ tangentRadiusSq h ^ 2 := sq_nonneg _
  have hremainder :
      0 ≤ pureBuresFourthRateReal n * tangentRadiusSq h ^ 2 :=
    mul_nonneg hrate hmoment
  have hlowerReal :
      pureQubitQuadraticLossReal h ≤ pureRootNBuresSqLossReal n h :=
    sub_nonneg.mp hb.1
  have hupperReal :
      pureRootNBuresSqLossReal n h ≤
        pureQubitQuadraticLossReal h +
          pureBuresFourthRateReal n * tangentRadiusSq h ^ 2 :=
    by linarith [hb.2]
  constructor
  · exact ENNReal.ofReal_le_ofReal hlowerReal
  · calc
      ENNReal.ofReal (pureRootNBuresSqLossReal n h) ≤
          ENNReal.ofReal
            (pureQubitQuadraticLossReal h +
              pureBuresFourthRateReal n * tangentRadiusSq h ^ 2) :=
        ENNReal.ofReal_le_ofReal hupperReal
      _ = ENNReal.ofReal (pureQubitQuadraticLossReal h) +
          ENNReal.ofReal
            (pureBuresFourthRateReal n * tangentRadiusSq h ^ 2) :=
        ENNReal.ofReal_add hquadratic hremainder
      _ = pureQubitQuadraticLoss h +
          pureBuresFourthRate n * pureQubitFourthRadiusMoment h := by
        rw [pureBuresRemainderENNReal_eq]
        rfl

def pureGoodInfidelityRisk
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (good : Set Ω) (n : ℕ)
    (error : Ω → PureQubitTangent) : ℝ≥0∞ :=
  eventLIntegral mu good
    (fun omega => pureRootNInfidelityLoss n (error omega))

def pureGoodBuresSqRisk
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (good : Set Ω) (n : ℕ)
    (error : Ω → PureQubitTangent) : ℝ≥0∞ :=
  eventLIntegral mu good
    (fun omega => pureRootNBuresSqLoss n (error omega))

def pureGoodQuadraticRisk
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (good : Set Ω)
    (error : Ω → PureQubitTangent) : ℝ≥0∞ :=
  eventLIntegral mu good
    (fun omega => pureQubitQuadraticLoss (error omega))

/-- Infidelity has no local Taylor remainder in the normalized rank-one chart. -/
theorem pureGoodInfidelityRisk_eq_quadratic
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (good : Set Ω) (n : ℕ)
    (error : Ω → PureQubitTangent)
    (hchart : ∀ omega ∈ good,
      pureRootScale n ^ 2 * tangentRadiusSq (error omega) ≤ 4) :
    pureGoodInfidelityRisk mu good n error =
      pureGoodQuadraticRisk mu good error := by
  unfold pureGoodInfidelityRisk pureGoodQuadraticRisk eventLIntegral
  apply lintegral_congr
  intro omega
  by_cases homega : omega ∈ good
  · simp only [Set.indicator_of_mem homega]
    exact pureRootNInfidelityLoss_eq_quadratic
      n (error omega) (hchart omega homega)
  · simp [Set.indicator_of_notMem homega]

/-- Integrated good-event Bures comparison under a fourth-radius moment bound. -/
theorem pureGoodBuresSqRisk_bounds
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (good : Set Ω) (n : ℕ)
    (error : Ω → PureQubitTangent) (C4 : ℝ≥0∞)
    (hchart : ∀ omega ∈ good,
      pureRootScale n ^ 2 * tangentRadiusSq (error omega) ≤ 4)
    (hquadraticMeasurable : Measurable
      (good.indicator
        (fun omega => pureQubitQuadraticLoss (error omega))))
    (hfourthMeasurable : Measurable
      (good.indicator
        (fun omega => pureQubitFourthRadiusMoment (error omega))))
    (hfourthMoment :
      eventLIntegral mu good
        (fun omega => pureQubitFourthRadiusMoment (error omega)) ≤ C4) :
    pureGoodQuadraticRisk mu good error ≤
        pureGoodBuresSqRisk mu good n error ∧
      pureGoodBuresSqRisk mu good n error ≤
        pureGoodQuadraticRisk mu good error + pureBuresFourthRate n * C4 := by
  have hpointwise : ∀ omega,
      good.indicator
          (fun omega => pureQubitQuadraticLoss (error omega)) omega ≤
        good.indicator
          (fun omega => pureRootNBuresSqLoss n (error omega)) omega ∧
      good.indicator
          (fun omega => pureRootNBuresSqLoss n (error omega)) omega ≤
        good.indicator
            (fun omega => pureQubitQuadraticLoss (error omega)) omega +
          pureBuresFourthRate n *
            good.indicator
              (fun omega => pureQubitFourthRadiusMoment (error omega)) omega := by
    intro omega
    by_cases homega : omega ∈ good
    · simpa [Set.indicator_of_mem homega] using
        pureRootNBuresSqLoss_pointwise_bounds
          n (error omega) (hchart omega homega)
    · simp [Set.indicator_of_notMem homega]
  constructor
  · unfold pureGoodQuadraticRisk pureGoodBuresSqRisk eventLIntegral
    exact lintegral_mono (fun omega => (hpointwise omega).1)
  · unfold pureGoodBuresSqRisk pureGoodQuadraticRisk eventLIntegral
    calc
      (∫⁻ omega,
          good.indicator
            (fun omega => pureRootNBuresSqLoss n (error omega)) omega ∂mu) ≤
        ∫⁻ omega,
          good.indicator
              (fun omega => pureQubitQuadraticLoss (error omega)) omega +
            pureBuresFourthRate n *
              good.indicator
                (fun omega => pureQubitFourthRadiusMoment (error omega)) omega
          ∂mu := lintegral_mono (fun omega => (hpointwise omega).2)
      _ = pureGoodQuadraticRisk mu good error +
          pureBuresFourthRate n *
            eventLIntegral mu good
              (fun omega => pureQubitFourthRadiusMoment (error omega)) := by
        rw [lintegral_add_left hquadraticMeasurable,
          lintegral_const_mul _ hfourthMeasurable]
        rfl
      _ ≤ pureGoodQuadraticRisk mu good error +
          pureBuresFourthRate n * C4 := by
        gcongr

/-! ## Physical pure-state fallback on the bad event -/

def pureFallbackInfidelityLoss
    {Ω : Type*} (n : ℕ)
    (fallback : Ω → PureQubitStateVector) (omega : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal
    (pureNaturalSampleSizeReal n *
      pureQubitStateInfidelity (fallback omega))

def pureFallbackBuresSqLoss
    {Ω : Type*} (n : ℕ)
    (fallback : Ω → PureQubitStateVector) (omega : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal
    (pureNaturalSampleSizeReal n *
      pureQubitStateBuresSq (fallback omega))

theorem pureFallbackInfidelityLoss_le
    {Ω : Type*} (n : ℕ)
    (fallback : Ω → PureQubitStateVector) (omega : Ω)
    (hnormalized : pureStateNormSq (fallback omega) = 1) :
    pureFallbackInfidelityLoss n fallback omega ≤
      (pureNaturalSampleSize n : ℝ≥0∞) := by
  have hloss := (pureQubitState_losses_bounds
    (fallback omega) hnormalized).1.2
  have hN : 0 ≤ pureNaturalSampleSizeReal n :=
    (pureNaturalSampleSizeReal_pos n).le
  calc
    pureFallbackInfidelityLoss n fallback omega ≤
        ENNReal.ofReal (pureNaturalSampleSizeReal n * 1) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hloss hN)
    _ = (pureNaturalSampleSize n : ℝ≥0∞) := by
      norm_num [pureNaturalSampleSizeReal]

theorem pureFallbackBuresSqLoss_le
    {Ω : Type*} (n : ℕ)
    (fallback : Ω → PureQubitStateVector) (omega : Ω)
    (hnormalized : pureStateNormSq (fallback omega) = 1) :
    pureFallbackBuresSqLoss n fallback omega ≤
      (2 : ℝ≥0∞) * pureNaturalSampleSize n := by
  have hloss := (pureQubitState_losses_bounds
    (fallback omega) hnormalized).2.2
  have hN : 0 ≤ pureNaturalSampleSizeReal n :=
    (pureNaturalSampleSizeReal_pos n).le
  calc
    pureFallbackBuresSqLoss n fallback omega ≤
        ENNReal.ofReal (pureNaturalSampleSizeReal n * 2) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hloss hN)
    _ = (2 : ℝ≥0∞) * pureNaturalSampleSize n := by
      norm_num [pureNaturalSampleSizeReal, mul_comm]

def pureBadInfidelityRisk
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (bad : Set Ω) (n : ℕ)
    (fallback : Ω → PureQubitStateVector) : ℝ≥0∞ :=
  eventLIntegral mu bad (pureFallbackInfidelityLoss n fallback)

def pureBadBuresSqRisk
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (bad : Set Ω) (n : ℕ)
    (fallback : Ω → PureQubitStateVector) : ℝ≥0∞ :=
  eventLIntegral mu bad (pureFallbackBuresSqLoss n fallback)

theorem pureBadInfidelityRisk_le
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (bad : Set Ω) (hbad : MeasurableSet bad)
    (n : ℕ) (fallback : Ω → PureQubitStateVector)
    (hnormalized : ∀ omega ∈ bad,
      pureStateNormSq (fallback omega) = 1) :
    pureBadInfidelityRisk mu bad n fallback ≤
      (pureNaturalSampleSize n : ℝ≥0∞) * mu bad := by
  exact eventLIntegral_le_envelope_mul_measure
    mu bad hbad (pureFallbackInfidelityLoss n fallback)
    (pureNaturalSampleSize n : ℝ≥0∞)
    (fun omega homega =>
      pureFallbackInfidelityLoss_le n fallback omega
        (hnormalized omega homega))

theorem pureBadBuresSqRisk_le
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (bad : Set Ω) (hbad : MeasurableSet bad)
    (n : ℕ) (fallback : Ω → PureQubitStateVector)
    (hnormalized : ∀ omega ∈ bad,
      pureStateNormSq (fallback omega) = 1) :
    pureBadBuresSqRisk mu bad n fallback ≤
      ((2 : ℝ≥0∞) * pureNaturalSampleSize n) * mu bad := by
  exact eventLIntegral_le_envelope_mul_measure
    mu bad hbad (pureFallbackBuresSqLoss n fallback)
    ((2 : ℝ≥0∞) * pureNaturalSampleSize n)
    (fun omega homega =>
      pureFallbackBuresSqLoss_le n fallback omega
        (hnormalized omega homega))

private lemma pure_ennreal_mul_inv_sq_eq_inv
    {a : ℝ≥0∞} (ha : a ≠ 0) (hatop : a ≠ ⊤) :
    a * a⁻¹ ^ 2 = a⁻¹ := by
  rw [pow_two, ← mul_assoc, ENNReal.mul_inv_cancel ha hatop, one_mul]

/-- Algebraic cancellation used for both physical losses on the bad event. -/
theorem pure_sampleSize_mul_probability_le_inverse
    (n : ℕ) (growth probability tailConstant : ℝ≥0∞)
    (htail : probability ≤ tailConstant *
      ((pureNaturalSampleSize n : ℝ≥0∞)⁻¹) ^ 2) :
    growth * pureNaturalSampleSize n * probability ≤
      growth * tailConstant *
        (pureNaturalSampleSize n : ℝ≥0∞)⁻¹ := by
  let N : ℝ≥0∞ := pureNaturalSampleSize n
  have hNzero : N ≠ 0 := by
    simp [N, pureNaturalSampleSize]
  have hNtop : N ≠ ⊤ := by simp [N]
  calc
    growth * pureNaturalSampleSize n * probability ≤
        growth * N * (tailConstant * N⁻¹ ^ 2) := by
      gcongr
    _ = growth * tailConstant * (N * N⁻¹ ^ 2) := by ac_rfl
    _ = growth * tailConstant * N⁻¹ := by
      rw [pure_ennreal_mul_inv_sq_eq_inv hNzero hNtop]
    _ = growth * tailConstant *
        (pureNaturalSampleSize n : ℝ≥0∞)⁻¹ := rfl

def pureInfidelityBadTailRate
    (tailConstant : ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  tailConstant * (pureNaturalSampleSize n : ℝ≥0∞)⁻¹

def pureBuresBadTailRate
    (tailConstant : ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  2 * tailConstant * (pureNaturalSampleSize n : ℝ≥0∞)⁻¹

theorem pureBadInfidelityRisk_le_tailRate
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (bad : Set Ω) (hbad : MeasurableSet bad)
    (n : ℕ) (fallback : Ω → PureQubitStateVector)
    (hnormalized : ∀ omega ∈ bad,
      pureStateNormSq (fallback omega) = 1)
    (tailConstant : ℝ≥0∞)
    (hprobability : mu bad ≤ tailConstant *
      ((pureNaturalSampleSize n : ℝ≥0∞)⁻¹) ^ 2) :
    pureBadInfidelityRisk mu bad n fallback ≤
      pureInfidelityBadTailRate tailConstant n := by
  calc
    pureBadInfidelityRisk mu bad n fallback ≤
        (pureNaturalSampleSize n : ℝ≥0∞) * mu bad :=
      pureBadInfidelityRisk_le mu bad hbad n fallback hnormalized
    _ = (1 : ℝ≥0∞) * pureNaturalSampleSize n * mu bad := by rw [one_mul]
    _ ≤ (1 : ℝ≥0∞) * tailConstant *
        (pureNaturalSampleSize n : ℝ≥0∞)⁻¹ :=
      pure_sampleSize_mul_probability_le_inverse
        n 1 (mu bad) tailConstant hprobability
    _ = pureInfidelityBadTailRate tailConstant n := by
      simp [pureInfidelityBadTailRate]

theorem pureBadBuresSqRisk_le_tailRate
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (bad : Set Ω) (hbad : MeasurableSet bad)
    (n : ℕ) (fallback : Ω → PureQubitStateVector)
    (hnormalized : ∀ omega ∈ bad,
      pureStateNormSq (fallback omega) = 1)
    (tailConstant : ℝ≥0∞)
    (hprobability : mu bad ≤ tailConstant *
      ((pureNaturalSampleSize n : ℝ≥0∞)⁻¹) ^ 2) :
    pureBadBuresSqRisk mu bad n fallback ≤
      pureBuresBadTailRate tailConstant n := by
  calc
    pureBadBuresSqRisk mu bad n fallback ≤
        ((2 : ℝ≥0∞) * pureNaturalSampleSize n) * mu bad :=
      pureBadBuresSqRisk_le mu bad hbad n fallback hnormalized
    _ ≤ (2 : ℝ≥0∞) * tailConstant *
        (pureNaturalSampleSize n : ℝ≥0∞)⁻¹ :=
      pure_sampleSize_mul_probability_le_inverse
        n 2 (mu bad) tailConstant hprobability
    _ = pureBuresBadTailRate tailConstant n := rfl

/-! ## Full good/bad risks -/

def pureFullInfidelityRisk
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (good : Set Ω) (n : ℕ)
    (error : Ω → PureQubitTangent)
    (fallback : Ω → PureQubitStateVector) : ℝ≥0∞ :=
  pureGoodInfidelityRisk mu good n error +
    pureBadInfidelityRisk mu goodᶜ n fallback

def pureFullBuresSqRisk
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (good : Set Ω) (n : ℕ)
    (error : Ω → PureQubitTangent)
    (fallback : Ω → PureQubitStateVector) : ℝ≥0∞ :=
  pureGoodBuresSqRisk mu good n error +
    pureBadBuresSqRisk mu goodᶜ n fallback

def pureBuresRiskTransferError
    (C4 tailConstant : ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  pureBuresFourthRate n * C4 + pureBuresBadTailRate tailConstant n

/-- Finite-sample infidelity reduction. Its good branch is exactly quadratic. -/
theorem pureFullInfidelityRisk_bounds
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (good : Set Ω) (hgood : MeasurableSet good)
    (n : ℕ) (error : Ω → PureQubitTangent)
    (fallback : Ω → PureQubitStateVector)
    (tailConstant : ℝ≥0∞)
    (hchart : ∀ omega ∈ good,
      pureRootScale n ^ 2 * tangentRadiusSq (error omega) ≤ 4)
    (hnormalized : ∀ omega ∈ goodᶜ,
      pureStateNormSq (fallback omega) = 1)
    (hprobability : mu goodᶜ ≤ tailConstant *
      ((pureNaturalSampleSize n : ℝ≥0∞)⁻¹) ^ 2) :
    pureGoodQuadraticRisk mu good error ≤
        pureFullInfidelityRisk mu good n error fallback ∧
      pureFullInfidelityRisk mu good n error fallback ≤
        pureGoodQuadraticRisk mu good error +
          pureInfidelityBadTailRate tailConstant n := by
  have hgoodExact :=
    pureGoodInfidelityRisk_eq_quadratic mu good n error hchart
  have hbad := pureBadInfidelityRisk_le_tailRate
    mu goodᶜ hgood.compl n fallback hnormalized tailConstant hprobability
  constructor
  · rw [pureFullInfidelityRisk, hgoodExact]
    exact self_le_add_right _ _
  · rw [pureFullInfidelityRisk, hgoodExact]
    exact add_le_add_right hbad _

/-- Finite-sample squared-Bures reduction with its explicit fourth-moment and
bad-event errors. -/
theorem pureFullBuresSqRisk_bounds
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (good : Set Ω) (hgood : MeasurableSet good)
    (n : ℕ) (error : Ω → PureQubitTangent)
    (fallback : Ω → PureQubitStateVector)
    (C4 tailConstant : ℝ≥0∞)
    (hchart : ∀ omega ∈ good,
      pureRootScale n ^ 2 * tangentRadiusSq (error omega) ≤ 4)
    (hquadraticMeasurable : Measurable
      (good.indicator
        (fun omega => pureQubitQuadraticLoss (error omega))))
    (hfourthMeasurable : Measurable
      (good.indicator
        (fun omega => pureQubitFourthRadiusMoment (error omega))))
    (hfourthMoment :
      eventLIntegral mu good
        (fun omega => pureQubitFourthRadiusMoment (error omega)) ≤ C4)
    (hnormalized : ∀ omega ∈ goodᶜ,
      pureStateNormSq (fallback omega) = 1)
    (hprobability : mu goodᶜ ≤ tailConstant *
      ((pureNaturalSampleSize n : ℝ≥0∞)⁻¹) ^ 2) :
    pureGoodQuadraticRisk mu good error ≤
        pureFullBuresSqRisk mu good n error fallback ∧
      pureFullBuresSqRisk mu good n error fallback ≤
        pureGoodQuadraticRisk mu good error +
          pureBuresRiskTransferError C4 tailConstant n := by
  have hgoodBounds := pureGoodBuresSqRisk_bounds
    mu good n error C4 hchart hquadraticMeasurable hfourthMeasurable
      hfourthMoment
  have hbad := pureBadBuresSqRisk_le_tailRate
    mu goodᶜ hgood.compl n fallback hnormalized tailConstant hprobability
  constructor
  · unfold pureFullBuresSqRisk
    exact hgoodBounds.1.trans (self_le_add_right _ _)
  · unfold pureFullBuresSqRisk pureBuresRiskTransferError
    calc
      pureGoodBuresSqRisk mu good n error +
          pureBadBuresSqRisk mu goodᶜ n fallback ≤
        (pureGoodQuadraticRisk mu good error +
            pureBuresFourthRate n * C4) +
          pureBuresBadTailRate tailConstant n :=
        add_le_add hgoodBounds.2 hbad
      _ = pureGoodQuadraticRisk mu good error +
          (pureBuresFourthRate n * C4 +
            pureBuresBadTailRate tailConstant n) := by ac_rfl

/-! ## Vanishing rates -/

theorem pureNaturalSampleSizeReal_tendsto_atTop :
    Tendsto pureNaturalSampleSizeReal atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards
    [(tendsto_atTop.1 tendsto_natCast_atTop_atTop) b] with n hn
  dsimp [pureNaturalSampleSizeReal, pureNaturalSampleSize]
  exact hn.trans (by norm_num)

theorem pureBuresFourthRateReal_tendsto_zero :
    Tendsto pureBuresFourthRateReal atTop (nhds 0) := by
  change Tendsto
    (fun n => (pureNaturalSampleSizeReal n)⁻¹ / 16) atTop (nhds 0)
  have hinv : Tendsto
      (fun n => (pureNaturalSampleSizeReal n)⁻¹)
      atTop (nhds 0) :=
    pureNaturalSampleSizeReal_tendsto_atTop.inv_tendsto_atTop
  simpa [pureBuresFourthRateReal, div_eq_mul_inv, mul_comm] using
    (tendsto_const_nhds.mul hinv :
      Tendsto
        (fun n => (1 / 16 : ℝ) * (pureNaturalSampleSizeReal n)⁻¹)
        atTop (nhds ((1 / 16 : ℝ) * 0)))

theorem pureBuresFourthRate_tendsto_zero :
    Tendsto pureBuresFourthRate atTop (nhds 0) := by
  change Tendsto
    (fun n => ENNReal.ofReal (pureBuresFourthRateReal n)) atTop (nhds 0)
  simpa [Function.comp_def] using
    ((ENNReal.continuous_ofReal.tendsto 0).comp
      pureBuresFourthRateReal_tendsto_zero)

theorem pureNaturalSampleSize_inv_tendsto_zero :
    Tendsto
      (fun n => (pureNaturalSampleSize n : ℝ≥0∞)⁻¹)
      atTop (nhds 0) := by
  have hshift : Tendsto pureNaturalSampleSize atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    exact hn.trans (Nat.le_add_right n 1)
  simpa [Function.comp_def] using
    ENNReal.tendsto_inv_nat_nhds_zero.comp hshift

theorem pureInfidelityBadTailRate_tendsto_zero
    {tailConstant : ℝ≥0∞} (hfinite : tailConstant ≠ ⊤) :
    Tendsto (pureInfidelityBadTailRate tailConstant) atTop (nhds 0) := by
  change Tendsto
    (fun n => tailConstant *
      (pureNaturalSampleSize n : ℝ≥0∞)⁻¹) atTop (nhds 0)
  simpa [Function.comp_def] using
    ((ENNReal.continuousAt_const_mul
      (a := tailConstant) (b := 0) (Or.inl hfinite)).tendsto.comp
        pureNaturalSampleSize_inv_tendsto_zero)

theorem pureBuresBadTailRate_tendsto_zero
    {tailConstant : ℝ≥0∞} (hfinite : tailConstant ≠ ⊤) :
    Tendsto (pureBuresBadTailRate tailConstant) atTop (nhds 0) := by
  have hconstant : (2 : ℝ≥0∞) * tailConstant ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by norm_num) hfinite
  change Tendsto
    (fun n => 2 * tailConstant *
      (pureNaturalSampleSize n : ℝ≥0∞)⁻¹) atTop (nhds 0)
  simpa [Function.comp_def, mul_assoc] using
    ((ENNReal.continuousAt_const_mul
      (a := (2 : ℝ≥0∞) * tailConstant) (b := 0)
      (Or.inl hconstant)).tendsto.comp
        pureNaturalSampleSize_inv_tendsto_zero)

theorem pureBuresRiskTransferError_tendsto_zero
    {C4 tailConstant : ℝ≥0∞}
    (hC4 : C4 ≠ ⊤) (hTail : tailConstant ≠ ⊤) :
    Tendsto (pureBuresRiskTransferError C4 tailConstant)
      atTop (nhds 0) := by
  have hfourth : Tendsto (fun n => pureBuresFourthRate n * C4)
      atTop (nhds 0) := by
    simpa [Function.comp_def, mul_comm] using
      ((ENNReal.continuousAt_const_mul
        (a := C4) (b := 0) (Or.inl hC4)).tendsto.comp
          pureBuresFourthRate_tendsto_zero)
  have hbad := pureBuresBadTailRate_tendsto_zero hTail
  change Tendsto
    (fun n => pureBuresFourthRate n * C4 +
      pureBuresBadTailRate tailConstant n) atTop (nhds 0)
  simpa only [add_zero] using hfourth.add hbad

/-! ## Separate asymptotic endpoints -/

/-- Honest infidelity endpoint.  The local infidelity is exactly quadratic;
only the physical fallback on the bad event contributes an error. -/
theorem pureInfidelityRisk_tendsto_of_quadratic
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : ℕ → Measure Ω) (good : ℕ → Set Ω)
    (error : ℕ → Ω → PureQubitTangent)
    (fallback : ℕ → Ω → PureQubitStateVector)
    (tailConstant benchmark : ℝ≥0∞)
    (hTail : tailConstant ≠ ⊤)
    (hgood : ∀ n, MeasurableSet (good n))
    (hchart : ∀ n omega, omega ∈ good n →
      pureRootScale n ^ 2 * tangentRadiusSq (error n omega) ≤ 4)
    (hnormalized : ∀ n omega, omega ∈ (good n)ᶜ →
      pureStateNormSq (fallback n omega) = 1)
    (hprobability : ∀ n,
      mu n (good n)ᶜ ≤ tailConstant *
        ((pureNaturalSampleSize n : ℝ≥0∞)⁻¹) ^ 2)
    (hQuadraticRisk : Tendsto
      (fun n => pureGoodQuadraticRisk (mu n) (good n) (error n))
      atTop (nhds benchmark)) :
    Tendsto
      (fun n => pureFullInfidelityRisk
        (mu n) (good n) n (error n) (fallback n))
      atTop (nhds benchmark) := by
  have herror := pureInfidelityBadTailRate_tendsto_zero hTail
  have hupper : Tendsto
      (fun n => pureGoodQuadraticRisk (mu n) (good n) (error n) +
        pureInfidelityBadTailRate tailConstant n)
      atTop (nhds benchmark) := by
    simpa using hQuadraticRisk.add herror
  refine Tendsto.squeeze hQuadraticRisk hupper ?_ ?_
  · intro n
    exact (pureFullInfidelityRisk_bounds
      (mu n) (good n) (hgood n) n (error n) (fallback n) tailConstant
      (fun omega homega => hchart n omega homega)
      (fun omega homega => hnormalized n omega homega)
      (hprobability n)).1
  · intro n
    exact (pureFullInfidelityRisk_bounds
      (mu n) (good n) (hgood n) n (error n) (fallback n) tailConstant
      (fun omega homega => hchart n omega homega)
      (fun omega homega => hnormalized n omega homega)
      (hprobability n)).2

/-- Honest squared-Bures endpoint.  Unlike infidelity, it includes the proved
fourth-order local remainder as well as the physical bad-event contribution. -/
theorem pureBuresSqRisk_tendsto_of_quadratic
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : ℕ → Measure Ω) (good : ℕ → Set Ω)
    (error : ℕ → Ω → PureQubitTangent)
    (fallback : ℕ → Ω → PureQubitStateVector)
    (C4 tailConstant benchmark : ℝ≥0∞)
    (hC4 : C4 ≠ ⊤) (hTail : tailConstant ≠ ⊤)
    (hgood : ∀ n, MeasurableSet (good n))
    (hchart : ∀ n omega, omega ∈ good n →
      pureRootScale n ^ 2 * tangentRadiusSq (error n omega) ≤ 4)
    (hquadraticMeasurable : ∀ n, Measurable
      ((good n).indicator
        (fun omega => pureQubitQuadraticLoss (error n omega))))
    (hfourthMeasurable : ∀ n, Measurable
      ((good n).indicator
        (fun omega => pureQubitFourthRadiusMoment (error n omega))))
    (hfourthMoment : ∀ n,
      eventLIntegral (mu n) (good n)
        (fun omega => pureQubitFourthRadiusMoment (error n omega)) ≤ C4)
    (hnormalized : ∀ n omega, omega ∈ (good n)ᶜ →
      pureStateNormSq (fallback n omega) = 1)
    (hprobability : ∀ n,
      mu n (good n)ᶜ ≤ tailConstant *
        ((pureNaturalSampleSize n : ℝ≥0∞)⁻¹) ^ 2)
    (hQuadraticRisk : Tendsto
      (fun n => pureGoodQuadraticRisk (mu n) (good n) (error n))
      atTop (nhds benchmark)) :
    Tendsto
      (fun n => pureFullBuresSqRisk
        (mu n) (good n) n (error n) (fallback n))
      atTop (nhds benchmark) := by
  have herror := pureBuresRiskTransferError_tendsto_zero hC4 hTail
  have hupper : Tendsto
      (fun n => pureGoodQuadraticRisk (mu n) (good n) (error n) +
        pureBuresRiskTransferError C4 tailConstant n)
      atTop (nhds benchmark) := by
    simpa using hQuadraticRisk.add herror
  refine Tendsto.squeeze hQuadraticRisk hupper ?_ ?_
  · intro n
    exact (pureFullBuresSqRisk_bounds
      (mu n) (good n) (hgood n) n (error n) (fallback n)
      C4 tailConstant
      (fun omega homega => hchart n omega homega)
      (hquadraticMeasurable n) (hfourthMeasurable n)
      (hfourthMoment n)
      (fun omega homega => hnormalized n omega homega)
      (hprobability n)).1
  · intro n
    exact (pureFullBuresSqRisk_bounds
      (mu n) (good n) (hgood n) n (error n) (fallback n)
      C4 tailConstant
      (fun omega homega => hchart n omega homega)
      (hquadraticMeasurable n) (hfourthMeasurable n)
      (hfourthMoment n)
      (fun omega homega => hnormalized n omega homega)
      (hprobability n)).2

end

end QubitOracle.Paper
