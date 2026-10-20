import QubitOracle.Paper.OneQubitMixedBuresFullRemainder
import QubitOracle.Paper.OneQubitBadEventMomentTransfer
import QubitOracle.Paper.EventLIntegralCore

open scoped ENNReal Topology
open Filter MeasureTheory Set

namespace QubitOracle.Paper

noncomputable section

/-!
# One-qubit mixed Bures risk transfer

This file keeps the local and fallback contributions separate.

* On a measurable good event, the general-direction mixed-qubit remainder is
  integrated against explicit third- and fourth-radius moments.
* On the complementary event, the physical Bures loss is bounded globally by
  `2 N`, while the existing physical fallback theorem bounds the normalized
  squared Bloch error by `4 N`.
* A quadratic probability envelope for the bad event therefore leaves an
  explicit `O(N⁻¹)` contribution.

The final declaration is a convergence *reduction*: it proves asymptotic
risk-equivalence between the physical Bures risk and the quadratic comparator.
Consequently the only remaining statistical input is convergence of that
quadratic comparator (for example, from LAN plus moment control). No physical
risk limit is assumed below.
-/

abbrev MixedQubitVector := Fin 3 → ℝ

def mixedBuresNaturalSampleSize (n : ℕ) : ℕ := n + 1

def mixedBuresNaturalSampleSizeReal (n : ℕ) : ℝ :=
  mixedBuresNaturalSampleSize n

lemma mixedBuresNaturalSampleSize_pos (n : ℕ) :
    0 < mixedBuresNaturalSampleSize n := by
  simp [mixedBuresNaturalSampleSize]

lemma mixedBuresNaturalSampleSizeReal_pos (n : ℕ) :
    0 < mixedBuresNaturalSampleSizeReal n := by
  unfold mixedBuresNaturalSampleSizeReal
  exact_mod_cast mixedBuresNaturalSampleSize_pos n

/-- The coefficient of the cubic-radius moment in the local remainder. -/
def mixedBuresCubicRateReal (margin : ℝ) (n : ℕ) : ℝ :=
  1 / (margin ^ 2 * Real.sqrt (mixedBuresNaturalSampleSizeReal n))

/-- The coefficient of the fourth-radius moment in the local remainder. -/
def mixedBuresQuarticRateReal (margin : ℝ) (n : ℕ) : ℝ :=
  2 / (margin ^ 3 * mixedBuresNaturalSampleSizeReal n)

def mixedBuresCubicRate (margin : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (mixedBuresCubicRateReal margin n)

def mixedBuresQuarticRate (margin : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (mixedBuresQuarticRateReal margin n)

def mixedBuresThirdRadiusMoment (R : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (R ^ 3)

def mixedBuresFourthRadiusMoment (R : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (R ^ 4)

def mixedBuresNaturalPhysicalLoss
    (n : ℕ) (theta h : MixedQubitVector) : ℝ≥0∞ :=
  ENNReal.ofReal
    (mixedGeneralRootNBuresLossReal
      (mixedBuresNaturalSampleSizeReal n) theta h)

def mixedBuresQuadraticLoss
    (theta h : MixedQubitVector) : ℝ≥0∞ :=
  ENNReal.ofReal (mixedQubitBuresQuadraticAt theta h)

/-- Restriction of a nonnegative loss to an event, written without changing the
ambient measure. -/
def mixedLossOnEvent {Ω : Type*}
    (event : Set Ω) (loss : Ω → ℝ≥0∞) : Ω → ℝ≥0∞ :=
  event.indicator loss

private lemma ofReal_le_ofReal_add_of_le_add
    {a b d : ℝ} (hd : 0 ≤ d) (h : a ≤ b + d) :
    ENNReal.ofReal a ≤ ENNReal.ofReal b + ENNReal.ofReal d := by
  by_cases hb : 0 ≤ b
  · calc
      ENNReal.ofReal a ≤ ENNReal.ofReal (b + d) :=
        ENNReal.ofReal_le_ofReal h
      _ = ENNReal.ofReal b + ENNReal.ofReal d :=
        ENNReal.ofReal_add hb hd
  · have had : a ≤ d := by linarith
    calc
      ENNReal.ofReal a ≤ ENNReal.ofReal d :=
        ENNReal.ofReal_le_ofReal had
      _ ≤ ENNReal.ofReal b + ENNReal.ofReal d := self_le_add_left _ _

private lemma mixedBuresRemainderEnvelope_eq
    {margin R : ℝ} {n : ℕ}
    (hmargin : 0 < margin) (hR : 0 ≤ R) :
    ENNReal.ofReal
        (R ^ 3 /
            (margin ^ 2 *
              Real.sqrt (mixedBuresNaturalSampleSizeReal n)) +
          2 * R ^ 4 /
            (margin ^ 3 * mixedBuresNaturalSampleSizeReal n)) =
      mixedBuresCubicRate margin n * mixedBuresThirdRadiusMoment R +
        mixedBuresQuarticRate margin n * mixedBuresFourthRadiusMoment R := by
  have hN : 0 < mixedBuresNaturalSampleSizeReal n :=
    mixedBuresNaturalSampleSizeReal_pos n
  have hsqrt : 0 < Real.sqrt (mixedBuresNaturalSampleSizeReal n) :=
    Real.sqrt_pos.2 hN
  have hcubic :
      0 ≤ 1 /
        (margin ^ 2 * Real.sqrt (mixedBuresNaturalSampleSizeReal n)) := by
    positivity
  have hquartic :
      0 ≤ 2 / (margin ^ 3 * mixedBuresNaturalSampleSizeReal n) := by
    positivity
  have hR3 : 0 ≤ R ^ 3 := pow_nonneg hR 3
  have hR4 : 0 ≤ R ^ 4 := pow_nonneg hR 4
  have hcubicTerm :
      0 ≤ R ^ 3 /
        (margin ^ 2 * Real.sqrt (mixedBuresNaturalSampleSizeReal n)) := by
    positivity
  have hquarticTerm :
      0 ≤ 2 * R ^ 4 /
        (margin ^ 3 * mixedBuresNaturalSampleSizeReal n) := by
    positivity
  rw [ENNReal.ofReal_add hcubicTerm hquarticTerm]
  change
    ENNReal.ofReal
          (R ^ 3 /
            (margin ^ 2 * Real.sqrt (mixedBuresNaturalSampleSizeReal n))) +
        ENNReal.ofReal
          (2 * R ^ 4 /
            (margin ^ 3 * mixedBuresNaturalSampleSizeReal n)) = _
  rw [show
      R ^ 3 /
          (margin ^ 2 * Real.sqrt (mixedBuresNaturalSampleSizeReal n)) =
        (1 /
          (margin ^ 2 * Real.sqrt (mixedBuresNaturalSampleSizeReal n))) *
            R ^ 3 by ring]
  rw [show
      2 * R ^ 4 /
          (margin ^ 3 * mixedBuresNaturalSampleSizeReal n) =
        (2 / (margin ^ 3 * mixedBuresNaturalSampleSizeReal n)) * R ^ 4 by
          ring]
  rw [ENNReal.ofReal_mul hcubic, ENNReal.ofReal_mul hquartic]
  rfl

/-- Concrete ENNReal form of the full real two-sided Taylor bound. The random
radius may vary pointwise; it only has to dominate the squared Bloch norm and
satisfy the displayed local condition. -/
theorem mixedBuresGoodPointwise_twoSided
    {margin R : ℝ} {n : ℕ} {theta h : MixedQubitVector}
    (hmargin : 0 < margin)
    (hinterior : MixedQubitInteriorWithMargin margin theta)
    (hR : 0 ≤ R)
    (hradius : blochNormSq h ≤ R ^ 2)
    (hlocal :
      2 * R / Real.sqrt (mixedBuresNaturalSampleSizeReal n) +
          R ^ 2 / mixedBuresNaturalSampleSizeReal n ≤ margin / 2) :
    mixedBuresNaturalPhysicalLoss n theta h ≤
        mixedBuresQuadraticLoss theta h +
          mixedBuresCubicRate margin n * mixedBuresThirdRadiusMoment R +
          mixedBuresQuarticRate margin n * mixedBuresFourthRadiusMoment R ∧
      mixedBuresQuadraticLoss theta h ≤
        mixedBuresNaturalPhysicalLoss n theta h +
          mixedBuresCubicRate margin n * mixedBuresThirdRadiusMoment R +
          mixedBuresQuarticRate margin n * mixedBuresFourthRadiusMoment R := by
  let physical :=
    mixedGeneralRootNBuresLossReal
      (mixedBuresNaturalSampleSizeReal n) theta h
  let quadratic := mixedQubitBuresQuadraticAt theta h
  let remainder :=
    R ^ 3 /
        (margin ^ 2 * Real.sqrt (mixedBuresNaturalSampleSizeReal n)) +
      2 * R ^ 4 /
        (margin ^ 3 * mixedBuresNaturalSampleSizeReal n)
  have habs : |physical - quadratic| ≤ remainder := by
    simpa [physical, quadratic, remainder] using
      mixedGeneralRootNBuresLossReal_abs_remainder
        (N := mixedBuresNaturalSampleSizeReal n)
        (margin := margin) (R := R) (theta := theta) (h := h)
        (mixedBuresNaturalSampleSizeReal_pos n) hinterior hR hradius hlocal
  have hrem : 0 ≤ remainder := by
    dsimp [remainder]
    exact add_nonneg
      (div_nonneg (pow_nonneg hR 3)
        (mul_nonneg (sq_nonneg margin)
          (Real.sqrt_nonneg _)))
      (div_nonneg
        (mul_nonneg (by norm_num) (pow_nonneg hR 4))
        (mul_nonneg (pow_nonneg hmargin.le 3)
          (mixedBuresNaturalSampleSizeReal_pos n).le))
  have hpq : physical ≤ quadratic + remainder := by
    have hdiff : physical - quadratic ≤ remainder :=
      (le_abs_self (physical - quadratic)).trans habs
    linarith
  have habs' : |quadratic - physical| ≤ remainder := by
    simpa [abs_sub_comm] using habs
  have hqp : quadratic ≤ physical + remainder := by
    have hdiff : quadratic - physical ≤ remainder :=
      (le_abs_self (quadratic - physical)).trans habs'
    linarith
  have henvelope :=
    mixedBuresRemainderEnvelope_eq
      (n := n) (hmargin := hmargin) (hR := hR)
  constructor
  · change ENNReal.ofReal physical ≤ _
    calc
      ENNReal.ofReal physical ≤
          ENNReal.ofReal quadratic + ENNReal.ofReal remainder :=
        ofReal_le_ofReal_add_of_le_add hrem hpq
      _ = _ := by
        rw [henvelope]
        simp [quadratic, mixedBuresQuadraticLoss, add_assoc]
  · change ENNReal.ofReal quadratic ≤ _
    calc
      ENNReal.ofReal quadratic ≤
          ENNReal.ofReal physical + ENNReal.ofReal remainder :=
        ofReal_le_ofReal_add_of_le_add hrem hqp
      _ = _ := by
        rw [henvelope]
        simp [physical, mixedBuresNaturalPhysicalLoss, add_assoc]

/-- The good-event expected-risk comparison. Its assumptions are exactly
measurability, the proved pointwise local-radius conditions, and restricted
third/fourth moment bounds. -/
theorem mixedBuresGoodEventExpectedRisk_twoSided
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (good : Set Ω)
    (n : ℕ) (margin : ℝ) (theta : MixedQubitVector)
    (error : Ω → MixedQubitVector) (radius : Ω → ℝ)
    (C3 C4 : ℝ≥0∞)
    (hmargin : 0 < margin)
    (hinterior : MixedQubitInteriorWithMargin margin theta)
    (hradiusNonnegative : ∀ omega ∈ good, 0 ≤ radius omega)
    (hradiusDominates :
      ∀ omega ∈ good, blochNormSq (error omega) ≤ radius omega ^ 2)
    (hlocal : ∀ omega ∈ good,
      2 * radius omega /
            Real.sqrt (mixedBuresNaturalSampleSizeReal n) +
          radius omega ^ 2 / mixedBuresNaturalSampleSizeReal n ≤ margin / 2)
    (hphysicalMeasurable : Measurable
      (mixedLossOnEvent good
        (fun omega => mixedBuresNaturalPhysicalLoss n theta (error omega))))
    (hquadraticMeasurable : Measurable
      (mixedLossOnEvent good
        (fun omega => mixedBuresQuadraticLoss theta (error omega))))
    (hthirdMeasurable : Measurable
      (mixedLossOnEvent good
        (fun omega => mixedBuresThirdRadiusMoment (radius omega))))
    (hfourthMeasurable : Measurable
      (mixedLossOnEvent good
        (fun omega => mixedBuresFourthRadiusMoment (radius omega))))
    (hthirdMoment :
      (∫⁻ omega,
        mixedLossOnEvent good
          (fun omega => mixedBuresThirdRadiusMoment (radius omega)) omega ∂mu) ≤ C3)
    (hfourthMoment :
      (∫⁻ omega,
        mixedLossOnEvent good
          (fun omega => mixedBuresFourthRadiusMoment (radius omega)) omega ∂mu) ≤ C4) :
    (∫⁻ omega,
        mixedLossOnEvent good
          (fun omega => mixedBuresNaturalPhysicalLoss n theta (error omega))
          omega ∂mu) ≤
        (∫⁻ omega,
          mixedLossOnEvent good
            (fun omega => mixedBuresQuadraticLoss theta (error omega))
            omega ∂mu) +
          mixedBuresCubicRate margin n * C3 +
          mixedBuresQuarticRate margin n * C4 ∧
      (∫⁻ omega,
        mixedLossOnEvent good
          (fun omega => mixedBuresQuadraticLoss theta (error omega))
          omega ∂mu) ≤
        (∫⁻ omega,
          mixedLossOnEvent good
            (fun omega => mixedBuresNaturalPhysicalLoss n theta (error omega))
            omega ∂mu) +
          mixedBuresCubicRate margin n * C3 +
          mixedBuresQuarticRate margin n * C4 := by
  let physical : Ω → ℝ≥0∞ :=
    mixedLossOnEvent good
      (fun omega => mixedBuresNaturalPhysicalLoss n theta (error omega))
  let quadratic : Ω → ℝ≥0∞ :=
    mixedLossOnEvent good
      (fun omega => mixedBuresQuadraticLoss theta (error omega))
  let third : Ω → ℝ≥0∞ :=
    mixedLossOnEvent good
      (fun omega => mixedBuresThirdRadiusMoment (radius omega))
  let fourth : Ω → ℝ≥0∞ :=
    mixedLossOnEvent good
      (fun omega => mixedBuresFourthRadiusMoment (radius omega))
  let combined : Ω → ℝ≥0∞ := fun omega =>
    mixedBuresCubicRate margin n * third omega +
      mixedBuresQuarticRate margin n * fourth omega
  have hcombinedMeasurable : Measurable combined := by
    exact (measurable_const.mul hthirdMeasurable).add
      (measurable_const.mul hfourthMeasurable)
  have hcombinedMoment : (∫⁻ omega, combined omega ∂mu) ≤
      mixedBuresCubicRate margin n * C3 +
        mixedBuresQuarticRate margin n * C4 := by
    calc
      (∫⁻ omega, combined omega ∂mu) =
          (∫⁻ omega, mixedBuresCubicRate margin n * third omega ∂mu) +
            (∫⁻ omega, mixedBuresQuarticRate margin n * fourth omega ∂mu) := by
        change (∫⁻ omega,
          mixedBuresCubicRate margin n * third omega +
            mixedBuresQuarticRate margin n * fourth omega ∂mu) = _
        exact lintegral_add_left (μ := mu)
          (measurable_const.mul hthirdMeasurable)
          (fun omega => mixedBuresQuarticRate margin n * fourth omega)
      _ = mixedBuresCubicRate margin n * (∫⁻ omega, third omega ∂mu) +
            mixedBuresQuarticRate margin n * (∫⁻ omega, fourth omega ∂mu) := by
        rw [lintegral_const_mul _ hthirdMeasurable,
          lintegral_const_mul _ hfourthMeasurable]
      _ ≤ mixedBuresCubicRate margin n * C3 +
            mixedBuresQuarticRate margin n * C4 :=
        add_le_add
          (by gcongr)
          (by gcongr)
  have hpointwise : ∀ omega,
      physical omega ≤ quadratic omega + combined omega ∧
        quadratic omega ≤ physical omega + combined omega := by
    intro omega
    by_cases homega : omega ∈ good
    · simpa [physical, quadratic, third, fourth, combined,
          mixedLossOnEvent, homega, add_assoc] using
        mixedBuresGoodPointwise_twoSided
          (n := n) (margin := margin) (R := radius omega)
          (theta := theta) (h := error omega)
          hmargin hinterior
          (hradiusNonnegative omega homega)
          (hradiusDominates omega homega)
          (hlocal omega homega)
    · simp [physical, quadratic, third, fourth, combined,
        mixedLossOnEvent, homega]
  have htransfer :=
    lintegral_twoSidedRiskTransfer
      mu physical quadratic combined 1
      (mixedBuresCubicRate margin n * C3 +
        mixedBuresQuarticRate margin n * C4)
      hphysicalMeasurable hquadraticMeasurable hcombinedMeasurable
      (by simpa using hpointwise) hcombinedMoment
  simpa [physical, quadratic, combined, one_mul, add_assoc] using htransfer

/-- The natural sample sizes tend to infinity after coercion to `ℝ`. -/
lemma mixedBuresNaturalSampleSizeReal_tendsto_atTop :
    Tendsto mixedBuresNaturalSampleSizeReal atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards
    [(tendsto_atTop.1 tendsto_natCast_atTop_atTop) b] with n hn
  dsimp [mixedBuresNaturalSampleSizeReal, mixedBuresNaturalSampleSize]
  exact hn.trans (by norm_num)

/-- The cubic rate vanishes for `N = n + 1`. -/
theorem mixedBuresCubicRateReal_tendsto_zero
    {margin : ℝ} (hmargin : 0 < margin) :
    Tendsto (mixedBuresCubicRateReal margin) atTop (nhds 0) := by
  change Tendsto
    (fun n => 1 /
      (margin ^ 2 * Real.sqrt (mixedBuresNaturalSampleSizeReal n)))
    atTop (nhds 0)
  have hsqrt : Tendsto
      (fun n => Real.sqrt (mixedBuresNaturalSampleSizeReal n))
      atTop atTop :=
    Real.tendsto_sqrt_atTop.comp mixedBuresNaturalSampleSizeReal_tendsto_atTop
  have hinv : Tendsto
      (fun n => (Real.sqrt (mixedBuresNaturalSampleSizeReal n))⁻¹)
      atTop (nhds 0) := hsqrt.inv_tendsto_atTop
  simpa [mixedBuresCubicRateReal, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc] using
    (tendsto_const_nhds.mul hinv :
      Tendsto
        (fun n => (1 / margin ^ 2) *
          (Real.sqrt (mixedBuresNaturalSampleSizeReal n))⁻¹)
        atTop (nhds ((1 / margin ^ 2) * 0)))

/-- The quartic rate vanishes for `N = n + 1`. -/
theorem mixedBuresQuarticRateReal_tendsto_zero
    {margin : ℝ} (hmargin : 0 < margin) :
    Tendsto (mixedBuresQuarticRateReal margin) atTop (nhds 0) := by
  change Tendsto
    (fun n => 2 / (margin ^ 3 * mixedBuresNaturalSampleSizeReal n))
    atTop (nhds 0)
  have hinv : Tendsto
      (fun n => (mixedBuresNaturalSampleSizeReal n)⁻¹)
      atTop (nhds 0) :=
    mixedBuresNaturalSampleSizeReal_tendsto_atTop.inv_tendsto_atTop
  simpa [mixedBuresQuarticRateReal, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc] using
    (tendsto_const_nhds.mul hinv :
      Tendsto
        (fun n => (2 / margin ^ 3) *
          (mixedBuresNaturalSampleSizeReal n)⁻¹)
        atTop (nhds ((2 / margin ^ 3) * 0)))

theorem mixedBuresCubicRate_tendsto_zero
    {margin : ℝ} (hmargin : 0 < margin) :
    Tendsto (mixedBuresCubicRate margin) atTop (nhds 0) := by
  change Tendsto
    (fun n => ENNReal.ofReal (mixedBuresCubicRateReal margin n))
    atTop (nhds 0)
  simpa [mixedBuresCubicRate, Function.comp_def] using
    ((ENNReal.continuous_ofReal.tendsto 0).comp
      (mixedBuresCubicRateReal_tendsto_zero hmargin))

theorem mixedBuresQuarticRate_tendsto_zero
    {margin : ℝ} (hmargin : 0 < margin) :
    Tendsto (mixedBuresQuarticRate margin) atTop (nhds 0) := by
  change Tendsto
    (fun n => ENNReal.ofReal (mixedBuresQuarticRateReal margin n))
    atTop (nhds 0)
  simpa [mixedBuresQuarticRate, Function.comp_def] using
    ((ENNReal.continuous_ofReal.tendsto 0).comp
      (mixedBuresQuarticRateReal_tendsto_zero hmargin))

/-- The exact qubit Bures-squared expression never exceeds two. This upper
bound needs no Taylor expansion. -/
theorem mixedBlochBuresSq_le_two
    (theta delta : MixedQubitVector) :
    mixedBlochBuresSq theta delta ≤ 2 := by
  unfold mixedBlochBuresSq qubitBlochBuresSq
  nlinarith [Real.sqrt_nonneg
    (qubitBlochFidelitySq (blochNormSq theta)
      (blochDot theta delta) (blochNormSq delta))]

/-- Physical Bures loss of a fallback Bloch vector, scaled by `N = n + 1`. -/
def mixedFallbackBuresPhysicalLoss {Ω : Type*}
    (n : ℕ) (fallback : Ω → MixedQubitVector)
    (truth : MixedQubitVector) (omega : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal
    (mixedBuresNaturalSampleSizeReal n *
      mixedBlochBuresSq truth
        (fun i => fallback omega i - truth i))

lemma mixedFallbackBuresPhysicalLoss_le
    {Ω : Type*} (n : ℕ) (fallback : Ω → MixedQubitVector)
    (truth : MixedQubitVector) (omega : Ω) :
    mixedFallbackBuresPhysicalLoss n fallback truth omega ≤
      (2 : ℝ≥0∞) * mixedBuresNaturalSampleSize n := by
  have hN : 0 ≤ mixedBuresNaturalSampleSizeReal n :=
    (mixedBuresNaturalSampleSizeReal_pos n).le
  have hreal :
      mixedBuresNaturalSampleSizeReal n *
          mixedBlochBuresSq truth
            (fun i => fallback omega i - truth i) ≤
        2 * mixedBuresNaturalSampleSizeReal n := by
    simpa [mul_comm] using mul_le_mul_of_nonneg_left
      (mixedBlochBuresSq_le_two truth
        (fun i => fallback omega i - truth i)) hN
  calc
    mixedFallbackBuresPhysicalLoss n fallback truth omega ≤
        ENNReal.ofReal (2 * mixedBuresNaturalSampleSizeReal n) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = (2 : ℝ≥0∞) * mixedBuresNaturalSampleSize n := by
      norm_num [mixedBuresNaturalSampleSizeReal]

private theorem lintegral_lossOnEvent_le_const_mul_measure
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (event : Set Ω) (loss : Ω → ℝ≥0∞)
    (C : ℝ≥0∞) (hevent : MeasurableSet event)
    (hbound : ∀ omega ∈ event, loss omega ≤ C) :
    (∫⁻ omega, mixedLossOnEvent event loss omega ∂mu) ≤ C * mu event := by
  calc
    (∫⁻ omega, mixedLossOnEvent event loss omega ∂mu) ≤
        ∫⁻ omega, mixedLossOnEvent event (fun _ => C) omega ∂mu := by
      apply lintegral_mono
      intro omega
      by_cases homega : omega ∈ event
      · simpa [mixedLossOnEvent, homega] using hbound omega homega
      · simp [mixedLossOnEvent, homega]
    _ = C * mu event := by
      simp [mixedLossOnEvent, hevent]

/-- The bad-event physical Bures contribution has the global `2 N` envelope. -/
theorem mixedFallbackBuresBadEventLIntegral_le
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (bad : Set Ω) (hbad : MeasurableSet bad)
    (n : ℕ) (fallback : Ω → MixedQubitVector)
    (truth : MixedQubitVector) :
    (∫⁻ omega,
      mixedLossOnEvent bad
        (mixedFallbackBuresPhysicalLoss n fallback truth) omega ∂mu) ≤
      ((2 : ℝ≥0∞) * mixedBuresNaturalSampleSize n) * mu bad := by
  exact lintegral_lossOnEvent_le_const_mul_measure
    mu bad (mixedFallbackBuresPhysicalLoss n fallback truth)
    ((2 : ℝ≥0∞) * mixedBuresNaturalSampleSize n) hbad
    (fun omega _homega =>
      mixedFallbackBuresPhysicalLoss_le n fallback truth omega)

private lemma ennreal_mul_inv_sq_eq_inv
    {a : ℝ≥0∞} (ha : a ≠ 0) (hatop : a ≠ ⊤) :
    a * a⁻¹ ^ 2 = a⁻¹ := by
  rw [pow_two, ← mul_assoc, ENNReal.mul_inv_cancel ha hatop, one_mul]

/-- A direct polynomial tail envelope of order two cancels one power of the
fallback growth. -/
theorem four_sampleSize_mul_probability_le_inverse
    (n : ℕ) (probability tailConstant : ℝ≥0∞)
    (htail : probability ≤
      tailConstant *
        ((mixedBuresNaturalSampleSize n : ℝ≥0∞)⁻¹) ^ 2) :
    (4 : ℝ≥0∞) * mixedBuresNaturalSampleSize n * probability ≤
      4 * tailConstant *
        (mixedBuresNaturalSampleSize n : ℝ≥0∞)⁻¹ := by
  let N : ℝ≥0∞ := mixedBuresNaturalSampleSize n
  have hNzero : N ≠ 0 := by
    simp [N, mixedBuresNaturalSampleSize]
  have hNtop : N ≠ ⊤ := by simp [N]
  calc
    (4 : ℝ≥0∞) * mixedBuresNaturalSampleSize n * probability ≤
        4 * N * (tailConstant * N⁻¹ ^ 2) := by
      gcongr
    _ = 4 * tailConstant * (N * N⁻¹ ^ 2) := by ac_rfl
    _ = 4 * tailConstant * N⁻¹ := by
      rw [ennreal_mul_inv_sq_eq_inv hNzero hNtop]
    _ = 4 * tailConstant *
        (mixedBuresNaturalSampleSize n : ℝ≥0∞)⁻¹ := rfl

/-- The inverse natural sample size tends to zero. -/
theorem mixedBuresNaturalSampleSize_inv_tendsto_zero :
    Tendsto
      (fun n => (mixedBuresNaturalSampleSize n : ℝ≥0∞)⁻¹)
      atTop (nhds 0) := by
  have hshift : Tendsto mixedBuresNaturalSampleSize atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    exact hn.trans (Nat.le_add_right n 1)
  simpa [Function.comp_def] using
    ENNReal.tendsto_inv_nat_nhds_zero.comp hshift

/-- The common `4 C / (n+1)` bad-event envelope vanishes. -/
theorem mixedBuresBadEventRate_tendsto_zero
    {tailConstant : ℝ≥0∞} (hfinite : tailConstant ≠ ⊤) :
    Tendsto
      (fun n => 4 * tailConstant *
        (mixedBuresNaturalSampleSize n : ℝ≥0∞)⁻¹)
      atTop (nhds 0) := by
  have hconstant : (4 : ℝ≥0∞) * tailConstant ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by norm_num) hfinite
  simpa [Function.comp_def, mul_assoc] using
    ((ENNReal.continuousAt_const_mul
      (a := (4 : ℝ≥0∞) * tailConstant) (b := 0)
      (Or.inl hconstant)).tendsto.comp
        mixedBuresNaturalSampleSize_inv_tendsto_zero)

/-- Good-event physical risk. -/
def mixedBuresGoodPhysicalRisk
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (good : Set Ω) (n : ℕ)
    (theta : MixedQubitVector) (error : Ω → MixedQubitVector) : ℝ≥0∞ :=
  ∫⁻ omega,
    mixedLossOnEvent good
      (fun omega => mixedBuresNaturalPhysicalLoss n theta (error omega))
      omega ∂mu

/-- Good-event quadratic comparator. -/
def mixedBuresGoodQuadraticRisk
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (good : Set Ω)
    (theta : MixedQubitVector) (error : Ω → MixedQubitVector) : ℝ≥0∞ :=
  ∫⁻ omega,
    mixedLossOnEvent good
      (fun omega => mixedBuresQuadraticLoss theta (error omega))
      omega ∂mu

/-- Bad-event physical Bures contribution of the fallback state. -/
def mixedBuresBadPhysicalRisk
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (bad : Set Ω) (n : ℕ)
    (fallback : Ω → MixedQubitVector) (truth : MixedQubitVector) : ℝ≥0∞ :=
  ∫⁻ omega,
    mixedLossOnEvent bad
      (mixedFallbackBuresPhysicalLoss n fallback truth) omega ∂mu

/-- Existing normalized squared-Bloch fallback contribution, used as the
bad-event quadratic comparator. -/
def mixedBuresBadFallbackComparator
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (bad : Set Ω) (n : ℕ)
    (fallback : Ω → MixedQubitVector) (truth : MixedQubitVector) : ℝ≥0∞ :=
  eventLIntegral mu bad
    (mixedPhysicalFallbackEvenMomentLoss
      (mixedBuresNaturalSampleSize n) 1 fallback truth)

def mixedBuresFullPhysicalRisk
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (good : Set Ω) (n : ℕ)
    (theta : MixedQubitVector) (error fallback : Ω → MixedQubitVector) : ℝ≥0∞ :=
  mixedBuresGoodPhysicalRisk mu good n theta error +
    mixedBuresBadPhysicalRisk mu goodᶜ n fallback theta

def mixedBuresFullQuadraticComparator
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (good : Set Ω) (n : ℕ)
    (theta : MixedQubitVector) (error fallback : Ω → MixedQubitVector) : ℝ≥0∞ :=
  mixedBuresGoodQuadraticRisk mu good theta error +
    mixedBuresBadFallbackComparator mu goodᶜ n fallback theta

def mixedBuresGoodMomentError
    (margin : ℝ) (C3 C4 : ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  mixedBuresCubicRate margin n * C3 +
    mixedBuresQuarticRate margin n * C4

def mixedBuresBadTailError
    (tailConstant : ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  4 * tailConstant *
    (mixedBuresNaturalSampleSize n : ℝ≥0∞)⁻¹

def mixedBuresTotalRiskTransferError
    (margin : ℝ) (C3 C4 tailConstant : ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  mixedBuresGoodMomentError margin C3 C4 n +
    mixedBuresBadTailError tailConstant n

/-- Finite-sample full good/bad reduction. The physical bad branch is actual
Bures loss. The comparator bad branch is the already-verified normalized
squared-Bloch fallback loss; both branches vanish under the same quadratic
bad-event probability envelope. -/
theorem mixedBuresFullRiskReduction_at
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (good : Set Ω)
    (n : ℕ) (margin : ℝ) (theta : MixedQubitVector)
    (error fallback : Ω → MixedQubitVector) (radius : Ω → ℝ)
    (C3 C4 tailConstant : ℝ≥0∞)
    (hmargin : 0 < margin)
    (hinterior : MixedQubitInteriorWithMargin margin theta)
    (hgood : MeasurableSet good)
    (hradiusNonnegative : ∀ omega ∈ good, 0 ≤ radius omega)
    (hradiusDominates :
      ∀ omega ∈ good, blochNormSq (error omega) ≤ radius omega ^ 2)
    (hlocal : ∀ omega ∈ good,
      2 * radius omega /
            Real.sqrt (mixedBuresNaturalSampleSizeReal n) +
          radius omega ^ 2 / mixedBuresNaturalSampleSizeReal n ≤ margin / 2)
    (hphysicalMeasurable : Measurable
      (mixedLossOnEvent good
        (fun omega => mixedBuresNaturalPhysicalLoss n theta (error omega))))
    (hquadraticMeasurable : Measurable
      (mixedLossOnEvent good
        (fun omega => mixedBuresQuadraticLoss theta (error omega))))
    (hthirdMeasurable : Measurable
      (mixedLossOnEvent good
        (fun omega => mixedBuresThirdRadiusMoment (radius omega))))
    (hfourthMeasurable : Measurable
      (mixedLossOnEvent good
        (fun omega => mixedBuresFourthRadiusMoment (radius omega))))
    (hthirdMoment :
      (∫⁻ omega,
        mixedLossOnEvent good
          (fun omega => mixedBuresThirdRadiusMoment (radius omega)) omega ∂mu) ≤ C3)
    (hfourthMoment :
      (∫⁻ omega,
        mixedLossOnEvent good
          (fun omega => mixedBuresFourthRadiusMoment (radius omega)) omega ∂mu) ≤ C4)
    (hfallback : ∀ omega ∈ goodᶜ, blochNormSq (fallback omega) ≤ 1)
    (htruth : blochNormSq theta ≤ 1)
    (hbadProbability : mu goodᶜ ≤
      tailConstant *
        ((mixedBuresNaturalSampleSize n : ℝ≥0∞)⁻¹) ^ 2) :
    mixedBuresFullPhysicalRisk mu good n theta error fallback ≤
        mixedBuresFullQuadraticComparator mu good n theta error fallback +
          mixedBuresTotalRiskTransferError margin C3 C4 tailConstant n ∧
      mixedBuresFullQuadraticComparator mu good n theta error fallback ≤
        mixedBuresFullPhysicalRisk mu good n theta error fallback +
          mixedBuresTotalRiskTransferError margin C3 C4 tailConstant n := by
  have hgoodRisk :=
    mixedBuresGoodEventExpectedRisk_twoSided
      mu good n margin theta error radius C3 C4
      hmargin hinterior hradiusNonnegative hradiusDominates hlocal
      hphysicalMeasurable hquadraticMeasurable
      hthirdMeasurable hfourthMeasurable hthirdMoment hfourthMoment
  have hphysicalBad0 :
      mixedBuresBadPhysicalRisk mu goodᶜ n fallback theta ≤
        ((2 : ℝ≥0∞) * mixedBuresNaturalSampleSize n) * mu goodᶜ := by
    exact mixedFallbackBuresBadEventLIntegral_le
      mu goodᶜ hgood.compl n fallback theta
  have hphysicalBad1 :
      mixedBuresBadPhysicalRisk mu goodᶜ n fallback theta ≤
        (4 : ℝ≥0∞) * mixedBuresNaturalSampleSize n * mu goodᶜ := by
    refine hphysicalBad0.trans ?_
    gcongr
    norm_num
  have hfallbackBad0 :
      mixedBuresBadFallbackComparator mu goodᶜ n fallback theta ≤
        ((4 : ℝ≥0∞) * mixedBuresNaturalSampleSize n) ^ 1 * mu goodᶜ := by
    exact mixedPhysicalFallbackBadEventLIntegral_le
      mu goodᶜ hgood.compl (mixedBuresNaturalSampleSize n) 1
      fallback theta hfallback htruth
  have hfallbackBad1 :
      mixedBuresBadFallbackComparator mu goodᶜ n fallback theta ≤
        (4 : ℝ≥0∞) * mixedBuresNaturalSampleSize n * mu goodᶜ := by
    simpa [pow_one, mul_assoc] using hfallbackBad0
  have htail := four_sampleSize_mul_probability_le_inverse
    n (mu goodᶜ) tailConstant hbadProbability
  have hphysicalBad :
      mixedBuresBadPhysicalRisk mu goodᶜ n fallback theta ≤
        mixedBuresBadTailError tailConstant n :=
    hphysicalBad1.trans (by simpa [mixedBuresBadTailError] using htail)
  have hfallbackBad :
      mixedBuresBadFallbackComparator mu goodᶜ n fallback theta ≤
        mixedBuresBadTailError tailConstant n :=
    hfallbackBad1.trans (by simpa [mixedBuresBadTailError] using htail)
  let GP := mixedBuresGoodPhysicalRisk mu good n theta error
  let GQ := mixedBuresGoodQuadraticRisk mu good theta error
  let BP := mixedBuresBadPhysicalRisk mu goodᶜ n fallback theta
  let BQ := mixedBuresBadFallbackComparator mu goodᶜ n fallback theta
  let EG := mixedBuresGoodMomentError margin C3 C4 n
  let EB := mixedBuresBadTailError tailConstant n
  have hGP : GP ≤ GQ + EG := by
    simpa [GP, GQ, EG, mixedBuresGoodMomentError,
      mixedBuresGoodPhysicalRisk, mixedBuresGoodQuadraticRisk,
      add_assoc] using hgoodRisk.1
  have hGQ : GQ ≤ GP + EG := by
    simpa [GP, GQ, EG, mixedBuresGoodMomentError,
      mixedBuresGoodPhysicalRisk, mixedBuresGoodQuadraticRisk,
      add_assoc] using hgoodRisk.2
  have hBP : BP ≤ EB := by simpa [BP, EB] using hphysicalBad
  have hBQ : BQ ≤ EB := by simpa [BQ, EB] using hfallbackBad
  constructor
  · change GP + BP ≤ GQ + BQ + (EG + EB)
    calc
      GP + BP ≤ (GQ + EG) + EB := add_le_add hGP hBP
      _ = GQ + (EG + EB) := by ac_rfl
      _ ≤ (GQ + BQ) + (EG + EB) := by
        exact add_le_add_left (self_le_add_right GQ BQ) (EG + EB)
  · change GQ + BQ ≤ GP + BP + (EG + EB)
    calc
      GQ + BQ ≤ (GP + EG) + EB := add_le_add hGQ hBQ
      _ = GP + (EG + EB) := by ac_rfl
      _ ≤ (GP + BP) + (EG + EB) := by
        exact add_le_add_left (self_le_add_right GP BP) (EG + EB)

/-- The complete deterministic error envelope tends to zero for uniformly
bounded third/fourth moments and a quadratic bad-event tail. -/
theorem mixedBuresTotalRiskTransferError_tendsto_zero
    {margin : ℝ} {C3 C4 tailConstant : ℝ≥0∞}
    (hmargin : 0 < margin)
    (hC3 : C3 ≠ ⊤) (hC4 : C4 ≠ ⊤)
    (hTail : tailConstant ≠ ⊤) :
    Tendsto
      (mixedBuresTotalRiskTransferError margin C3 C4 tailConstant)
      atTop (nhds 0) := by
  have hcubic := mixedBuresCubicRate_tendsto_zero hmargin
  have hquartic := mixedBuresQuarticRate_tendsto_zero hmargin
  have hcubicMoment : Tendsto
      (fun n => mixedBuresCubicRate margin n * C3)
      atTop (nhds 0) := by
    simpa [Function.comp_def, mul_comm] using
      ((ENNReal.continuousAt_const_mul
        (a := C3) (b := 0) (Or.inl hC3)).tendsto.comp hcubic)
  have hquarticMoment : Tendsto
      (fun n => mixedBuresQuarticRate margin n * C4)
      atTop (nhds 0) := by
    simpa [Function.comp_def, mul_comm] using
      ((ENNReal.continuousAt_const_mul
        (a := C4) (b := 0) (Or.inl hC4)).tendsto.comp hquartic)
  have hgood : Tendsto
      (mixedBuresGoodMomentError margin C3 C4)
      atTop (nhds 0) := by
    change Tendsto
      (fun n => mixedBuresCubicRate margin n * C3 +
        mixedBuresQuarticRate margin n * C4) atTop (nhds 0)
    simpa only [add_zero] using hcubicMoment.add hquarticMoment
  have hbad : Tendsto
      (mixedBuresBadTailError tailConstant)
      atTop (nhds 0) := by
    change Tendsto
      (fun n => 4 * tailConstant *
        (mixedBuresNaturalSampleSize n : ℝ≥0∞)⁻¹) atTop (nhds 0)
    exact mixedBuresBadEventRate_tendsto_zero hTail
  change Tendsto
    (fun n => mixedBuresGoodMomentError margin C3 C4 n +
      mixedBuresBadTailError tailConstant n) atTop (nhds 0)
  simpa only [add_zero] using hgood.add hbad

/-- Quantitative asymptotic equivalence is the exact noncircular endpoint needed
before inserting the LAN/quadratic-risk limit. -/
def MixedBuresRiskAsymptoticEquivalence
    (physicalRisk quadraticRisk : ℕ → ℝ≥0∞) : Prop :=
  ∃ errorBound : ℕ → ℝ≥0∞,
    Tendsto errorBound atTop (nhds 0) ∧
      ∀ n,
        physicalRisk n ≤ quadraticRisk n + errorBound n ∧
          quadraticRisk n ≤ physicalRisk n + errorBound n

/-- Full mixed one-qubit physical Bures/fidelity-risk reduction. It assumes no
physical-risk conclusion: all premises are interior geometry, measurability,
uniform third/fourth moments, physical fallback bounds, and an explicit
quadratic bad-event probability envelope. -/
theorem mixedBuresFidelityRiskConvergenceReduction
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : ℕ → Measure Ω) (good : ℕ → Set Ω)
    (margin : ℝ) (theta : MixedQubitVector)
    (error fallback : ℕ → Ω → MixedQubitVector)
    (radius : ℕ → Ω → ℝ)
    (C3 C4 tailConstant : ℝ≥0∞)
    (hmargin : 0 < margin)
    (hinterior : MixedQubitInteriorWithMargin margin theta)
    (hC3 : C3 ≠ ⊤) (hC4 : C4 ≠ ⊤)
    (hTail : tailConstant ≠ ⊤)
    (hgood : ∀ n, MeasurableSet (good n))
    (hradiusNonnegative :
      ∀ n omega, omega ∈ good n → 0 ≤ radius n omega)
    (hradiusDominates :
      ∀ n omega, omega ∈ good n →
        blochNormSq (error n omega) ≤ radius n omega ^ 2)
    (hlocal : ∀ n omega, omega ∈ good n →
      2 * radius n omega /
            Real.sqrt (mixedBuresNaturalSampleSizeReal n) +
          radius n omega ^ 2 / mixedBuresNaturalSampleSizeReal n ≤ margin / 2)
    (hphysicalMeasurable : ∀ n, Measurable
      (mixedLossOnEvent (good n)
        (fun omega => mixedBuresNaturalPhysicalLoss n theta (error n omega))))
    (hquadraticMeasurable : ∀ n, Measurable
      (mixedLossOnEvent (good n)
        (fun omega => mixedBuresQuadraticLoss theta (error n omega))))
    (hthirdMeasurable : ∀ n, Measurable
      (mixedLossOnEvent (good n)
        (fun omega => mixedBuresThirdRadiusMoment (radius n omega))))
    (hfourthMeasurable : ∀ n, Measurable
      (mixedLossOnEvent (good n)
        (fun omega => mixedBuresFourthRadiusMoment (radius n omega))))
    (hthirdMoment : ∀ n,
      (∫⁻ omega,
        mixedLossOnEvent (good n)
          (fun omega => mixedBuresThirdRadiusMoment (radius n omega)) omega
          ∂(mu n)) ≤ C3)
    (hfourthMoment : ∀ n,
      (∫⁻ omega,
        mixedLossOnEvent (good n)
          (fun omega => mixedBuresFourthRadiusMoment (radius n omega)) omega
          ∂(mu n)) ≤ C4)
    (hfallback : ∀ n omega, omega ∈ (good n)ᶜ →
      blochNormSq (fallback n omega) ≤ 1)
    (htruth : blochNormSq theta ≤ 1)
    (hbadProbability : ∀ n,
      mu n (good n)ᶜ ≤ tailConstant *
        ((mixedBuresNaturalSampleSize n : ℝ≥0∞)⁻¹) ^ 2) :
    MixedBuresRiskAsymptoticEquivalence
      (fun n =>
        mixedBuresFullPhysicalRisk
          (mu n) (good n) n theta (error n) (fallback n))
      (fun n =>
        mixedBuresFullQuadraticComparator
          (mu n) (good n) n theta (error n) (fallback n)) := by
  refine ⟨mixedBuresTotalRiskTransferError margin C3 C4 tailConstant,
    mixedBuresTotalRiskTransferError_tendsto_zero
      hmargin hC3 hC4 hTail, ?_⟩
  intro n
  exact mixedBuresFullRiskReduction_at
    (mu n) (good n) n margin theta (error n) (fallback n) (radius n)
    C3 C4 tailConstant hmargin hinterior (hgood n)
    (fun omega homega => hradiusNonnegative n omega homega)
    (fun omega homega => hradiusDominates n omega homega)
    (fun omega homega => hlocal n omega homega)
    (hphysicalMeasurable n) (hquadraticMeasurable n)
    (hthirdMeasurable n) (hfourthMeasurable n)
    (hthirdMoment n) (hfourthMoment n)
    (fun omega homega => hfallback n omega homega)
    htruth (hbadProbability n)

end

end QubitOracle.Paper
