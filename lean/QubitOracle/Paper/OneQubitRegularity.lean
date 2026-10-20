import QubitOracle.Paper.QubitRLSCore
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# One-qubit mixed and pure regularity

This module deliberately treats only a single qubit.  The mixed branch is the
open Bloch ball and the pure branch is its unit sphere.  No theorem about
general rank-one states, moving `U(d)` frames, or `d > 2` is used.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory
open scoped BigOperators

noncomputable section

/-- Three-dimensional Cauchy--Schwarz, proved by the sum-of-squares identity
for the three pairwise minors. -/
theorem blochDot_sq_le_normSq_mul_normSq
    (x z : Fin 3 -> Real) :
    blochDot x z ^ 2 <= blochNormSq x * blochNormSq z := by
  simp [blochDot, blochNormSq, Fin.sum_univ_succ]
  nlinarith
    [sq_nonneg (x 0 * z 1 - x 1 * z 0),
      sq_nonneg (x 0 * z 2 - x 2 * z 0),
      sq_nonneg (x 1 * z 2 - x 2 * z 1)]

/-- Every projective outcome at an interior mixed-qubit truth has a uniform
probability floor determined by its distance from the Bloch-sphere boundary. -/
theorem mixedQubitBornProbability_floor
    (theta axis : Fin 3 -> Real) (margin : Real)
    (hmargin0 : 0 < margin) (hmargin1 : margin <= 1)
    (haxis : blochNormSq axis = 1)
    (htheta : blochNormSq theta <= (1 - margin) ^ 2)
    (y : QubitRLSOutcome) :
    margin / 2 <= qubitRLSBornProbability theta axis y := by
  have hsq0 := blochDot_sq_le_normSq_mul_normSq axis theta
  have hsq : blochDot axis theta ^ 2 <= (1 - margin) ^ 2 := by
    calc
      blochDot axis theta ^ 2 <=
          blochNormSq axis * blochNormSq theta := hsq0
      _ = blochNormSq theta := by rw [haxis, one_mul]
      _ <= (1 - margin) ^ 2 := htheta
  have hnonnegative : 0 <= 1 - margin := by linarith
  have hlower : -(1 - margin) <= blochDot axis theta := by
    nlinarith [sq_nonneg (blochDot axis theta + (1 - margin))]
  have hupper : blochDot axis theta <= 1 - margin := by
    nlinarith [sq_nonneg (blochDot axis theta - (1 - margin))]
  cases y <;>
    simp [qubitRLSBornProbability, qubitRLSOutcomeSign,
      qubitBornTrace_eq] <;>
    linarith

/-- Core pure-qubit regularity estimate.  A tangent measurement axis is
orthogonal to the controller.  Its overlap with the truth is therefore at
most the controller error, and both binary probabilities are at least `1/4`
once the squared Bloch error is at most `1/4`. -/
theorem pureQubitTangentBornProbability_floor
    (truth controller axis : Fin 3 -> Real)
    (haxis : blochNormSq axis = 1)
    (htangent : blochDot axis controller = 0)
    (hclose :
      blochNormSq (fun j => truth j - controller j) <= (1 / 4 : Real))
    (y : QubitRLSOutcome) :
    (1 / 4 : Real) <= qubitRLSBornProbability truth axis y := by
  have hdotSub :
      blochDot axis (fun j => truth j - controller j) =
        blochDot axis truth - blochDot axis controller := by
    simp [blochDot, mul_sub, Finset.sum_sub_distrib]
  have hdotEq :
      blochDot axis (fun j => truth j - controller j) =
        blochDot axis truth := by
    rw [hdotSub, htangent, sub_zero]
  have hcauchy := blochDot_sq_le_normSq_mul_normSq axis
    (fun j => truth j - controller j)
  have hsq : blochDot axis truth ^ 2 <= (1 / 4 : Real) := by
    rw [← hdotEq]
    calc
      blochDot axis (fun j => truth j - controller j) ^ 2 <=
          blochNormSq axis *
            blochNormSq (fun j => truth j - controller j) := hcauchy
      _ = blochNormSq (fun j => truth j - controller j) := by
        rw [haxis, one_mul]
      _ <= (1 / 4 : Real) := hclose
  have hlower : (-1 / 2 : Real) <= blochDot axis truth := by
    nlinarith [sq_nonneg (blochDot axis truth + (1 / 2 : Real))]
  have hupper : blochDot axis truth <= (1 / 2 : Real) := by
    nlinarith [sq_nonneg (blochDot axis truth - (1 / 2 : Real))]
  cases y <;>
    simp [qubitRLSBornProbability, qubitRLSOutcomeSign,
      qubitBornTrace_eq] <;>
    linarith

/-- Probability-margin meaning of a regular pure-qubit exploitation round. -/
def PureQubitRoundRegular
    (truth axis : Fin 3 -> Real) : Prop :=
  forall y : QubitRLSOutcome,
    (1 / 4 : Real) <= qubitRLSBornProbability truth axis y

/-- RLS eventual closeness and tangent-axis construction imply eventual
pure-qubit regularity. -/
theorem pureQubit_eventually_regular_of_close
    (truth : Fin 3 -> Real)
    (controller axis : Nat -> Fin 3 -> Real)
    (haxis : forall n, blochNormSq (axis n) = 1)
    (htangent : forall n, blochDot (axis n) (controller n) = 0)
    (hclose : ∀ᶠ n in atTop,
      blochNormSq (fun j => truth j - controller n j) <= (1 / 4 : Real)) :
    ∀ᶠ n in atTop, PureQubitRoundRegular truth (axis n) := by
  filter_upwards [hclose] with n hn
  intro y
  exact pureQubitTangentBornProbability_floor
    truth (controller n) (axis n) (haxis n) (htangent n) hn y

/-- Indicator of a probability-floor failure in a pure-qubit exploitation
round. -/
noncomputable def pureQubitExceptionalIndicator
    (truth axis : Fin 3 -> Real) : Real :=
  by
    classical
    exact if PureQubitRoundRegular truth axis then 0 else 1

theorem pureQubitExceptionalIndicator_bounds
    (truth axis : Fin 3 -> Real) :
    0 <= pureQubitExceptionalIndicator truth axis ∧
      pureQubitExceptionalIndicator truth axis <= 1 := by
  classical
  by_cases h : PureQubitRoundRegular truth axis <;>
    simp [pureQubitExceptionalIndicator, h]

/-- The exceptional indicator is eventually zero once the controller is
eventually close and every exploitation axis is tangent to it. -/
theorem pureQubitExceptionalIndicator_eventually_zero
    (truth : Fin 3 -> Real)
    (controller axis : Nat -> Fin 3 -> Real)
    (haxis : forall n, blochNormSq (axis n) = 1)
    (htangent : forall n, blochDot (axis n) (controller n) = 0)
    (hclose : ∀ᶠ n in atTop,
      blochNormSq (fun j => truth j - controller n j) <= (1 / 4 : Real)) :
    ∀ᶠ n in atTop,
      pureQubitExceptionalIndicator truth (axis n) = 0 := by
  have hregular := pureQubit_eventually_regular_of_close
    truth controller axis haxis htangent hclose
  filter_upwards [hregular] with n hn
  simp [pureQubitExceptionalIndicator, hn]

/-- Any eventually zero real sequence has a Cesaro average tending to zero. -/
theorem exceptionalFrequency_tendsto_zero_of_eventually_zero
    (exception : Nat -> Real)
    (hzero : ∀ᶠ n in atTop, exception n = 0) :
    Tendsto
      (fun n : Nat =>
        (n : Real)⁻¹ * ∑ i ∈ Finset.range n, exception i)
      atTop (nhds 0) := by
  have hpoint : Tendsto exception atTop (nhds 0) :=
    tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hzero)
  exact hpoint.cesaro

/-- Realized exceptional-round frequency along one adaptive path. -/
def pureQubitExceptionalFrequency
    {Omega : Type*} (truth : Fin 3 -> Real)
    (axis : Nat -> Omega -> Fin 3 -> Real)
    (n : Nat) (omega : Omega) : Real :=
  (n : Real)⁻¹ *
    ∑ i ∈ Finset.range n,
      pureQubitExceptionalIndicator truth (axis i omega)

/-- The realized exceptional frequency always lies in `[0,1]`. -/
theorem pureQubitExceptionalFrequency_bounds
    {Omega : Type*} (truth : Fin 3 -> Real)
    (axis : Nat -> Omega -> Fin 3 -> Real)
    (n : Nat) (omega : Omega) :
    0 <= pureQubitExceptionalFrequency truth axis n omega ∧
      pureQubitExceptionalFrequency truth axis n omega <= 1 := by
  classical
  unfold pureQubitExceptionalFrequency
  have hsum0 : 0 <= ∑ i ∈ Finset.range n,
      pureQubitExceptionalIndicator truth (axis i omega) :=
    Finset.sum_nonneg fun i hi =>
      (pureQubitExceptionalIndicator_bounds truth (axis i omega)).1
  have hsum1 :
      (∑ i ∈ Finset.range n,
        pureQubitExceptionalIndicator truth (axis i omega)) <= (n : Real) := by
    calc
      (∑ i ∈ Finset.range n,
          pureQubitExceptionalIndicator truth (axis i omega)) <=
          ∑ _i ∈ Finset.range n, (1 : Real) := by
            apply Finset.sum_le_sum
            intro i hi
            exact (pureQubitExceptionalIndicator_bounds
              truth (axis i omega)).2
      _ = (n : Real) := by simp
  by_cases hn : n = 0
  · subst n
    simp
  · have hnpos : (0 : Real) < (n : Real) := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    have hinv : 0 <= (n : Real)⁻¹ := inv_nonneg.mpr hnpos.le
    constructor
    · exact mul_nonneg hinv hsum0
    · calc
        (n : Real)⁻¹ *
            (∑ i ∈ Finset.range n,
              pureQubitExceptionalIndicator truth (axis i omega)) <=
            (n : Real)⁻¹ * (n : Real) :=
          mul_le_mul_of_nonneg_left hsum1 hinv
        _ = 1 := inv_mul_cancel₀ hnpos.ne'

/-- Almost-sure qubit regularity gives almost-sure zero exceptional-round
frequency. -/
theorem pureQubit_exceptionFrequency_ae
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (truth : Fin 3 -> Real)
    (controller axis : Nat -> Omega -> Fin 3 -> Real)
    (haxis : forall n omega, blochNormSq (axis n omega) = 1)
    (htangent : forall n omega,
      blochDot (axis n omega) (controller n omega) = 0)
    (hclose : ∀ᵐ omega ∂mu, ∀ᶠ n in atTop,
      blochNormSq (fun j => truth j - controller n omega j) <=
        (1 / 4 : Real)) :
    ∀ᵐ omega ∂mu,
      Tendsto
        (fun n => pureQubitExceptionalFrequency truth axis n omega)
        atTop (nhds 0) := by
  filter_upwards [hclose] with omega hcloseOmega
  have hzero := pureQubitExceptionalIndicator_eventually_zero
    truth (fun n => controller n omega) (fun n => axis n omega)
    (fun n => haxis n omega) (fun n => htangent n omega) hcloseOmega
  simpa [pureQubitExceptionalFrequency] using
    exceptionalFrequency_tendsto_zero_of_eventually_zero
      (fun n => pureQubitExceptionalIndicator truth (axis n omega)) hzero

namespace Label

/-- One-qubit replacement for the probability-margin part of
`lem:SI_r1_regularity`. -/
theorem lem_SI_r1_probability_regularity_qubit
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (truth : Fin 3 -> Real)
    (controller axis : Nat -> Omega -> Fin 3 -> Real)
    (haxis : forall n omega, blochNormSq (axis n omega) = 1)
    (htangent : forall n omega,
      blochDot (axis n omega) (controller n omega) = 0)
    (hclose : ∀ᵐ omega ∂mu, ∀ᶠ n in atTop,
      blochNormSq (fun j => truth j - controller n omega j) <=
        (1 / 4 : Real)) :
    ∀ᵐ omega ∂mu, ∀ᶠ n in atTop,
      PureQubitRoundRegular truth (axis n omega) := by
  filter_upwards [hclose] with omega hcloseOmega
  exact pureQubit_eventually_regular_of_close
    truth (fun n => controller n omega) (fun n => axis n omega)
    (fun n => haxis n omega) (fun n => htangent n omega) hcloseOmega

/-- Qubit specialization of `eq:SI_protocol_exception_as`. -/
theorem eq_SI_protocol_exception_as
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (truth : Fin 3 -> Real)
    (controller axis : Nat -> Omega -> Fin 3 -> Real)
    (haxis : forall n omega, blochNormSq (axis n omega) = 1)
    (htangent : forall n omega,
      blochDot (axis n omega) (controller n omega) = 0)
    (hclose : ∀ᵐ omega ∂mu, ∀ᶠ n in atTop,
      blochNormSq (fun j => truth j - controller n omega j) <=
        (1 / 4 : Real)) :
    ∀ᵐ omega ∂mu,
      Tendsto
        (fun n => pureQubitExceptionalFrequency truth axis n omega)
        atTop (nhds 0) :=
  pureQubit_exceptionFrequency_ae
    mu truth controller axis haxis htangent hclose

/-- Qubit specialization of `eq:SI_protocol_exception_mean_verified`.
Measurability is stated explicitly; boundedness is proved above. -/
theorem eq_SI_protocol_exception_mean_verified
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (truth : Fin 3 -> Real)
    (controller axis : Nat -> Omega -> Fin 3 -> Real)
    (haxis : forall n omega, blochNormSq (axis n omega) = 1)
    (htangent : forall n omega,
      blochDot (axis n omega) (controller n omega) = 0)
    (hclose : ∀ᵐ omega ∂mu, ∀ᶠ n in atTop,
      blochNormSq (fun j => truth j - controller n omega j) <=
        (1 / 4 : Real))
    (hmeasurable : forall n, AEStronglyMeasurable
      (pureQubitExceptionalFrequency truth axis n) mu) :
    Tendsto
      (fun n => ∫ omega,
        pureQubitExceptionalFrequency truth axis n omega ∂mu)
      atTop (nhds 0) := by
  have hae := pureQubit_exceptionFrequency_ae
    mu truth controller axis haxis htangent hclose
  have hbound : forall n, ∀ᵐ omega ∂mu,
      ‖pureQubitExceptionalFrequency truth axis n omega‖ <=
        (fun _ : Omega => (1 : Real)) omega := by
    intro n
    exact Filter.Eventually.of_forall fun omega => by
      have hb := pureQubitExceptionalFrequency_bounds
        truth axis n omega
      rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
      exact hb.2
  have hDCT := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := mu) (fun _ : Omega => (1 : Real))
    hmeasurable (integrable_const 1) hbound hae
  simpa using hDCT

end Label

end

end QubitOracle.Paper
