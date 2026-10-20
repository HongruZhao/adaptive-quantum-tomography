import QubitOracle.Paper.OneQubitRegularity
import QubitOracle.Paper.OneQubitPureCoordinateCore

/-!
# Directional likelihood regularity for one pure qubit

This is a clean, self-contained reimplementation of the canonical
north-pole calculation.  It does not import the quarantined likelihood files.

The result is deliberately directional.  For each fixed `h : Fin 2 → Real`
it studies the one-dimensional path

`t ↦ northPoleStereographicChart (t • h)`.

This is the scope needed by the scalar Taylor expansion along each fixed LAN
line `h / sqrt n`.  The module does not claim a uniform multivariate
Frechet-derivative theorem or transport between arbitrary moving charts.

Under

* `h 0 ^ 2 + h 1 ^ 2 ≤ 1`,
* `|t| ≤ 1`, and
* `t ^ 2 * (h 0 ^ 2 + h 1 ^ 2) ≤ 1 / 15`,

the binary Born probability is at least `1 / 4`, and the absolute first,
second, and third directional log-likelihood derivatives are bounded by
`10`, `80`, and `1200`, respectively.
-/

namespace QubitOracle.Paper

open Finset
open scoped BigOperators

noncomputable section

/-! ## Scalar logarithmic differentiation -/

def directionalScalarLog (p : Real → Real) : Real → Real :=
  fun t => Real.log (p t)

def directionalScalarScore
    (p dp : Real → Real) : Real → Real :=
  fun t => dp t / p t

def directionalScalarCurvature
    (p dp ddp : Real → Real) : Real → Real :=
  fun t => ddp t / p t - (dp t / p t) ^ 2

def directionalScalarThird
    (p dp ddp dddp : Real → Real) : Real → Real :=
  fun t =>
    dddp t / p t -
      3 * (dp t / p t) * (ddp t / p t) +
      2 * (dp t / p t) ^ 3

theorem hasDerivAt_directionalScalarLog
    (p dp : Real → Real) (t : Real)
    (hp : HasDerivAt p (dp t) t) (hPositive : 0 < p t) :
    HasDerivAt (directionalScalarLog p)
      (directionalScalarScore p dp t) t := by
  unfold directionalScalarLog directionalScalarScore
  exact hp.log hPositive.ne'

theorem hasDerivAt_directionalScalarScore
    (p dp ddp : Real → Real) (t : Real)
    (hp : HasDerivAt p (dp t) t)
    (hdp : HasDerivAt dp (ddp t) t)
    (hPositive : 0 < p t) :
    HasDerivAt (directionalScalarScore p dp)
      (directionalScalarCurvature p dp ddp t) t := by
  unfold directionalScalarScore directionalScalarCurvature
  convert hdp.div hp hPositive.ne' using 1
  all_goals first | rfl | (field_simp [hPositive.ne'] <;> ring)

theorem hasDerivAt_directionalScalarCurvature
    (p dp ddp dddp : Real → Real) (t : Real)
    (hp : HasDerivAt p (dp t) t)
    (hdp : HasDerivAt dp (ddp t) t)
    (hddp : HasDerivAt ddp (dddp t) t)
    (hPositive : 0 < p t) :
    HasDerivAt (directionalScalarCurvature p dp ddp)
      (directionalScalarThird p dp ddp dddp t) t := by
  unfold directionalScalarCurvature directionalScalarThird
  have hScore := hdp.div hp hPositive.ne'
  have hQuotient := hddp.div hp hPositive.ne'
  convert hQuotient.sub (hScore.pow 2) using 1
  all_goals first | rfl |
    (simp only [Pi.div_apply]
     field_simp [hPositive.ne']
     norm_num
     field_simp [hPositive.ne']
     ring)

theorem abs_div_le_directionalFloor
    (floor numeratorBound p q : Real)
    (hFloor : 0 < floor) (hp : floor ≤ p)
    (hBoundNonnegative : 0 ≤ numeratorBound)
    (hq : |q| ≤ numeratorBound) :
    |q / p| ≤ numeratorBound / floor := by
  have hpPositive : 0 < p := hFloor.trans_le hp
  rw [abs_div, abs_of_pos hpPositive]
  apply (div_le_iff₀ hpPositive).2
  calc
    |q| ≤ numeratorBound := hq
    _ = (numeratorBound / floor) * floor := by
      field_simp [hFloor.ne']
    _ ≤ (numeratorBound / floor) * p := by
      exact mul_le_mul_of_nonneg_left hp
        (div_nonneg hBoundNonnegative hFloor.le)

/-! ## The one-dimensional path `t ↦ chart (t • h)` -/

def directionalLineDenominator
    (h : Fin 2 → Real) (t : Real) : Real :=
  1 + t ^ 2 * directionalQubitNormSq h

theorem directionalLineDenominator_eq_chart
    (h : Fin 2 → Real) (t : Real) :
    directionalLineDenominator h t =
      directionalStereographicDenominator (t • h) := by
  simp [directionalLineDenominator,
    directionalStereographicDenominator,
    directionalQubitNormSq_smul]

theorem one_le_directionalLineDenominator
    (h : Fin 2 → Real) (t : Real) :
    1 ≤ directionalLineDenominator h t := by
  unfold directionalLineDenominator
  have hNonnegative :
      0 ≤ t ^ 2 * directionalQubitNormSq h :=
    mul_nonneg (sq_nonneg t) (directionalQubitNormSq_nonnegative h)
  linarith

theorem directionalLineDenominator_pos
    (h : Fin 2 → Real) (t : Real) :
    0 < directionalLineDenominator h t :=
  lt_of_lt_of_le zero_lt_one (one_le_directionalLineDenominator h t)

theorem directionalLineDenominator_ne
    (h : Fin 2 → Real) (t : Real) :
    directionalLineDenominator h t ≠ 0 :=
  (directionalLineDenominator_pos h t).ne'

def directionalNorthPoleStereographicLine
    (h : Fin 2 → Real) (t : Real) : Fin 3 → Real :=
  ![2 * t * h 0 / directionalLineDenominator h t,
    2 * t * h 1 / directionalLineDenominator h t,
    (1 - t ^ 2 * directionalQubitNormSq h) /
      directionalLineDenominator h t]

theorem directionalStereographicLine_eq_chart_smul
    (h : Fin 2 → Real) (t : Real) :
    directionalNorthPoleStereographicLine h t =
      directionalNorthPoleStereographicChart (t • h) := by
  funext j
  fin_cases j <;>
    simp [directionalNorthPoleStereographicLine,
      directionalNorthPoleStereographicChart,
      directionalLineDenominator_eq_chart,
      directionalQubitNormSq_smul, Pi.smul_apply, smul_eq_mul] <;> ring

theorem directionalStereographicLine_normSq
    (h : Fin 2 → Real) (t : Real) :
    blochNormSq (directionalNorthPoleStereographicLine h t) = 1 := by
  rw [directionalStereographicLine_eq_chart_smul]
  exact directionalNorthPoleStereographicChart_normSq (t • h)

theorem directionalNorthPoleInverse_line
    (h : Fin 2 → Real) (t : Real) :
    directionalNorthPoleInverse
        (directionalNorthPoleStereographicLine h t) = t • h := by
  rw [directionalStereographicLine_eq_chart_smul]
  exact directionalNorthPoleInverse_chart (t • h)

@[simp]
theorem blochDot_axis_directionalNorthPole
    (axis : Fin 3 → Real) :
    blochDot axis directionalNorthPole = axis 2 := by
  simp [blochDot, directionalNorthPole, Fin.sum_univ_succ]

theorem directionalStereographicLine_distance_northPole
    (h : Fin 2 → Real) (t : Real) :
    blochNormSq (fun j =>
      directionalNorthPoleStereographicLine h t j -
        directionalNorthPole j) =
      4 * (t ^ 2 * directionalQubitNormSq h) /
        directionalLineDenominator h t := by
  have hDenominator := directionalLineDenominator_ne h t
  simp [blochNormSq, directionalNorthPoleStereographicLine,
    directionalNorthPole, directionalLineDenominator,
    directionalQubitNormSq, Fin.sum_univ_succ]
  field_simp [hDenominator]
  ring

theorem directionalStereographicLine_close_northPole
    (h : Fin 2 → Real) (t : Real)
    (hSafeguard :
      t ^ 2 * directionalQubitNormSq h ≤ (1 / 15 : Real)) :
    blochNormSq (fun j =>
      directionalNorthPoleStereographicLine h t j -
        directionalNorthPole j) ≤ (1 / 4 : Real) := by
  rw [directionalStereographicLine_distance_northPole]
  have hScaledNonnegative :
      0 ≤ t ^ 2 * directionalQubitNormSq h :=
    mul_nonneg (sq_nonneg t) (directionalQubitNormSq_nonnegative h)
  have hDenominatorPositive := directionalLineDenominator_pos h t
  apply (div_le_iff₀ hDenominatorPositive).2
  unfold directionalLineDenominator
  nlinarith

theorem directionalStereographicBornProbability_floor
    (axis : Fin 3 → Real) (h : Fin 2 → Real)
    (y : QubitRLSOutcome) (t : Real)
    (hAxis : blochNormSq axis = 1)
    (hTangent : axis 2 = 0)
    (hSafeguard :
      t ^ 2 * directionalQubitNormSq h ≤ (1 / 15 : Real)) :
    (1 / 4 : Real) ≤
      qubitRLSBornProbability
        (directionalNorthPoleStereographicLine h t) axis y := by
  apply pureQubitTangentBornProbability_floor
    (directionalNorthPoleStereographicLine h t)
    directionalNorthPole axis hAxis
  · simpa using hTangent
  · exact directionalStereographicLine_close_northPole h t hSafeguard

/-! ## Quadratic Born numerator and denominator -/

def directionalTangentOverlap
    (axis : Fin 3 → Real) (h : Fin 2 → Real) : Real :=
  axis 0 * h 0 + axis 1 * h 1

def directionalBornNumerator
    (axis : Fin 3 → Real) (h : Fin 2 → Real)
    (y : QubitRLSOutcome) (t : Real) : Real :=
  1 + qubitRLSOutcomeSign y * axis 2 +
    2 * qubitRLSOutcomeSign y * directionalTangentOverlap axis h * t +
    directionalQubitNormSq h *
      (1 - qubitRLSOutcomeSign y * axis 2) * t ^ 2

def directionalBornDenominator
    (h : Fin 2 → Real) (t : Real) : Real :=
  2 * directionalLineDenominator h t

theorem two_le_directionalBornDenominator
    (h : Fin 2 → Real) (t : Real) :
    2 ≤ directionalBornDenominator h t := by
  unfold directionalBornDenominator
  nlinarith [one_le_directionalLineDenominator h t]

theorem directionalBornDenominator_pos
    (h : Fin 2 → Real) (t : Real) :
    0 < directionalBornDenominator h t :=
  lt_of_lt_of_le (by norm_num) (two_le_directionalBornDenominator h t)

theorem directionalBornDenominator_ne
    (h : Fin 2 → Real) (t : Real) :
    directionalBornDenominator h t ≠ 0 :=
  (directionalBornDenominator_pos h t).ne'

theorem directionalBornProbability_eq_quadraticQuotient
    (axis : Fin 3 → Real) (h : Fin 2 → Real)
    (y : QubitRLSOutcome) (t : Real) :
    qubitRLSBornProbability
        (directionalNorthPoleStereographicLine h t) axis y =
      directionalBornNumerator axis h y t /
        directionalBornDenominator h t := by
  have hDenominator := directionalLineDenominator_ne h t
  simp [qubitRLSBornProbability, qubitBornTrace_eq, blochDot,
    directionalNorthPoleStereographicLine, directionalBornNumerator,
    directionalBornDenominator, directionalLineDenominator,
    directionalQubitNormSq, directionalTangentOverlap,
    Fin.sum_univ_succ]
  field_simp [hDenominator]
  ring

theorem directionalBornNumerator_eq_probability_mul_denominator
    (axis : Fin 3 → Real) (h : Fin 2 → Real)
    (y : QubitRLSOutcome) (t : Real) :
    directionalBornNumerator axis h y t =
      qubitRLSBornProbability
          (directionalNorthPoleStereographicLine h t) axis y *
        directionalBornDenominator h t := by
  rw [directionalBornProbability_eq_quadraticQuotient]
  field_simp [directionalBornDenominator_ne h t]

theorem directionalBornNumerator_floor
    (axis : Fin 3 → Real) (h : Fin 2 → Real)
    (y : QubitRLSOutcome) (t : Real)
    (hAxis : blochNormSq axis = 1)
    (hTangent : axis 2 = 0)
    (hSafeguard :
      t ^ 2 * directionalQubitNormSq h ≤ (1 / 15 : Real)) :
    (1 / 2 : Real) ≤ directionalBornNumerator axis h y t := by
  rw [directionalBornNumerator_eq_probability_mul_denominator]
  have hProbability := directionalStereographicBornProbability_floor
    axis h y t hAxis hTangent hSafeguard
  have hDenominator := two_le_directionalBornDenominator h t
  calc
    (1 / 2 : Real) = (1 / 4 : Real) * 2 := by ring
    _ ≤ qubitRLSBornProbability
          (directionalNorthPoleStereographicLine h t) axis y *
          directionalBornDenominator h t := by
      exact mul_le_mul hProbability hDenominator (by norm_num) (by linarith)

/-! ## Exact polynomial derivatives -/

def directionalBornNumeratorD1
    (axis : Fin 3 → Real) (h : Fin 2 → Real)
    (y : QubitRLSOutcome) (t : Real) : Real :=
  2 * qubitRLSOutcomeSign y * directionalTangentOverlap axis h +
    2 * directionalQubitNormSq h *
      (1 - qubitRLSOutcomeSign y * axis 2) * t

def directionalBornNumeratorD2
    (axis : Fin 3 → Real) (h : Fin 2 → Real)
    (y : QubitRLSOutcome) (_t : Real) : Real :=
  2 * directionalQubitNormSq h *
    (1 - qubitRLSOutcomeSign y * axis 2)

def directionalBornNumeratorD3
    (_axis : Fin 3 → Real) (_h : Fin 2 → Real)
    (_y : QubitRLSOutcome) (_t : Real) : Real :=
  0

def directionalBornDenominatorD1
    (h : Fin 2 → Real) (t : Real) : Real :=
  4 * directionalQubitNormSq h * t

def directionalBornDenominatorD2
    (h : Fin 2 → Real) (_t : Real) : Real :=
  4 * directionalQubitNormSq h

def directionalBornDenominatorD3
    (_h : Fin 2 → Real) (_t : Real) : Real :=
  0

theorem hasDerivAt_directionalBornNumerator
    (axis : Fin 3 → Real) (h : Fin 2 → Real)
    (y : QubitRLSOutcome) (t : Real) :
    HasDerivAt (directionalBornNumerator axis h y)
      (directionalBornNumeratorD1 axis h y t) t := by
  unfold directionalBornNumerator directionalBornNumeratorD1
  convert
    (((hasDerivAt_const (x := t)
      (c := 1 + qubitRLSOutcomeSign y * axis 2)).add
      ((hasDerivAt_id' t).const_mul
        (2 * qubitRLSOutcomeSign y * directionalTangentOverlap axis h))).add
      (((hasDerivAt_id' t).pow 2).const_mul
        (directionalQubitNormSq h *
          (1 - qubitRLSOutcomeSign y * axis 2)))) using 1
  all_goals first | rfl | ring

theorem hasDerivAt_directionalBornNumeratorD1
    (axis : Fin 3 → Real) (h : Fin 2 → Real)
    (y : QubitRLSOutcome) (t : Real) :
    HasDerivAt (directionalBornNumeratorD1 axis h y)
      (directionalBornNumeratorD2 axis h y t) t := by
  unfold directionalBornNumeratorD1 directionalBornNumeratorD2
  convert
    (hasDerivAt_const (x := t)
      (c := 2 * qubitRLSOutcomeSign y *
        directionalTangentOverlap axis h)).add
      ((hasDerivAt_id' t).const_mul
        (2 * directionalQubitNormSq h *
          (1 - qubitRLSOutcomeSign y * axis 2))) using 1
  all_goals first | rfl | ring

theorem hasDerivAt_directionalBornNumeratorD2
    (axis : Fin 3 → Real) (h : Fin 2 → Real)
    (y : QubitRLSOutcome) (t : Real) :
    HasDerivAt (directionalBornNumeratorD2 axis h y)
      (directionalBornNumeratorD3 axis h y t) t := by
  unfold directionalBornNumeratorD2 directionalBornNumeratorD3
  exact hasDerivAt_const (x := t)
    (c := 2 * directionalQubitNormSq h *
      (1 - qubitRLSOutcomeSign y * axis 2))

theorem hasDerivAt_directionalBornDenominator
    (h : Fin 2 → Real) (t : Real) :
    HasDerivAt (directionalBornDenominator h)
      (directionalBornDenominatorD1 h t) t := by
  unfold directionalBornDenominator directionalLineDenominator
  unfold directionalBornDenominatorD1
  convert
    (hasDerivAt_const (x := t) (c := (2 : Real))).add
      (((hasDerivAt_id' t).pow 2).const_mul
        (2 * directionalQubitNormSq h)) using 1
  all_goals first | rfl | (funext x; simp; ring) | ring

theorem hasDerivAt_directionalBornDenominatorD1
    (h : Fin 2 → Real) (t : Real) :
    HasDerivAt (directionalBornDenominatorD1 h)
      (directionalBornDenominatorD2 h t) t := by
  unfold directionalBornDenominatorD1 directionalBornDenominatorD2
  simpa [mul_assoc] using
    (hasDerivAt_id' t).const_mul
      (4 * directionalQubitNormSq h)

theorem hasDerivAt_directionalBornDenominatorD2
    (h : Fin 2 → Real) (t : Real) :
    HasDerivAt (directionalBornDenominatorD2 h)
      (directionalBornDenominatorD3 h t) t := by
  unfold directionalBornDenominatorD2 directionalBornDenominatorD3
  exact hasDerivAt_const (x := t) (c := 4 * directionalQubitNormSq h)

/-! ## Directional log likelihood and exact derivative chain -/

def directionalRationalLogLikelihood
    (axis : Fin 3 → Real) (h : Fin 2 → Real)
    (y : QubitRLSOutcome) : Real → Real :=
  fun t => Real.log (directionalBornNumerator axis h y t) -
    Real.log (directionalBornDenominator h t)

def directionalRationalLogLikelihoodD1
    (axis : Fin 3 → Real) (h : Fin 2 → Real)
    (y : QubitRLSOutcome) : Real → Real :=
  fun t =>
    directionalScalarScore
        (directionalBornNumerator axis h y)
        (directionalBornNumeratorD1 axis h y) t -
      directionalScalarScore
        (directionalBornDenominator h)
        (directionalBornDenominatorD1 h) t

def directionalRationalLogLikelihoodD2
    (axis : Fin 3 → Real) (h : Fin 2 → Real)
    (y : QubitRLSOutcome) : Real → Real :=
  fun t =>
    directionalScalarCurvature
        (directionalBornNumerator axis h y)
        (directionalBornNumeratorD1 axis h y)
        (directionalBornNumeratorD2 axis h y) t -
      directionalScalarCurvature
        (directionalBornDenominator h)
        (directionalBornDenominatorD1 h)
        (directionalBornDenominatorD2 h) t

def directionalRationalLogLikelihoodD3
    (axis : Fin 3 → Real) (h : Fin 2 → Real)
    (y : QubitRLSOutcome) : Real → Real :=
  fun t =>
    directionalScalarThird
        (directionalBornNumerator axis h y)
        (directionalBornNumeratorD1 axis h y)
        (directionalBornNumeratorD2 axis h y)
        (directionalBornNumeratorD3 axis h y) t -
      directionalScalarThird
        (directionalBornDenominator h)
        (directionalBornDenominatorD1 h)
        (directionalBornDenominatorD2 h)
        (directionalBornDenominatorD3 h) t

theorem directionalRationalLogLikelihood_eq_logBorn
    (axis : Fin 3 → Real) (h : Fin 2 → Real)
    (y : QubitRLSOutcome) (t : Real)
    (hAxis : blochNormSq axis = 1)
    (hTangent : axis 2 = 0)
    (hSafeguard :
      t ^ 2 * directionalQubitNormSq h ≤ (1 / 15 : Real)) :
    directionalRationalLogLikelihood axis h y t =
      Real.log (qubitRLSBornProbability
        (directionalNorthPoleStereographicLine h t) axis y) := by
  have hNumeratorPositive :
      0 < directionalBornNumerator axis h y t :=
    lt_of_lt_of_le (by norm_num)
      (directionalBornNumerator_floor
        axis h y t hAxis hTangent hSafeguard)
  have hDenominatorPositive := directionalBornDenominator_pos h t
  rw [directionalBornProbability_eq_quadraticQuotient]
  simpa [directionalRationalLogLikelihood] using
    (Real.log_div hNumeratorPositive.ne'
      hDenominatorPositive.ne').symm

theorem directionalRationalLogLikelihood_derivativeChain
    (axis : Fin 3 → Real) (h : Fin 2 → Real)
    (y : QubitRLSOutcome) (t : Real)
    (hAxis : blochNormSq axis = 1)
    (hTangent : axis 2 = 0)
    (hSafeguard :
      t ^ 2 * directionalQubitNormSq h ≤ (1 / 15 : Real)) :
    HasDerivAt (directionalRationalLogLikelihood axis h y)
        (directionalRationalLogLikelihoodD1 axis h y t) t ∧
      HasDerivAt (directionalRationalLogLikelihoodD1 axis h y)
        (directionalRationalLogLikelihoodD2 axis h y t) t ∧
      HasDerivAt (directionalRationalLogLikelihoodD2 axis h y)
        (directionalRationalLogLikelihoodD3 axis h y t) t := by
  have hN0 := hasDerivAt_directionalBornNumerator axis h y t
  have hN1 := hasDerivAt_directionalBornNumeratorD1 axis h y t
  have hN2 := hasDerivAt_directionalBornNumeratorD2 axis h y t
  have hD0 := hasDerivAt_directionalBornDenominator h t
  have hD1 := hasDerivAt_directionalBornDenominatorD1 h t
  have hD2 := hasDerivAt_directionalBornDenominatorD2 h t
  have hNPositive : 0 < directionalBornNumerator axis h y t :=
    lt_of_lt_of_le (by norm_num)
      (directionalBornNumerator_floor
        axis h y t hAxis hTangent hSafeguard)
  have hDPositive := directionalBornDenominator_pos h t
  have hNLog0 := hasDerivAt_directionalScalarLog
    (directionalBornNumerator axis h y)
    (directionalBornNumeratorD1 axis h y) t hN0 hNPositive
  have hDLog0 := hasDerivAt_directionalScalarLog
    (directionalBornDenominator h)
    (directionalBornDenominatorD1 h) t hD0 hDPositive
  have hNLog1 := hasDerivAt_directionalScalarScore
    (directionalBornNumerator axis h y)
    (directionalBornNumeratorD1 axis h y)
    (directionalBornNumeratorD2 axis h y) t hN0 hN1 hNPositive
  have hDLog1 := hasDerivAt_directionalScalarScore
    (directionalBornDenominator h)
    (directionalBornDenominatorD1 h)
    (directionalBornDenominatorD2 h) t hD0 hD1 hDPositive
  have hNLog2 := hasDerivAt_directionalScalarCurvature
    (directionalBornNumerator axis h y)
    (directionalBornNumeratorD1 axis h y)
    (directionalBornNumeratorD2 axis h y)
    (directionalBornNumeratorD3 axis h y) t hN0 hN1 hN2 hNPositive
  have hDLog2 := hasDerivAt_directionalScalarCurvature
    (directionalBornDenominator h)
    (directionalBornDenominatorD1 h)
    (directionalBornDenominatorD2 h)
    (directionalBornDenominatorD3 h) t hD0 hD1 hD2 hDPositive
  constructor
  · unfold directionalRationalLogLikelihood
      directionalRationalLogLikelihoodD1
    exact hNLog0.sub hDLog0
  constructor
  · unfold directionalRationalLogLikelihoodD1
      directionalRationalLogLikelihoodD2
    exact hNLog1.sub hDLog1
  · unfold directionalRationalLogLikelihoodD2
      directionalRationalLogLikelihoodD3
    exact hNLog2.sub hDLog2

/-! ## Elementary uniform component bounds -/

theorem abs_qubitRLSOutcomeSign_directional_eq_one
    (y : QubitRLSOutcome) :
    |qubitRLSOutcomeSign y| = 1 := by
  cases y <;> norm_num [qubitRLSOutcomeSign]

theorem abs_directionalTangentOverlap_le_one
    (axis : Fin 3 → Real) (h : Fin 2 → Real)
    (hAxis : blochNormSq axis = 1)
    (hTangent : axis 2 = 0)
    (hNorm : directionalQubitNormSq h ≤ 1) :
    |directionalTangentOverlap axis h| ≤ 1 := by
  have hAxisPlane : axis 0 ^ 2 + axis 1 ^ 2 = 1 := by
    have h := hAxis
    simp [blochNormSq, Fin.sum_univ_succ, hTangent] at h
    nlinarith
  have hIdentity :
      directionalTangentOverlap axis h ^ 2 +
          (axis 0 * h 1 - axis 1 * h 0) ^ 2 =
        (axis 0 ^ 2 + axis 1 ^ 2) * directionalQubitNormSq h := by
    unfold directionalTangentOverlap directionalQubitNormSq
    ring
  have hSquare : directionalTangentOverlap axis h ^ 2 ≤ 1 := by
    calc
      directionalTangentOverlap axis h ^ 2 ≤
          directionalTangentOverlap axis h ^ 2 +
            (axis 0 * h 1 - axis 1 * h 0) ^ 2 := by
        nlinarith [sq_nonneg (axis 0 * h 1 - axis 1 * h 0)]
      _ = (axis 0 ^ 2 + axis 1 ^ 2) *
          directionalQubitNormSq h := hIdentity
      _ = directionalQubitNormSq h := by rw [hAxisPlane]; ring
      _ ≤ 1 := hNorm
  rw [← sq_abs] at hSquare
  nlinarith [abs_nonneg (directionalTangentOverlap axis h)]

theorem abs_directionalBornNumeratorD1_le_four
    (axis : Fin 3 → Real) (h : Fin 2 → Real)
    (y : QubitRLSOutcome) (t : Real)
    (hAxis : blochNormSq axis = 1)
    (hTangent : axis 2 = 0)
    (hNorm : directionalQubitNormSq h ≤ 1)
    (hTime : |t| ≤ 1) :
    |directionalBornNumeratorD1 axis h y t| ≤ 4 := by
  have hOverlap :=
    abs_directionalTangentOverlap_le_one
      axis h hAxis hTangent hNorm
  have hNormNonnegative := directionalQubitNormSq_nonnegative h
  have hFirst :
      |2 * qubitRLSOutcomeSign y *
        directionalTangentOverlap axis h| ≤ 2 := by
    rw [abs_mul, abs_mul, abs_qubitRLSOutcomeSign_directional_eq_one]
    norm_num
    nlinarith
  have hSecond :
      |2 * directionalQubitNormSq h * t| ≤ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hNormNonnegative]
    norm_num
    have hProduct : directionalQubitNormSq h * |t| ≤ 1 := by
      nlinarith [mul_nonneg hNormNonnegative (abs_nonneg t),
        mul_le_mul hNorm hTime (abs_nonneg t) (by norm_num : 0 ≤ (1 : Real))]
    nlinarith
  have hFormula :
      directionalBornNumeratorD1 axis h y t =
        2 * qubitRLSOutcomeSign y * directionalTangentOverlap axis h +
          2 * directionalQubitNormSq h * t := by
    simp [directionalBornNumeratorD1, hTangent]
  rw [hFormula]
  exact (abs_add_le _ _).trans (by nlinarith [hFirst, hSecond])

theorem abs_directionalBornNumeratorD2_le_two
    (axis : Fin 3 → Real) (h : Fin 2 → Real)
    (y : QubitRLSOutcome) (t : Real)
    (hTangent : axis 2 = 0)
    (hNorm : directionalQubitNormSq h ≤ 1) :
    |directionalBornNumeratorD2 axis h y t| ≤ 2 := by
  have hNormNonnegative := directionalQubitNormSq_nonnegative h
  have hFormula :
      directionalBornNumeratorD2 axis h y t =
        2 * directionalQubitNormSq h := by
    simp [directionalBornNumeratorD2, hTangent]
  rw [hFormula, abs_of_nonneg (mul_nonneg (by norm_num) hNormNonnegative)]
  nlinarith

theorem abs_directionalBornDenominatorD1_le_four
    (h : Fin 2 → Real) (t : Real)
    (hNorm : directionalQubitNormSq h ≤ 1)
    (hTime : |t| ≤ 1) :
    |directionalBornDenominatorD1 h t| ≤ 4 := by
  have hNormNonnegative := directionalQubitNormSq_nonnegative h
  rw [directionalBornDenominatorD1, abs_mul, abs_mul,
    abs_of_nonneg hNormNonnegative]
  norm_num
  have hProduct : directionalQubitNormSq h * |t| ≤ 1 := by
    simpa using mul_le_mul hNorm hTime (abs_nonneg t)
      (by norm_num : 0 ≤ (1 : Real))
  nlinarith

theorem abs_directionalBornDenominatorD2_le_four
    (h : Fin 2 → Real) (t : Real)
    (hNorm : directionalQubitNormSq h ≤ 1) :
    |directionalBornDenominatorD2 h t| ≤ 4 := by
  have hNormNonnegative := directionalQubitNormSq_nonnegative h
  rw [directionalBornDenominatorD2,
    abs_of_nonneg (mul_nonneg (by norm_num) hNormNonnegative)]
  nlinarith

private theorem abs_sq_le_sq_of_abs_le
    (x c : Real) (hc : 0 ≤ c) (hx : |x| ≤ c) :
    |x ^ 2| ≤ c ^ 2 := by
  rw [abs_of_nonneg (sq_nonneg x), ← sq_abs]
  have hProduct : 0 ≤ (c - |x|) * (c + |x|) :=
    mul_nonneg (sub_nonneg.mpr hx) (add_nonneg hc (abs_nonneg x))
  nlinarith

private theorem abs_cube_le_cube_of_abs_le
    (x c : Real) (hc : 0 ≤ c) (hx : |x| ≤ c) :
    |x ^ 3| ≤ c ^ 3 := by
  rw [abs_pow]
  have hSquare := abs_sq_le_sq_of_abs_le x c hc hx
  rw [abs_of_nonneg (sq_nonneg x)] at hSquare
  rw [← sq_abs] at hSquare
  calc
    |x| ^ 3 = |x| ^ 2 * |x| := by ring
    _ ≤ c ^ 2 * c :=
      mul_le_mul hSquare hx (abs_nonneg x) (sq_nonneg c)
    _ = c ^ 3 := by ring

private theorem abs_curvature_le
    (r1 r2 b1 b2 : Real)
    (hr1 : |r1| ≤ b1) (hr2 : |r2| ≤ b2)
    (hb1 : 0 ≤ b1) :
    |r2 - r1 ^ 2| ≤ b2 + b1 ^ 2 := by
  calc
    |r2 - r1 ^ 2| ≤ |r2| + |r1 ^ 2| := abs_sub _ _
    _ ≤ b2 + b1 ^ 2 :=
      add_le_add hr2 (abs_sq_le_sq_of_abs_le r1 b1 hb1 hr1)

private theorem abs_third_le
    (r1 r2 r3 b1 b2 b3 : Real)
    (hr1 : |r1| ≤ b1) (hr2 : |r2| ≤ b2)
    (hr3 : |r3| ≤ b3)
    (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2) :
    |r3 - 3 * r1 * r2 + 2 * r1 ^ 3| ≤
      b3 + 3 * b1 * b2 + 2 * b1 ^ 3 := by
  have hProduct : |r1| * |r2| ≤ b1 * b2 :=
    mul_le_mul hr1 hr2 (abs_nonneg r2) hb1
  have hMiddle : |3 * r1 * r2| ≤ 3 * b1 * b2 := by
    calc
      |3 * r1 * r2| = 3 * (|r1| * |r2|) := by
        simp only [abs_mul]
        norm_num
        ring
      _ ≤ 3 * (b1 * b2) :=
        mul_le_mul_of_nonneg_left hProduct (by norm_num)
      _ = 3 * b1 * b2 := by ring
  have hCubic : |2 * r1 ^ 3| ≤ 2 * b1 ^ 3 := by
    calc
      |2 * r1 ^ 3| = 2 * |r1 ^ 3| := by rw [abs_mul]; norm_num
      _ ≤ 2 * b1 ^ 3 :=
        mul_le_mul_of_nonneg_left
          (abs_cube_le_cube_of_abs_le r1 b1 hb1 hr1) (by norm_num)
  calc
    |r3 - 3 * r1 * r2 + 2 * r1 ^ 3| ≤
        |r3 - 3 * r1 * r2| + |2 * r1 ^ 3| := abs_add_le _ _
    _ ≤ (|r3| + |3 * r1 * r2|) + |2 * r1 ^ 3| :=
      add_le_add (abs_sub _ _) le_rfl
    _ ≤ (b3 + 3 * b1 * b2) + 2 * b1 ^ 3 :=
      add_le_add (add_le_add hr3 hMiddle) hCubic
    _ = b3 + 3 * b1 * b2 + 2 * b1 ^ 3 := by ring

/-! ## Explicit directional log-likelihood bounds -/

theorem abs_directionalRationalLogLikelihoodD1_le_ten
    (axis : Fin 3 → Real) (h : Fin 2 → Real)
    (y : QubitRLSOutcome) (t : Real)
    (hAxis : blochNormSq axis = 1)
    (hTangent : axis 2 = 0)
    (hNorm : directionalQubitNormSq h ≤ 1)
    (hTime : |t| ≤ 1)
    (hSafeguard :
      t ^ 2 * directionalQubitNormSq h ≤ (1 / 15 : Real)) :
    |directionalRationalLogLikelihoodD1 axis h y t| ≤ 10 := by
  have hNFloor := directionalBornNumerator_floor
    axis h y t hAxis hTangent hSafeguard
  have hN1 := abs_directionalBornNumeratorD1_le_four
    axis h y t hAxis hTangent hNorm hTime
  have hDFloor := two_le_directionalBornDenominator h t
  have hD1 := abs_directionalBornDenominatorD1_le_four h t hNorm hTime
  have hNRatio :
      |directionalBornNumeratorD1 axis h y t /
        directionalBornNumerator axis h y t| ≤ 8 := by
    have h := abs_div_le_directionalFloor
      (1 / 2 : Real) 4
      (directionalBornNumerator axis h y t)
      (directionalBornNumeratorD1 axis h y t)
      (by norm_num) hNFloor (by norm_num) hN1
    norm_num at h
    exact h
  have hDRatio :
      |directionalBornDenominatorD1 h t /
        directionalBornDenominator h t| ≤ 2 := by
    have h := abs_div_le_directionalFloor
      2 4 (directionalBornDenominator h t)
      (directionalBornDenominatorD1 h t)
      (by norm_num) hDFloor (by norm_num) hD1
    norm_num at h
    exact h
  unfold directionalRationalLogLikelihoodD1 directionalScalarScore
  exact (abs_sub _ _).trans (by nlinarith)

theorem abs_directionalRationalLogLikelihoodD2_le_eighty
    (axis : Fin 3 → Real) (h : Fin 2 → Real)
    (y : QubitRLSOutcome) (t : Real)
    (hAxis : blochNormSq axis = 1)
    (hTangent : axis 2 = 0)
    (hNorm : directionalQubitNormSq h ≤ 1)
    (hTime : |t| ≤ 1)
    (hSafeguard :
      t ^ 2 * directionalQubitNormSq h ≤ (1 / 15 : Real)) :
    |directionalRationalLogLikelihoodD2 axis h y t| ≤ 80 := by
  have hNFloor := directionalBornNumerator_floor
    axis h y t hAxis hTangent hSafeguard
  have hN1 := abs_directionalBornNumeratorD1_le_four
    axis h y t hAxis hTangent hNorm hTime
  have hN2 := abs_directionalBornNumeratorD2_le_two
    axis h y t hTangent hNorm
  have hDFloor := two_le_directionalBornDenominator h t
  have hD1 := abs_directionalBornDenominatorD1_le_four h t hNorm hTime
  have hD2 := abs_directionalBornDenominatorD2_le_four h t hNorm
  have hN1Ratio :
      |directionalBornNumeratorD1 axis h y t /
        directionalBornNumerator axis h y t| ≤ 8 := by
    have h := abs_div_le_directionalFloor
      (1 / 2 : Real) 4
      (directionalBornNumerator axis h y t)
      (directionalBornNumeratorD1 axis h y t)
      (by norm_num) hNFloor (by norm_num) hN1
    norm_num at h
    exact h
  have hN2Ratio :
      |directionalBornNumeratorD2 axis h y t /
        directionalBornNumerator axis h y t| ≤ 4 := by
    have h := abs_div_le_directionalFloor
      (1 / 2 : Real) 2
      (directionalBornNumerator axis h y t)
      (directionalBornNumeratorD2 axis h y t)
      (by norm_num) hNFloor (by norm_num) hN2
    norm_num at h
    exact h
  have hD1Ratio :
      |directionalBornDenominatorD1 h t /
        directionalBornDenominator h t| ≤ 2 := by
    have h := abs_div_le_directionalFloor
      2 4 (directionalBornDenominator h t)
      (directionalBornDenominatorD1 h t)
      (by norm_num) hDFloor (by norm_num) hD1
    norm_num at h
    exact h
  have hD2Ratio :
      |directionalBornDenominatorD2 h t /
        directionalBornDenominator h t| ≤ 2 := by
    have h := abs_div_le_directionalFloor
      2 4 (directionalBornDenominator h t)
      (directionalBornDenominatorD2 h t)
      (by norm_num) hDFloor (by norm_num) hD2
    norm_num at h
    exact h
  have hNumeratorCurvature :
      |directionalScalarCurvature
        (directionalBornNumerator axis h y)
        (directionalBornNumeratorD1 axis h y)
        (directionalBornNumeratorD2 axis h y) t| ≤ 68 := by
    unfold directionalScalarCurvature
    have hBound := abs_curvature_le
      (directionalBornNumeratorD1 axis h y t /
        directionalBornNumerator axis h y t)
      (directionalBornNumeratorD2 axis h y t /
        directionalBornNumerator axis h y t)
      8 4 hN1Ratio hN2Ratio (by norm_num)
    norm_num at hBound
    exact hBound
  have hDenominatorCurvature :
      |directionalScalarCurvature
        (directionalBornDenominator h)
        (directionalBornDenominatorD1 h)
        (directionalBornDenominatorD2 h) t| ≤ 6 := by
    unfold directionalScalarCurvature
    have hBound := abs_curvature_le
      (directionalBornDenominatorD1 h t /
        directionalBornDenominator h t)
      (directionalBornDenominatorD2 h t /
        directionalBornDenominator h t)
      2 2 hD1Ratio hD2Ratio (by norm_num)
    norm_num at hBound
    exact hBound
  unfold directionalRationalLogLikelihoodD2
  exact (abs_sub _ _).trans (by nlinarith)

theorem abs_directionalRationalLogLikelihoodD3_le_twelveHundred
    (axis : Fin 3 → Real) (h : Fin 2 → Real)
    (y : QubitRLSOutcome) (t : Real)
    (hAxis : blochNormSq axis = 1)
    (hTangent : axis 2 = 0)
    (hNorm : directionalQubitNormSq h ≤ 1)
    (hTime : |t| ≤ 1)
    (hSafeguard :
      t ^ 2 * directionalQubitNormSq h ≤ (1 / 15 : Real)) :
    |directionalRationalLogLikelihoodD3 axis h y t| ≤ 1200 := by
  have hNFloor := directionalBornNumerator_floor
    axis h y t hAxis hTangent hSafeguard
  have hN1 := abs_directionalBornNumeratorD1_le_four
    axis h y t hAxis hTangent hNorm hTime
  have hN2 := abs_directionalBornNumeratorD2_le_two
    axis h y t hTangent hNorm
  have hDFloor := two_le_directionalBornDenominator h t
  have hD1 := abs_directionalBornDenominatorD1_le_four h t hNorm hTime
  have hD2 := abs_directionalBornDenominatorD2_le_four h t hNorm
  have hN1Ratio :
      |directionalBornNumeratorD1 axis h y t /
        directionalBornNumerator axis h y t| ≤ 8 := by
    have h := abs_div_le_directionalFloor
      (1 / 2 : Real) 4
      (directionalBornNumerator axis h y t)
      (directionalBornNumeratorD1 axis h y t)
      (by norm_num) hNFloor (by norm_num) hN1
    norm_num at h
    exact h
  have hN2Ratio :
      |directionalBornNumeratorD2 axis h y t /
        directionalBornNumerator axis h y t| ≤ 4 := by
    have h := abs_div_le_directionalFloor
      (1 / 2 : Real) 2
      (directionalBornNumerator axis h y t)
      (directionalBornNumeratorD2 axis h y t)
      (by norm_num) hNFloor (by norm_num) hN2
    norm_num at h
    exact h
  have hD1Ratio :
      |directionalBornDenominatorD1 h t /
        directionalBornDenominator h t| ≤ 2 := by
    have h := abs_div_le_directionalFloor
      2 4 (directionalBornDenominator h t)
      (directionalBornDenominatorD1 h t)
      (by norm_num) hDFloor (by norm_num) hD1
    norm_num at h
    exact h
  have hD2Ratio :
      |directionalBornDenominatorD2 h t /
        directionalBornDenominator h t| ≤ 2 := by
    have h := abs_div_le_directionalFloor
      2 4 (directionalBornDenominator h t)
      (directionalBornDenominatorD2 h t)
      (by norm_num) hDFloor (by norm_num) hD2
    norm_num at h
    exact h
  have hNumeratorThird :
      |directionalScalarThird
        (directionalBornNumerator axis h y)
        (directionalBornNumeratorD1 axis h y)
        (directionalBornNumeratorD2 axis h y)
        (directionalBornNumeratorD3 axis h y) t| ≤ 1120 := by
    unfold directionalScalarThird
    have hBound := abs_third_le
      (directionalBornNumeratorD1 axis h y t /
        directionalBornNumerator axis h y t)
      (directionalBornNumeratorD2 axis h y t /
        directionalBornNumerator axis h y t)
      (directionalBornNumeratorD3 axis h y t /
        directionalBornNumerator axis h y t)
      8 4 0 hN1Ratio hN2Ratio
      (by simp [directionalBornNumeratorD3])
      (by norm_num) (by norm_num)
    norm_num at hBound
    exact hBound
  have hDenominatorThird :
      |directionalScalarThird
        (directionalBornDenominator h)
        (directionalBornDenominatorD1 h)
        (directionalBornDenominatorD2 h)
        (directionalBornDenominatorD3 h) t| ≤ 28 := by
    unfold directionalScalarThird
    have hBound := abs_third_le
      (directionalBornDenominatorD1 h t /
        directionalBornDenominator h t)
      (directionalBornDenominatorD2 h t /
        directionalBornDenominator h t)
      (directionalBornDenominatorD3 h t /
        directionalBornDenominator h t)
      2 2 0 hD1Ratio hD2Ratio
      (by simp [directionalBornDenominatorD3])
      (by norm_num) (by norm_num)
    norm_num at hBound
    exact hBound
  unfold directionalRationalLogLikelihoodD3
  exact (abs_sub _ _).trans (by nlinarith)

/-! ## Honest sufficient directional regularity package -/

/-- Concrete sufficient regularity statement for one fixed local line. -/
structure OneQubitDirectionalRegularityCertificate
    (axis : Fin 3 → Real) (h : Fin 2 → Real)
    (y : QubitRLSOutcome) (t : Real) : Prop where
  chart_is_pure :
    blochNormSq (directionalNorthPoleStereographicLine h t) = 1
  inverse_chart :
    directionalNorthPoleInverse
        (directionalNorthPoleStereographicLine h t) = t • h
  born_probability_floor :
    (1 / 4 : Real) ≤ qubitRLSBornProbability
      (directionalNorthPoleStereographicLine h t) axis y
  log_identification :
    directionalRationalLogLikelihood axis h y t =
      Real.log (qubitRLSBornProbability
        (directionalNorthPoleStereographicLine h t) axis y)
  derivative_chain :
    HasDerivAt (directionalRationalLogLikelihood axis h y)
        (directionalRationalLogLikelihoodD1 axis h y t) t ∧
      HasDerivAt (directionalRationalLogLikelihoodD1 axis h y)
        (directionalRationalLogLikelihoodD2 axis h y t) t ∧
      HasDerivAt (directionalRationalLogLikelihoodD2 axis h y)
        (directionalRationalLogLikelihoodD3 axis h y t) t
  first_derivative_bound :
    |directionalRationalLogLikelihoodD1 axis h y t| ≤ 10
  second_derivative_bound :
    |directionalRationalLogLikelihoodD2 axis h y t| ≤ 80
  third_derivative_bound :
    |directionalRationalLogLikelihoodD3 axis h y t| ≤ 1200

theorem oneQubitDirectionalRegularity_of_safeguard
    (axis : Fin 3 → Real) (h : Fin 2 → Real)
    (y : QubitRLSOutcome) (t : Real)
    (hAxis : blochNormSq axis = 1)
    (hTangent : axis 2 = 0)
    (hNorm : directionalQubitNormSq h ≤ 1)
    (hTime : |t| ≤ 1)
    (hSafeguard :
      t ^ 2 * directionalQubitNormSq h ≤ (1 / 15 : Real)) :
    OneQubitDirectionalRegularityCertificate axis h y t where
  chart_is_pure := directionalStereographicLine_normSq h t
  inverse_chart := directionalNorthPoleInverse_line h t
  born_probability_floor :=
    directionalStereographicBornProbability_floor
      axis h y t hAxis hTangent hSafeguard
  log_identification :=
    directionalRationalLogLikelihood_eq_logBorn
      axis h y t hAxis hTangent hSafeguard
  derivative_chain :=
    directionalRationalLogLikelihood_derivativeChain
      axis h y t hAxis hTangent hSafeguard
  first_derivative_bound :=
    abs_directionalRationalLogLikelihoodD1_le_ten
      axis h y t hAxis hTangent hNorm hTime hSafeguard
  second_derivative_bound :=
    abs_directionalRationalLogLikelihoodD2_le_eighty
      axis h y t hAxis hTangent hNorm hTime hSafeguard
  third_derivative_bound :=
    abs_directionalRationalLogLikelihoodD3_le_twelveHundred
      axis h y t hAxis hTangent hNorm hTime hSafeguard

namespace Label

/-- One-qubit, north-pole, fixed-line reduction of
`lem:SI_r1_regularity`.  The suffix records that this theorem supplies the
directional regularity needed for scalar Taylor/LAN, not a general
multivariate moving-chart statement. -/
theorem lem_SI_r1_regularity_qubit_directional_reduction
    (axis : Fin 3 → Real) (h : Fin 2 → Real)
    (y : QubitRLSOutcome) (t : Real)
    (hAxis : blochNormSq axis = 1)
    (hTangent : axis 2 = 0)
    (hNorm : directionalQubitNormSq h ≤ 1)
    (hTime : |t| ≤ 1)
    (hSafeguard :
      t ^ 2 * directionalQubitNormSq h ≤ (1 / 15 : Real)) :
    OneQubitDirectionalRegularityCertificate axis h y t :=
  oneQubitDirectionalRegularity_of_safeguard
    axis h y t hAxis hTangent hNorm hTime hSafeguard

end Label

end

end QubitOracle.Paper
