import QubitOracle.FiniteGillMassar
import QubitOracle.RankOneLosses
import QubitOracle.TwoBasis
/-!
# Deterministic pure-qubit coordinate geometry

This module isolates the two elementary coordinate systems used by the
one-qubit Bures calculations.  It has no controller, LAN, MLE, or minimax
dependency.
-/

namespace QubitOracle

open scoped BigOperators

noncomputable section

/-! ## North-pole inverse and stereographic chart in `Fin 2` -/

def directionalQubitNormSq (h : Fin 2 -> Real) : Real :=
  h 0 ^ 2 + h 1 ^ 2

theorem directionalQubitNormSq_nonnegative (h : Fin 2 -> Real) :
    0 <= directionalQubitNormSq h := by
  unfold directionalQubitNormSq
  positivity

theorem directionalQubitNormSq_smul
    (t : Real) (h : Fin 2 -> Real) :
    directionalQubitNormSq (t • h) =
      t ^ 2 * directionalQubitNormSq h := by
  simp [directionalQubitNormSq, Pi.smul_apply, smul_eq_mul]
  ring

def directionalNorthPole : Fin 3 -> Real :=
  ![0, 0, 1]

def directionalNorthPoleInverse
    (r : Fin 3 -> Real) : Fin 2 -> Real :=
  fun i =>
    if i = 0 then r 0 / (1 + r 2)
    else r 1 / (1 + r 2)

def directionalStereographicDenominator
    (u : Fin 2 -> Real) : Real :=
  1 + directionalQubitNormSq u

theorem directionalStereographicDenominator_pos
    (u : Fin 2 -> Real) :
    0 < directionalStereographicDenominator u := by
  unfold directionalStereographicDenominator
  have hq := directionalQubitNormSq_nonnegative u
  linarith

theorem directionalStereographicDenominator_ne
    (u : Fin 2 -> Real) :
    directionalStereographicDenominator u ≠ 0 :=
  (directionalStereographicDenominator_pos u).ne'

def directionalNorthPoleStereographicChart
    (u : Fin 2 -> Real) : Fin 3 -> Real :=
  ![2 * u 0 / directionalStereographicDenominator u,
    2 * u 1 / directionalStereographicDenominator u,
    (1 - directionalQubitNormSq u) /
      directionalStereographicDenominator u]

theorem directionalNorthPoleStereographicChart_normSq
    (u : Fin 2 -> Real) :
    blochNormSq (directionalNorthPoleStereographicChart u) = 1 := by
  have hDenominator := directionalStereographicDenominator_ne u
  simp [blochNormSq, directionalNorthPoleStereographicChart,
    directionalStereographicDenominator, directionalQubitNormSq,
    Fin.sum_univ_succ]
  field_simp [hDenominator]
  ring

theorem directionalNorthPoleInverse_chart
    (u : Fin 2 -> Real) :
    directionalNorthPoleInverse
        (directionalNorthPoleStereographicChart u) = u := by
  have hDenominator := directionalStereographicDenominator_ne u
  funext i
  fin_cases i <;>
    simp [directionalNorthPoleInverse,
      directionalNorthPoleStereographicChart,
      directionalStereographicDenominator, directionalQubitNormSq] <;>
    field_simp [hDenominator] <;> ring

/-! ## Rank-one Bloch chart in `Fin 2` -/

def finTwoQubitRadiusSq (h : Fin 2 -> Real) : Real :=
  ∑ j, h j ^ 2

theorem finTwoQubitRadiusSq_nonnegative (h : Fin 2 -> Real) :
    0 <= finTwoQubitRadiusSq h := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem finTwoQubitRadiusSq_smul
    (a : Real) (h : Fin 2 -> Real) :
    finTwoQubitRadiusSq (a • h) = a ^ 2 * finTwoQubitRadiusSq h := by
  unfold finTwoQubitRadiusSq
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

def finTwoAsQubitTangent
    (h : Fin 2 -> Real) : QubitOracle.TangentIndex 1 -> Real
  | Sum.inl _ => h 0
  | Sum.inr _ => h 1

theorem tangentRadiusSq_finTwoAsQubitTangent
    (h : Fin 2 -> Real) :
    tangentRadiusSq (finTwoAsQubitTangent h) = finTwoQubitRadiusSq h := by
  simp [tangentRadiusSq, finTwoAsQubitTangent,
    finTwoQubitRadiusSq, Fin.sum_univ_succ]

theorem finTwoAsQubitTangent_smul
    (a : Real) (h : Fin 2 -> Real) :
    finTwoAsQubitTangent (a • h) = a • finTwoAsQubitTangent h := by
  funext j
  cases j <;> simp [finTwoAsQubitTangent]

def localPureQubitNorthPole : Fin 3 -> Real :=
  ![0, 0, 1]

theorem localPureQubitNorthPole_normSq :
    blochNormSq localPureQubitNorthPole = 1 := by
  simp [localPureQubitNorthPole, blochNormSq, Fin.sum_univ_succ]

noncomputable def pureQubitRankOneBlochChart
    (k : Fin 2 -> Real) : Fin 3 -> Real :=
  ![k 0 * Real.sqrt (1 - finTwoQubitRadiusSq k / 4),
    k 1 * Real.sqrt (1 - finTwoQubitRadiusSq k / 4),
    1 - finTwoQubitRadiusSq k / 2]

theorem pureQubitRankOneBlochChart_normSq
    (k : Fin 2 -> Real)
    (hChart : finTwoQubitRadiusSq k <= 4) :
    blochNormSq (pureQubitRankOneBlochChart k) = 1 := by
  have hRadiusNonnegative := finTwoQubitRadiusSq_nonnegative k
  have hRootArgument : 0 <= 1 - finTwoQubitRadiusSq k / 4 := by
    linarith
  have hRootSq :
      Real.sqrt (1 - finTwoQubitRadiusSq k / 4) ^ 2 =
        1 - finTwoQubitRadiusSq k / 4 :=
    Real.sq_sqrt hRootArgument
  simp [pureQubitRankOneBlochChart, blochNormSq,
    finTwoQubitRadiusSq, Fin.sum_univ_succ] at hRootSq ⊢
  nlinarith

theorem pureQubitRankOneBlochChart_distance_northPole
    (k : Fin 2 -> Real)
    (hChart : finTwoQubitRadiusSq k <= 4) :
    blochNormSq
        (fun j => pureQubitRankOneBlochChart k j -
          localPureQubitNorthPole j) =
      finTwoQubitRadiusSq k := by
  have hRadiusNonnegative := finTwoQubitRadiusSq_nonnegative k
  have hRootArgument : 0 <= 1 - finTwoQubitRadiusSq k / 4 := by
    linarith
  have hRootSq :
      Real.sqrt (1 - finTwoQubitRadiusSq k / 4) ^ 2 =
        1 - finTwoQubitRadiusSq k / 4 :=
    Real.sq_sqrt hRootArgument
  simp [pureQubitRankOneBlochChart, localPureQubitNorthPole,
    blochNormSq, finTwoQubitRadiusSq, Fin.sum_univ_succ] at hRootSq ⊢
  nlinarith

theorem pureQubitRankOneBlochChart_reverse_distance_northPole
    (k : Fin 2 -> Real)
    (hChart : finTwoQubitRadiusSq k <= 4) :
    blochNormSq
        (fun j => localPureQubitNorthPole j -
          pureQubitRankOneBlochChart k j) =
      finTwoQubitRadiusSq k := by
  have hForward := pureQubitRankOneBlochChart_distance_northPole k hChart
  calc
    blochNormSq
        (fun j => localPureQubitNorthPole j -
          pureQubitRankOneBlochChart k j) =
      blochNormSq
        (fun j => pureQubitRankOneBlochChart k j -
          localPureQubitNorthPole j) := by
        unfold blochNormSq
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ = finTwoQubitRadiusSq k := hForward

theorem pureQubitRankOneBlochChart_fidelity_northPole
    (k : Fin 2 -> Real) :
    (1 + blochDot localPureQubitNorthPole
      (pureQubitRankOneBlochChart k)) / 2 =
        1 - finTwoQubitRadiusSq k / 4 := by
  simp [pureQubitRankOneBlochChart, localPureQubitNorthPole,
    blochDot, finTwoQubitRadiusSq, Fin.sum_univ_succ]
  ring

end

end QubitOracle
