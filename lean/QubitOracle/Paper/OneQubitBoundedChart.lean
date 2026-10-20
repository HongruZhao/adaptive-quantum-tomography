import QubitOracle.FiniteGillMassar
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# A bounded inverse chart for the north-pole qubit model

This file stays entirely in Bloch coordinates.  The truth is the north pole
`(0, 0, 1)`, and the local two-dimensional coordinate is the inverse
stereographic map

`r |-> (r 0 / (1 + r 2), r 1 / (1 + r 2))`.

For a fixed safeguard `eta`, the measurable extension uses this coordinate
only on `eta <= 1 + r 2`; it is zero elsewhere.  On the Bloch ball and for
`eta > 0`, every coordinate is bounded by `eta⁻¹`, and its two-dimensional
Euclidean squared norm is bounded by `2 * eta⁻¹ ^ 2`.
-/

namespace QubitOracle

open scoped BigOperators

noncomputable section

/-- The pure one-qubit truth used by the canonical local chart. -/
def boundedChartNorthPoleTruth : Fin 3 -> Real :=
  ![0, 0, 1]

/-- The inverse stereographic coordinate at the north-pole truth. -/
def northPoleInverseStereographic (r : Fin 3 -> Real) : Fin 2 -> Real :=
  fun i => r i.castSucc / (1 + r 2)

/-- A globally defined extension of the north-pole inverse chart.

The true inverse chart is used only where its denominator is at least `eta`;
outside this regular neighborhood the output is the zero coordinate. -/
def boundedNorthPoleInverseStereographic
    (eta : Real) (r : Fin 3 -> Real) : Fin 2 -> Real :=
  if eta <= 1 + r 2 then northPoleInverseStereographic r else 0

/-- Squared Euclidean norm in the explicit two-dimensional chart. -/
def finTwoEuclideanNormSq (u : Fin 2 -> Real) : Real :=
  ∑ i, u i ^ 2

@[simp]
theorem blochNormSq_boundedChartNorthPoleTruth :
    blochNormSq boundedChartNorthPoleTruth = 1 := by
  norm_num [blochNormSq, boundedChartNorthPoleTruth, Fin.sum_univ_succ]

@[simp]
theorem northPoleInverseStereographic_northPoleTruth :
    northPoleInverseStereographic boundedChartNorthPoleTruth = 0 := by
  funext i
  fin_cases i <;>
    norm_num [northPoleInverseStereographic, boundedChartNorthPoleTruth]

/-- On the regular neighborhood, the bounded extension is exactly the true
inverse stereographic coordinate. -/
theorem boundedNorthPoleInverseStereographic_eq
    (eta : Real) (r : Fin 3 -> Real)
    (hregular : eta <= 1 + r 2) :
    boundedNorthPoleInverseStereographic eta r =
      northPoleInverseStereographic r := by
  simp [boundedNorthPoleInverseStereographic, hregular]

/-- Outside the regular neighborhood, the bounded extension is zero. -/
theorem boundedNorthPoleInverseStereographic_eq_zero
    (eta : Real) (r : Fin 3 -> Real)
    (hregular : ¬ eta <= 1 + r 2) :
    boundedNorthPoleInverseStereographic eta r = 0 := by
  simp [boundedNorthPoleInverseStereographic, hregular]

/-- Each raw inverse-chart coordinate is measurable whenever the three Bloch
coordinates are measurable. -/
theorem measurable_northPoleInverseStereographic_coordinate
    {Omega : Type*} [MeasurableSpace Omega]
    (r : Omega -> Fin 3 -> Real)
    (hr : ∀ j, Measurable (fun omega => r omega j))
    (i : Fin 2) :
    Measurable (fun omega => northPoleInverseStereographic (r omega) i) := by
  have hone : Measurable (fun _ : Omega => (1 : Real)) := measurable_const
  have hden := hone.add (hr (2 : Fin 3))
  have hdenEq :
      ((fun _ : Omega => (1 : Real)) +
          fun omega => r omega (2 : Fin 3)) =
        fun omega => 1 + r omega (2 : Fin 3) := by
    funext omega
    rfl
  rw [hdenEq] at hden
  have hdiv := (hr i.castSucc).div hden
  have hdivEq :
      ((fun omega => r omega i.castSucc) /
          fun omega => (1 : Real) + r omega (2 : Fin 3)) =
        fun omega => r omega i.castSucc / (1 + r omega (2 : Fin 3)) := by
    funext omega
    rfl
  rw [hdivEq] at hdiv
  simpa only [northPoleInverseStereographic] using hdiv

/-- Each safeguarded coordinate is measurable.  This is the coordinatewise
measurability needed for a `Fin 2`-valued estimator. -/
theorem measurable_boundedNorthPoleInverseStereographic_coordinate
    {Omega : Type*} [MeasurableSpace Omega]
    (eta : Real) (r : Omega -> Fin 3 -> Real)
    (hr : ∀ j, Measurable (fun omega => r omega j))
    (i : Fin 2) :
    Measurable
      (fun omega => boundedNorthPoleInverseStereographic eta (r omega) i) := by
  have hnum : Measurable (fun omega => r omega i.castSucc) := hr i.castSucc
  have hthird : Measurable (fun omega => r omega (2 : Fin 3)) := hr 2
  have hone : Measurable (fun _ : Omega => (1 : Real)) := measurable_const
  have hden := hone.add hthird
  have hdenEq :
      ((fun _ : Omega => (1 : Real)) +
          fun omega => r omega (2 : Fin 3)) =
        fun omega => 1 + r omega (2 : Fin 3) := by
    funext omega
    rfl
  rw [hdenEq] at hden
  have hdiv := hnum.div hden
  have hdivEq :
      ((fun omega => r omega i.castSucc) /
          fun omega => (1 : Real) + r omega (2 : Fin 3)) =
        fun omega => r omega i.castSucc / (1 + r omega (2 : Fin 3)) := by
    funext omega
    rfl
  rw [hdivEq] at hdiv
  have hs : MeasurableSet
      {omega | eta <= 1 + r omega (2 : Fin 3)} :=
    measurableSet_le measurable_const hden
  simpa only [boundedNorthPoleInverseStereographic,
    northPoleInverseStereographic, ite_apply, Pi.zero_apply] using
    Measurable.ite hs hdiv measurable_const

/-- Every coordinate of a Bloch vector in the closed unit ball has absolute
value at most one. -/
theorem abs_blochCoordinate_le_one_of_normSq_le_one
    (r : Fin 3 -> Real) (hball : blochNormSq r <= 1) (j : Fin 3) :
    |r j| <= 1 := by
  have hcoordinate : r j ^ 2 <= blochNormSq r := by
    unfold blochNormSq
    exact Finset.single_le_sum
      (fun k _ => sq_nonneg (r k)) (Finset.mem_univ j)
  have hsquare : r j ^ 2 <= 1 := hcoordinate.trans hball
  apply (sq_le_sq₀ (abs_nonneg (r j)) (by norm_num : (0 : Real) <= 1)).1
  simpa only [sq_abs, one_pow] using hsquare

/-- On a regular Bloch-ball neighborhood, each raw inverse-chart coordinate
has the explicit bound `eta⁻¹`. -/
theorem abs_northPoleInverseStereographic_coordinate_le
    (eta : Real) (r : Fin 3 -> Real)
    (heta : 0 < eta) (hregular : eta <= 1 + r 2)
    (hball : blochNormSq r <= 1) (i : Fin 2) :
    |northPoleInverseStereographic r i| <= eta⁻¹ := by
  have hdenominator : 0 < 1 + r 2 := lt_of_lt_of_le heta hregular
  have hcoordinate : |r i.castSucc| <= 1 :=
    abs_blochCoordinate_le_one_of_normSq_le_one r hball i.castSucc
  change |r i.castSucc / (1 + r 2)| <= eta⁻¹
  rw [abs_div, abs_of_pos hdenominator, div_eq_mul_inv]
  calc
    |r i.castSucc| * (1 + r 2)⁻¹ <= 1 * (1 + r 2)⁻¹ :=
      mul_le_mul_of_nonneg_right hcoordinate
        (inv_nonneg.mpr hdenominator.le)
    _ = (1 + r 2)⁻¹ := one_mul _
    _ <= eta⁻¹ := by
      simpa only [one_div] using
        one_div_le_one_div_of_le heta hregular

/-- The same coordinate bound for the measurable bounded extension. -/
theorem abs_boundedNorthPoleInverseStereographic_coordinate_le
    (eta : Real) (r : Fin 3 -> Real)
    (heta : 0 < eta) (hregular : eta <= 1 + r 2)
    (hball : blochNormSq r <= 1) (i : Fin 2) :
    |boundedNorthPoleInverseStereographic eta r i| <= eta⁻¹ := by
  rw [boundedNorthPoleInverseStereographic_eq eta r hregular]
  exact abs_northPoleInverseStereographic_coordinate_le
    eta r heta hregular hball i

/-- Explicit Euclidean squared-norm bound for the raw two-coordinate chart. -/
theorem finTwoEuclideanNormSq_northPoleInverseStereographic_le
    (eta : Real) (r : Fin 3 -> Real)
    (heta : 0 < eta) (hregular : eta <= 1 + r 2)
    (hball : blochNormSq r <= 1) :
    finTwoEuclideanNormSq (northPoleInverseStereographic r) <=
      2 * eta⁻¹ ^ 2 := by
  have hinverse : 0 <= eta⁻¹ := inv_nonneg.mpr heta.le
  have hzero := abs_northPoleInverseStereographic_coordinate_le
    eta r heta hregular hball (0 : Fin 2)
  have hone := abs_northPoleInverseStereographic_coordinate_le
    eta r heta hregular hball (1 : Fin 2)
  have hzeroSquare :
      northPoleInverseStereographic r 0 ^ 2 <= eta⁻¹ ^ 2 := by
    have hsquare :=
      (sq_le_sq₀
        (abs_nonneg (northPoleInverseStereographic r 0)) hinverse).2 hzero
    simpa only [sq_abs] using hsquare
  have honeSquare :
      northPoleInverseStereographic r 1 ^ 2 <= eta⁻¹ ^ 2 := by
    have hsquare :=
      (sq_le_sq₀
        (abs_nonneg (northPoleInverseStereographic r 1)) hinverse).2 hone
    simpa only [sq_abs] using hsquare
  calc
    finTwoEuclideanNormSq (northPoleInverseStereographic r) =
        northPoleInverseStereographic r 0 ^ 2 +
          northPoleInverseStereographic r 1 ^ 2 := by
      simp [finTwoEuclideanNormSq, Fin.sum_univ_succ]
    _ <= eta⁻¹ ^ 2 + eta⁻¹ ^ 2 := add_le_add hzeroSquare honeSquare
    _ = 2 * eta⁻¹ ^ 2 := by ring

/-- Explicit Euclidean squared-norm bound for the measurable bounded
extension on its regular neighborhood. -/
theorem finTwoEuclideanNormSq_boundedNorthPoleInverseStereographic_le
    (eta : Real) (r : Fin 3 -> Real)
    (heta : 0 < eta) (hregular : eta <= 1 + r 2)
    (hball : blochNormSq r <= 1) :
    finTwoEuclideanNormSq
        (boundedNorthPoleInverseStereographic eta r) <=
      2 * eta⁻¹ ^ 2 := by
  rw [boundedNorthPoleInverseStereographic_eq eta r hregular]
  exact finTwoEuclideanNormSq_northPoleInverseStereographic_le
    eta r heta hregular hball

end

end QubitOracle
