import QubitOracle.Paper.OneQubitDirectionalRegularity

/-!
# Orthogonal transport of one-qubit directional regularity

For a unit Bloch truth `r`, this file gives a concrete orthogonal map sending
`r` to the canonical north pole.  When `r` is already the north pole the map
is the identity.  Otherwise it is the Householder reflection with normal
`r - e₃`:

`Hᵣ x = x - 2 ((r-e₃)·x / ||r-e₃||²) (r-e₃)`.

The reflection preserves Bloch dot products and norms, is involutive, sends
the truth to the north pole, and transports a unit tangent measurement axis
to a unit north-pole tangent axis.  The arbitrary-truth local chart is defined
concretely by reflecting the clean north-pole stereographic chart back to the
original coordinates.  Born probabilities and all directional regularity
constants are therefore unchanged.

No identification with a separately chosen moving frame or manuscript chart
is asserted.  The reflected chart itself is the exact algebraic chart used by
this reduction.
-/

namespace QubitOracle.Paper

open Finset
open scoped BigOperators

noncomputable section

/-! ## Elementary finite-three-dimensional dot algebra -/

theorem blochDot_directional_comm
    (x z : Fin 3 → Real) :
    blochDot x z = blochDot z x := by
  simp [blochDot, Fin.sum_univ_succ]
  ring

theorem blochDot_directional_self
    (x : Fin 3 → Real) :
    blochDot x x = blochNormSq x := by
  simp [blochDot, blochNormSq, Fin.sum_univ_succ]
  ring

theorem blochDot_sub_scaled
    (x z v : Fin 3 → Real) (a b : Real) :
    blochDot (fun j => x j - a * v j)
        (fun j => z j - b * v j) =
      blochDot x z - b * blochDot x v -
        a * blochDot v z + a * b * blochNormSq v := by
  simp [blochDot, blochNormSq, Fin.sum_univ_succ]
  ring

theorem blochDot_right_sub_scaled
    (v x : Fin 3 → Real) (a : Real) :
    blochDot v (fun j => x j - a * v j) =
      blochDot v x - a * blochNormSq v := by
  simp [blochDot, blochNormSq, Fin.sum_univ_succ]
  ring

/-! ## The concrete Householder map -/

def qubitHouseholderVector
    (r : Fin 3 → Real) : Fin 3 → Real :=
  fun j => r j - directionalNorthPole j

theorem qubitHouseholderVector_normSq_nonnegative
    (r : Fin 3 → Real) :
    0 ≤ blochNormSq (qubitHouseholderVector r) := by
  unfold blochNormSq
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem qubitHouseholderVector_normSq_pos
    (r : Fin 3 → Real)
    (hDifferent : r ≠ directionalNorthPole) :
    0 < blochNormSq (qubitHouseholderVector r) := by
  have hNonnegative := qubitHouseholderVector_normSq_nonnegative r
  have hNonzero : blochNormSq (qubitHouseholderVector r) ≠ 0 := by
    intro hZero
    have hExpanded :
        r 0 ^ 2 + r 1 ^ 2 + (r 2 - 1) ^ 2 = 0 := by
      convert hZero using 1 <;>
        simp [blochNormSq, qubitHouseholderVector,
          directionalNorthPole, Fin.sum_univ_succ] <;> ring
    have h0 : r 0 = 0 := by
      nlinarith [sq_nonneg (r 0), sq_nonneg (r 1),
        sq_nonneg (r 2 - 1)]
    have h1 : r 1 = 0 := by
      nlinarith [sq_nonneg (r 0), sq_nonneg (r 1),
        sq_nonneg (r 2 - 1)]
    have h2 : r 2 = 1 := by
      nlinarith [sq_nonneg (r 0), sq_nonneg (r 1),
        sq_nonneg (r 2 - 1)]
    apply hDifferent
    funext j
    fin_cases j <;>
      simp [directionalNorthPole, h0, h1, h2]
  exact lt_of_le_of_ne hNonnegative (Ne.symm hNonzero)

theorem qubitHouseholderVector_normSq_ne
    (r : Fin 3 → Real)
    (hDifferent : r ≠ directionalNorthPole) :
    blochNormSq (qubitHouseholderVector r) ≠ 0 :=
  (qubitHouseholderVector_normSq_pos r hDifferent).ne'

/-- Identity at the north pole, and otherwise the reflection across the
hyperplane orthogonal to `r - e₃`. -/
def qubitHouseholderToNorth
    (r x : Fin 3 → Real) : Fin 3 → Real :=
  if hNorth : r = directionalNorthPole then x
  else
    fun j =>
      x j -
        2 * (blochDot (qubitHouseholderVector r) x /
          blochNormSq (qubitHouseholderVector r)) *
          qubitHouseholderVector r j

@[simp]
theorem qubitHouseholderToNorth_at_northPole
    (x : Fin 3 → Real) :
    qubitHouseholderToNorth directionalNorthPole x = x := by
  simp [qubitHouseholderToNorth]

/-- The Householder map preserves every Bloch inner product. -/
theorem qubitHouseholderToNorth_dot_preserved
    (r x z : Fin 3 → Real) :
    blochDot (qubitHouseholderToNorth r x)
        (qubitHouseholderToNorth r z) = blochDot x z := by
  classical
  by_cases hNorth : r = directionalNorthPole
  · simp [qubitHouseholderToNorth, hNorth]
  · have hDenominator :=
      qubitHouseholderVector_normSq_ne r hNorth
    simp only [qubitHouseholderToNorth, dif_neg hNorth]
    rw [blochDot_sub_scaled]
    rw [blochDot_directional_comm x (qubitHouseholderVector r)]
    field_simp [hDenominator]
    ring

/-- Consequently the squared Bloch norm is preserved. -/
theorem qubitHouseholderToNorth_normSq_preserved
    (r x : Fin 3 → Real) :
    blochNormSq (qubitHouseholderToNorth r x) = blochNormSq x := by
  rw [← blochDot_directional_self,
    qubitHouseholderToNorth_dot_preserved,
    blochDot_directional_self]

/-- Dotting the reflection normal with a reflected vector changes sign. -/
theorem qubitHouseholderVector_dot_image
    (r x : Fin 3 → Real) :
    blochDot (qubitHouseholderVector r)
        (qubitHouseholderToNorth r x) =
      -blochDot (qubitHouseholderVector r) x := by
  classical
  by_cases hNorth : r = directionalNorthPole
  · subst r
    simp [qubitHouseholderToNorth, qubitHouseholderVector,
      directionalNorthPole, blochDot, Fin.sum_univ_succ]
  · have hDenominator :=
      qubitHouseholderVector_normSq_ne r hNorth
    simp only [qubitHouseholderToNorth, dif_neg hNorth]
    rw [blochDot_right_sub_scaled]
    field_simp [hDenominator]
    ring

/-- The concrete reflection is its own inverse. -/
theorem qubitHouseholderToNorth_involutive
    (r x : Fin 3 → Real) :
    qubitHouseholderToNorth r (qubitHouseholderToNorth r x) = x := by
  classical
  by_cases hNorth : r = directionalNorthPole
  · simp [qubitHouseholderToNorth, hNorth]
  · funext j
    have hDot := qubitHouseholderVector_dot_image r x
    simp only [qubitHouseholderToNorth, dif_neg hNorth] at hDot ⊢
    rw [hDot]
    ring

/-! ## Sending a unit truth to the north pole -/

theorem qubitHouseholderVector_dot_truth
    (r : Fin 3 → Real)
    (hUnit : blochNormSq r = 1) :
    blochDot (qubitHouseholderVector r) r = 1 - r 2 := by
  have hExpanded := hUnit
  simp [blochNormSq, Fin.sum_univ_succ] at hExpanded
  simp [blochDot, qubitHouseholderVector,
    directionalNorthPole, Fin.sum_univ_succ]
  nlinarith

theorem qubitHouseholderVector_normSq_eq
    (r : Fin 3 → Real)
    (hUnit : blochNormSq r = 1) :
    blochNormSq (qubitHouseholderVector r) = 2 * (1 - r 2) := by
  have hExpanded := hUnit
  simp [blochNormSq, Fin.sum_univ_succ] at hExpanded
  simp [blochNormSq, qubitHouseholderVector,
    directionalNorthPole, Fin.sum_univ_succ]
  nlinarith

theorem qubitHouseholder_truth_coefficient_eq_one
    (r : Fin 3 → Real)
    (hUnit : blochNormSq r = 1)
    (hDifferent : r ≠ directionalNorthPole) :
    2 * (blochDot (qubitHouseholderVector r) r /
      blochNormSq (qubitHouseholderVector r)) = 1 := by
  have hDenominator := qubitHouseholderVector_normSq_ne r hDifferent
  rw [qubitHouseholderVector_dot_truth r hUnit,
    qubitHouseholderVector_normSq_eq r hUnit]
  have hGap : 1 - r 2 ≠ 0 := by
    intro hZero
    apply hDenominator
    rw [qubitHouseholderVector_normSq_eq r hUnit, hZero]
    norm_num
  field_simp [hGap]

/-- Every unit Bloch truth is sent exactly to the north pole. -/
theorem qubitHouseholderToNorth_maps_truth
    (r : Fin 3 → Real)
    (hUnit : blochNormSq r = 1) :
    qubitHouseholderToNorth r r = directionalNorthPole := by
  classical
  by_cases hNorth : r = directionalNorthPole
  · simpa [hNorth, qubitHouseholderToNorth]
  · have hCoefficient :=
      qubitHouseholder_truth_coefficient_eq_one r hUnit hNorth
    funext j
    simp only [qubitHouseholderToNorth, dif_neg hNorth]
    rw [hCoefficient]
    simp [qubitHouseholderVector]

/-- By involutivity, the same map sends the north pole back to the truth. -/
theorem qubitHouseholderToNorth_maps_northPole
    (r : Fin 3 → Real)
    (hUnit : blochNormSq r = 1) :
    qubitHouseholderToNorth r directionalNorthPole = r := by
  calc
    qubitHouseholderToNorth r directionalNorthPole =
        qubitHouseholderToNorth r (qubitHouseholderToNorth r r) := by
      rw [qubitHouseholderToNorth_maps_truth r hUnit]
    _ = r := qubitHouseholderToNorth_involutive r r

/-! ## Transport of tangent measurement axes and Born probabilities -/

theorem qubitHouseholder_transportedAxis_unit
    (r axis : Fin 3 → Real)
    (hAxis : blochNormSq axis = 1) :
    blochNormSq (qubitHouseholderToNorth r axis) = 1 := by
  rw [qubitHouseholderToNorth_normSq_preserved, hAxis]

theorem qubitHouseholder_transportedAxis_tangent
    (r axis : Fin 3 → Real)
    (hTruthUnit : blochNormSq r = 1)
    (hTangent : blochDot axis r = 0) :
    blochDot (qubitHouseholderToNorth r axis)
        directionalNorthPole = 0 := by
  calc
    blochDot (qubitHouseholderToNorth r axis)
        directionalNorthPole =
      blochDot (qubitHouseholderToNorth r axis)
        (qubitHouseholderToNorth r r) := by
      rw [qubitHouseholderToNorth_maps_truth r hTruthUnit]
    _ = blochDot axis r :=
      qubitHouseholderToNorth_dot_preserved r axis r
    _ = 0 := hTangent

theorem qubitHouseholder_transportedAxis_coordinate_two
    (r axis : Fin 3 → Real)
    (hTruthUnit : blochNormSq r = 1)
    (hTangent : blochDot axis r = 0) :
    qubitHouseholderToNorth r axis 2 = 0 := by
  have h := qubitHouseholder_transportedAxis_tangent
    r axis hTruthUnit hTangent
  simpa using h

/-- Born probabilities are invariant when both the state and measurement
axis are reflected. -/
theorem qubitHouseholder_BornProbability_invariant
    (r theta axis : Fin 3 → Real) (y : QubitRLSOutcome) :
    qubitRLSBornProbability theta axis y =
      qubitRLSBornProbability
        (qubitHouseholderToNorth r theta)
        (qubitHouseholderToNorth r axis) y := by
  unfold qubitRLSBornProbability
  rw [qubitBornTrace_eq, qubitBornTrace_eq]
  rw [qubitHouseholderToNorth_dot_preserved]

theorem qubitHouseholder_truth_BornProbability_invariant
    (r axis : Fin 3 → Real) (y : QubitRLSOutcome)
    (hTruthUnit : blochNormSq r = 1) :
    qubitRLSBornProbability r axis y =
      qubitRLSBornProbability directionalNorthPole
        (qubitHouseholderToNorth r axis) y := by
  calc
    qubitRLSBornProbability r axis y =
        qubitRLSBornProbability
          (qubitHouseholderToNorth r r)
          (qubitHouseholderToNorth r axis) y :=
      qubitHouseholder_BornProbability_invariant r r axis y
    _ = qubitRLSBornProbability directionalNorthPole
        (qubitHouseholderToNorth r axis) y := by
      rw [qubitHouseholderToNorth_maps_truth r hTruthUnit]

/-! ## The reflected arbitrary-truth chart -/

/-- Concrete local chart through an arbitrary unit truth: reflect the clean
north-pole stereographic line back with the same involution. -/
def qubitRotatedDirectionalChart
    (r : Fin 3 → Real) (h : Fin 2 → Real) (t : Real) : Fin 3 → Real :=
  qubitHouseholderToNorth r
    (directionalNorthPoleStereographicLine h t)

theorem qubitRotatedDirectionalChart_at_zero
    (r : Fin 3 → Real) (h : Fin 2 → Real)
    (hTruthUnit : blochNormSq r = 1) :
    qubitRotatedDirectionalChart r h 0 = r := by
  have hLineZero :
      directionalNorthPoleStereographicLine h 0 =
        directionalNorthPole := by
    funext j
    fin_cases j <;>
      simp [directionalNorthPoleStereographicLine,
        directionalLineDenominator, directionalNorthPole]
  rw [qubitRotatedDirectionalChart, hLineZero,
    qubitHouseholderToNorth_maps_northPole r hTruthUnit]

theorem qubitRotatedDirectionalChart_normSq
    (r : Fin 3 → Real) (h : Fin 2 → Real) (t : Real) :
    blochNormSq (qubitRotatedDirectionalChart r h t) = 1 := by
  rw [qubitRotatedDirectionalChart,
    qubitHouseholderToNorth_normSq_preserved,
    directionalStereographicLine_normSq]

/-- Exact Born transport from the arbitrary-truth chart to the north-pole
chart with the transported measurement axis. -/
theorem qubitRotatedDirectionalChart_BornProbability
    (r axis : Fin 3 → Real) (h : Fin 2 → Real)
    (y : QubitRLSOutcome) (t : Real) :
    qubitRLSBornProbability
        (qubitRotatedDirectionalChart r h t) axis y =
      qubitRLSBornProbability
        (directionalNorthPoleStereographicLine h t)
        (qubitHouseholderToNorth r axis) y := by
  calc
    qubitRLSBornProbability
        (qubitRotatedDirectionalChart r h t) axis y =
      qubitRLSBornProbability
        (qubitHouseholderToNorth r
          (qubitRotatedDirectionalChart r h t))
        (qubitHouseholderToNorth r axis) y :=
      qubitHouseholder_BornProbability_invariant
        r (qubitRotatedDirectionalChart r h t) axis y
    _ = qubitRLSBornProbability
        (directionalNorthPoleStereographicLine h t)
        (qubitHouseholderToNorth r axis) y := by
      rw [qubitRotatedDirectionalChart,
        qubitHouseholderToNorth_involutive]

/-! ## Transported log likelihood and regularity certificate -/

def qubitRotatedRationalLogLikelihood
    (r axis : Fin 3 → Real) (h : Fin 2 → Real)
    (y : QubitRLSOutcome) : Real → Real :=
  directionalRationalLogLikelihood
    (qubitHouseholderToNorth r axis) h y

def qubitRotatedRationalLogLikelihoodD1
    (r axis : Fin 3 → Real) (h : Fin 2 → Real)
    (y : QubitRLSOutcome) : Real → Real :=
  directionalRationalLogLikelihoodD1
    (qubitHouseholderToNorth r axis) h y

def qubitRotatedRationalLogLikelihoodD2
    (r axis : Fin 3 → Real) (h : Fin 2 → Real)
    (y : QubitRLSOutcome) : Real → Real :=
  directionalRationalLogLikelihoodD2
    (qubitHouseholderToNorth r axis) h y

def qubitRotatedRationalLogLikelihoodD3
    (r axis : Fin 3 → Real) (h : Fin 2 → Real)
    (y : QubitRLSOutcome) : Real → Real :=
  directionalRationalLogLikelihoodD3
    (qubitHouseholderToNorth r axis) h y

/-- Honest arbitrary-truth transport package.  The derivative chain and
constants are exactly those of the north-pole certificate after applying the
explicit Householder map. -/
structure OneQubitRotatedDirectionalRegularityCertificate
    (r axis : Fin 3 → Real) (h : Fin 2 → Real)
    (y : QubitRLSOutcome) (t : Real) : Prop where
  truth_transport :
    qubitHouseholderToNorth r r = directionalNorthPole
  chart_at_zero :
    qubitRotatedDirectionalChart r h 0 = r
  chart_is_pure :
    blochNormSq (qubitRotatedDirectionalChart r h t) = 1
  transported_axis_unit :
    blochNormSq (qubitHouseholderToNorth r axis) = 1
  transported_axis_tangent :
    qubitHouseholderToNorth r axis 2 = 0
  born_transport :
    qubitRLSBornProbability
        (qubitRotatedDirectionalChart r h t) axis y =
      qubitRLSBornProbability
        (directionalNorthPoleStereographicLine h t)
        (qubitHouseholderToNorth r axis) y
  born_probability_floor :
    (1 / 4 : Real) ≤
      qubitRLSBornProbability
        (qubitRotatedDirectionalChart r h t) axis y
  log_identification :
    qubitRotatedRationalLogLikelihood r axis h y t =
      Real.log (qubitRLSBornProbability
        (qubitRotatedDirectionalChart r h t) axis y)
  derivative_chain :
    HasDerivAt (qubitRotatedRationalLogLikelihood r axis h y)
        (qubitRotatedRationalLogLikelihoodD1 r axis h y t) t ∧
      HasDerivAt (qubitRotatedRationalLogLikelihoodD1 r axis h y)
        (qubitRotatedRationalLogLikelihoodD2 r axis h y t) t ∧
      HasDerivAt (qubitRotatedRationalLogLikelihoodD2 r axis h y)
        (qubitRotatedRationalLogLikelihoodD3 r axis h y t) t
  first_derivative_bound :
    |qubitRotatedRationalLogLikelihoodD1 r axis h y t| ≤ 10
  second_derivative_bound :
    |qubitRotatedRationalLogLikelihoodD2 r axis h y t| ≤ 80
  third_derivative_bound :
    |qubitRotatedRationalLogLikelihoodD3 r axis h y t| ≤ 1200

theorem oneQubitRotatedDirectionalRegularity_of_safeguard
    (r axis : Fin 3 → Real) (h : Fin 2 → Real)
    (y : QubitRLSOutcome) (t : Real)
    (hTruthUnit : blochNormSq r = 1)
    (hAxisUnit : blochNormSq axis = 1)
    (hAxisTangent : blochDot axis r = 0)
    (hNorm : directionalQubitNormSq h ≤ 1)
    (hTime : |t| ≤ 1)
    (hSafeguard :
      t ^ 2 * directionalQubitNormSq h ≤ (1 / 15 : Real)) :
    OneQubitRotatedDirectionalRegularityCertificate r axis h y t := by
  have hTransportedUnit :=
    qubitHouseholder_transportedAxis_unit r axis hAxisUnit
  have hTransportedTangent :=
    qubitHouseholder_transportedAxis_coordinate_two
      r axis hTruthUnit hAxisTangent
  have hNorthCertificate :=
    oneQubitDirectionalRegularity_of_safeguard
      (qubitHouseholderToNorth r axis) h y t
      hTransportedUnit hTransportedTangent
      hNorm hTime hSafeguard
  have hBornTransport :=
    qubitRotatedDirectionalChart_BornProbability r axis h y t
  refine
    { truth_transport :=
        qubitHouseholderToNorth_maps_truth r hTruthUnit
      chart_at_zero :=
        qubitRotatedDirectionalChart_at_zero r h hTruthUnit
      chart_is_pure := qubitRotatedDirectionalChart_normSq r h t
      transported_axis_unit := hTransportedUnit
      transported_axis_tangent := hTransportedTangent
      born_transport := hBornTransport
      born_probability_floor := ?_
      log_identification := ?_
      derivative_chain := ?_
      first_derivative_bound := ?_
      second_derivative_bound := ?_
      third_derivative_bound := ?_ }
  · rw [hBornTransport]
    exact hNorthCertificate.born_probability_floor
  · unfold qubitRotatedRationalLogLikelihood
    calc
      directionalRationalLogLikelihood
          (qubitHouseholderToNorth r axis) h y t =
        Real.log (qubitRLSBornProbability
          (directionalNorthPoleStereographicLine h t)
          (qubitHouseholderToNorth r axis) y) :=
        hNorthCertificate.log_identification
      _ = Real.log (qubitRLSBornProbability
          (qubitRotatedDirectionalChart r h t) axis y) := by
        rw [hBornTransport]
  · simpa [qubitRotatedRationalLogLikelihood,
      qubitRotatedRationalLogLikelihoodD1,
      qubitRotatedRationalLogLikelihoodD2,
      qubitRotatedRationalLogLikelihoodD3] using
        hNorthCertificate.derivative_chain
  · simpa [qubitRotatedRationalLogLikelihoodD1] using
      hNorthCertificate.first_derivative_bound
  · simpa [qubitRotatedRationalLogLikelihoodD2] using
      hNorthCertificate.second_derivative_bound
  · simpa [qubitRotatedRationalLogLikelihoodD3] using
      hNorthCertificate.third_derivative_bound

namespace Label

/-- Arbitrary-unit-truth Householder transport of the clean one-qubit
directional regularity reduction.  It retains the `_rotation_reduction`
suffix because no equality with an independently chosen manuscript moving
chart is claimed. -/
theorem lem_SI_r1_regularity_qubit_rotation_reduction
    (r axis : Fin 3 → Real) (h : Fin 2 → Real)
    (y : QubitRLSOutcome) (t : Real)
    (hTruthUnit : blochNormSq r = 1)
    (hAxisUnit : blochNormSq axis = 1)
    (hAxisTangent : blochDot axis r = 0)
    (hNorm : directionalQubitNormSq h ≤ 1)
    (hTime : |t| ≤ 1)
    (hSafeguard :
      t ^ 2 * directionalQubitNormSq h ≤ (1 / 15 : Real)) :
    OneQubitRotatedDirectionalRegularityCertificate r axis h y t :=
  oneQubitRotatedDirectionalRegularity_of_safeguard
    r axis h y t hTruthUnit hAxisUnit hAxisTangent
    hNorm hTime hSafeguard

end Label

end

end QubitOracle.Paper
