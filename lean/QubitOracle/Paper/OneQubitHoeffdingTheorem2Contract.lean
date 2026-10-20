import Mathlib

/-!
# Hoeffding (1963), Theorem 2, equation (2.6)

This file records the exact finite-family assumptions and one-sided conclusion
of Hoeffding's bounded independent sample-mean inequality.  It is the proposed
single literature boundary for consistency of the deterministic three-Pauli
pilot.  No axiom is declared.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace QubitOracle.Paper

noncomputable section

/-- Independence of a finite real-valued family, stated by factorization on
all measurable rectangles. -/
def FiniteIndependentRealFamily
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (X : Fin n → Ω → ℝ) : Prop :=
  ∀ events : Fin n → Set ℝ,
    (∀ i, MeasurableSet (events i)) →
      μ (⋂ i, X i ⁻¹' events i) =
        ∏ i, μ (X i ⁻¹' events i)

def hoeffdingSampleAverage
    {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (ω : Ω) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, X i ω

def hoeffdingMeanAverage
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (X : Fin n → Ω → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, ∫ ω, X i ω ∂μ

def hoeffdingRangeSquareSum {n : ℕ}
    (lower upper : Fin n → ℝ) : ℝ :=
  ∑ i, (upper i - lower i) ^ 2

/-- All assumptions in Hoeffding's Theorem 2 for a fixed finite family. -/
structure HoeffdingTheorem2Data
    {Ω : Type*} [MeasurableSpace Ω] (n : ℕ) where
  μ : Measure Ω
  X : Fin n → Ω → ℝ
  lower : Fin n → ℝ
  upper : Fin n → ℝ
  nonemptyFamily : 0 < n
  probabilityMeasure : μ univ = 1
  measurableVariable : ∀ i, Measurable (X i)
  integrableVariable : ∀ i, Integrable (X i) μ
  independent : FiniteIndependentRealFamily μ X
  orderedBounds : ∀ i, lower i ≤ upper i
  boundedAlmostEverywhere : ∀ i,
    ∀ᵐ ω ∂μ, lower i ≤ X i ω ∧ X i ω ≤ upper i

/-- The one-sided probability bound in equation (2.6). -/
def HoeffdingTheorem2Conclusion
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (data : HoeffdingTheorem2Data (Ω := Ω) n) (t : ℝ) : Prop :=
  data.μ {ω |
      hoeffdingMeanAverage data.μ data.X + t ≤
        hoeffdingSampleAverage data.X ω} ≤
    ENNReal.ofReal
      (Real.exp
        (-2 * (n : ℝ) ^ 2 * t ^ 2 /
          hoeffdingRangeSquareSum data.lower data.upper))

/-- Proposed literature atom for one fixed data family.  A future approved
axiom would quantify over `data` and assert this proposition. -/
def Hoeffding1963Theorem2Contract
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (data : HoeffdingTheorem2Data (Ω := Ω) n) : Prop :=
  ∀ t : ℝ, 0 < t → HoeffdingTheorem2Conclusion data t

/-- Three-Pauli pilot signs all have interval width two. -/
theorem pauliPilot_hoeffdingRangeSquareSum
    (q : ℕ) :
    hoeffdingRangeSquareSum
        (n := q) (fun _ => (-1 : ℝ)) (fun _ => 1) =
      4 * q := by
  simp [hoeffdingRangeSquareSum]
  ring

/-- Algebraic simplification of the Theorem 2 exponent for `q` variables in
`[-1,1]`. -/
theorem pauliPilot_hoeffdingExponent
    (q : ℕ) (hq : 0 < q) (t : ℝ) :
    -2 * (q : ℝ) ^ 2 * t ^ 2 /
        hoeffdingRangeSquareSum
          (n := q) (fun _ => (-1 : ℝ)) (fun _ => 1) =
      -(q : ℝ) * t ^ 2 / 2 := by
  rw [pauliPilot_hoeffdingRangeSquareSum]
  have hqReal : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  field_simp
  ring

end

end QubitOracle.Paper
