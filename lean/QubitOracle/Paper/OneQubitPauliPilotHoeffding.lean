import QubitOracle.Paper.OneQubitPauliPilotEstimator
import QubitOracle.Paper.OneQubitHoeffdingTheorem2Contract

/-!
# Hoeffding concentration for the explicit Pauli pilot

This file turns the exact Hoeffding Theorem 2 contract into the two-sided
coordinate tail bound for the three-Pauli least-squares pilot.  Probability
normalization, independence, and the Born mean are exposed explicitly for the
next finite-product-law module to prove.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace QubitOracle.Paper

noncomputable section

local instance pauliPilotPathMeasurableSpace (q : ℕ) :
    MeasurableSpace (PauliPilotPath q) := ⊤

def pauliPilotCoordinateVariable
    {q : ℕ} (j : Fin 3) (b : Fin q) (path : PauliPilotPath q) : ℝ :=
  pauliOutcomeSign (path b j)

def pauliPilotNegativeCoordinateVariable
    {q : ℕ} (j : Fin 3) (b : Fin q) (path : PauliPilotPath q) : ℝ :=
  -pauliOutcomeSign (path b j)

theorem finiteIndependentRealFamily_neg
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (X : Fin n → Ω → ℝ)
    (hIndependent : FiniteIndependentRealFamily μ X) :
    FiniteIndependentRealFamily μ (fun i ω => -X i ω) := by
  intro events hEvents
  let reflected : Fin n → Set ℝ := fun i => {x | -x ∈ events i}
  have hReflected : ∀ i, MeasurableSet (reflected i) := by
    intro i
    exact continuous_neg.measurable (hEvents i)
  have hFactor := hIndependent reflected hReflected
  have hpreimage (i : Fin n) :
      (fun ω => -X i ω) ⁻¹' events i = X i ⁻¹' reflected i := by
    ext ω
    rfl
  simpa only [hpreimage] using hFactor

def pauliPilotPositiveHoeffdingData
    {q : ℕ} (hq : 0 < q) (μ : Measure (PauliPilotPath q))
    (j : Fin 3)
    (hProbability : μ univ = 1)
    (hIndependent : FiniteIndependentRealFamily μ
      (pauliPilotCoordinateVariable j)) :
    HoeffdingTheorem2Data (Ω := PauliPilotPath q) q where
  μ := μ
  X := pauliPilotCoordinateVariable j
  lower := fun _ => -1
  upper := fun _ => 1
  nonemptyFamily := hq
  probabilityMeasure := hProbability
  measurableVariable := fun _ => Measurable.of_discrete
  integrableVariable := fun _ => by
    letI : IsProbabilityMeasure μ := ⟨hProbability⟩
    exact Integrable.of_finite
  independent := hIndependent
  orderedBounds := fun _ => by norm_num
  boundedAlmostEverywhere := fun i =>
    Filter.Eventually.of_forall (fun path => by
      cases h : path i j <;>
        norm_num [pauliPilotCoordinateVariable, pauliOutcomeSign, h])

def pauliPilotNegativeHoeffdingData
    {q : ℕ} (hq : 0 < q) (μ : Measure (PauliPilotPath q))
    (j : Fin 3)
    (hProbability : μ univ = 1)
    (hIndependent : FiniteIndependentRealFamily μ
      (pauliPilotCoordinateVariable j)) :
    HoeffdingTheorem2Data (Ω := PauliPilotPath q) q where
  μ := μ
  X := pauliPilotNegativeCoordinateVariable j
  lower := fun _ => -1
  upper := fun _ => 1
  nonemptyFamily := hq
  probabilityMeasure := hProbability
  measurableVariable := fun _ => Measurable.of_discrete
  integrableVariable := fun _ => by
    letI : IsProbabilityMeasure μ := ⟨hProbability⟩
    exact Integrable.of_finite
  independent := by
    exact finiteIndependentRealFamily_neg μ
      (pauliPilotCoordinateVariable j) hIndependent
  orderedBounds := fun _ => by norm_num
  boundedAlmostEverywhere := fun i =>
    Filter.Eventually.of_forall (fun path => by
      cases h : path i j <;>
        norm_num [pauliPilotNegativeCoordinateVariable, pauliOutcomeSign, h])

theorem hoeffdingMeanAverage_pauliPilotCoordinate
    {q : ℕ} (hq : 0 < q) (μ : Measure (PauliPilotPath q))
    (theta : RLSVector 3) (j : Fin 3)
    (hBornMean : ∀ b : Fin q,
      (∫ path, pauliPilotCoordinateVariable j b path ∂μ) = theta j) :
    hoeffdingMeanAverage μ (pauliPilotCoordinateVariable j) = theta j := by
  unfold hoeffdingMeanAverage
  simp_rw [hBornMean]
  have hqReal : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  simp [hqReal]

theorem hoeffdingMeanAverage_pauliPilotNegativeCoordinate
    {q : ℕ} (hq : 0 < q) (μ : Measure (PauliPilotPath q))
    (theta : RLSVector 3) (j : Fin 3)
    (hBornMean : ∀ b : Fin q,
      (∫ path, pauliPilotCoordinateVariable j b path ∂μ) = theta j) :
    hoeffdingMeanAverage μ (pauliPilotNegativeCoordinateVariable j) =
      -theta j := by
  unfold hoeffdingMeanAverage
  have hNegativeMean (b : Fin q) :
      (∫ path, pauliPilotNegativeCoordinateVariable j b path ∂μ) = -theta j := by
    unfold pauliPilotNegativeCoordinateVariable
    have hBorn := hBornMean b
    unfold pauliPilotCoordinateVariable at hBorn
    rw [integral_neg, hBorn]
  simp_rw [hNegativeMean]
  have hqReal : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  simp [hqReal]

theorem hoeffdingSampleAverage_pauliPilotCoordinate
    {q : ℕ} (path : PauliPilotPath q) (j : Fin 3) :
    hoeffdingSampleAverage (pauliPilotCoordinateVariable j) path =
      pauliPilotEstimate path j := by
  rfl

theorem hoeffdingSampleAverage_pauliPilotNegativeCoordinate
    {q : ℕ} (path : PauliPilotPath q) (j : Fin 3) :
    hoeffdingSampleAverage (pauliPilotNegativeCoordinateVariable j) path =
      -pauliPilotEstimate path j := by
  unfold hoeffdingSampleAverage pauliPilotNegativeCoordinateVariable
  unfold pauliPilotEstimate pauliPilotCoordinateSum
  rw [Finset.sum_neg_distrib]
  ring

theorem pauliPilot_upperTail_of_hoeffding2
    {q : ℕ} (hq : 0 < q) (μ : Measure (PauliPilotPath q))
    (theta : RLSVector 3) (j : Fin 3)
    (hProbability : μ univ = 1)
    (hIndependent : FiniteIndependentRealFamily μ
      (pauliPilotCoordinateVariable j))
    (hBornMean : ∀ b : Fin q,
      (∫ path, pauliPilotCoordinateVariable j b path ∂μ) = theta j)
    (hHoeffding : Hoeffding1963Theorem2Contract
      (pauliPilotPositiveHoeffdingData hq μ j hProbability hIndependent))
    (t : ℝ) (ht : 0 < t) :
    μ {path | theta j + t ≤ pauliPilotEstimate path j} ≤
      ENNReal.ofReal (Real.exp (-(q : ℝ) * t ^ 2 / 2)) := by
  have h := hHoeffding t ht
  unfold HoeffdingTheorem2Conclusion at h
  dsimp only [pauliPilotPositiveHoeffdingData] at h
  rw [hoeffdingMeanAverage_pauliPilotCoordinate
        hq μ theta j hBornMean] at h
  simp_rw [hoeffdingSampleAverage_pauliPilotCoordinate] at h
  rw [pauliPilot_hoeffdingExponent q hq t] at h
  exact h

theorem pauliPilot_lowerTail_of_hoeffding2
    {q : ℕ} (hq : 0 < q) (μ : Measure (PauliPilotPath q))
    (theta : RLSVector 3) (j : Fin 3)
    (hProbability : μ univ = 1)
    (hIndependent : FiniteIndependentRealFamily μ
      (pauliPilotCoordinateVariable j))
    (hBornMean : ∀ b : Fin q,
      (∫ path, pauliPilotCoordinateVariable j b path ∂μ) = theta j)
    (hHoeffding : Hoeffding1963Theorem2Contract
      (pauliPilotNegativeHoeffdingData hq μ j hProbability hIndependent))
    (t : ℝ) (ht : 0 < t) :
    μ {path | pauliPilotEstimate path j ≤ theta j - t} ≤
      ENNReal.ofReal (Real.exp (-(q : ℝ) * t ^ 2 / 2)) := by
  have h := hHoeffding t ht
  unfold HoeffdingTheorem2Conclusion at h
  dsimp only [pauliPilotNegativeHoeffdingData] at h
  rw [hoeffdingMeanAverage_pauliPilotNegativeCoordinate
        hq μ theta j hBornMean] at h
  simp_rw [hoeffdingSampleAverage_pauliPilotNegativeCoordinate] at h
  rw [pauliPilot_hoeffdingExponent q hq t] at h
  have hset :
      {ω : PauliPilotPath q | -theta j + t ≤ -pauliPilotEstimate ω j} =
        {path : PauliPilotPath q |
          pauliPilotEstimate path j ≤ theta j - t} := by
    ext path
    simp only [Set.mem_setOf_eq]
    constructor <;> intro hpath <;> linarith
  rw [hset] at h
  exact h

theorem pauliPilot_twoSidedTail_of_hoeffding2
    {q : ℕ} (hq : 0 < q) (μ : Measure (PauliPilotPath q))
    (theta : RLSVector 3) (j : Fin 3)
    (hProbability : μ univ = 1)
    (hIndependent : FiniteIndependentRealFamily μ
      (pauliPilotCoordinateVariable j))
    (hBornMean : ∀ b : Fin q,
      (∫ path, pauliPilotCoordinateVariable j b path ∂μ) = theta j)
    (hPositive : Hoeffding1963Theorem2Contract
      (pauliPilotPositiveHoeffdingData hq μ j hProbability hIndependent))
    (hNegative : Hoeffding1963Theorem2Contract
      (pauliPilotNegativeHoeffdingData hq μ j hProbability hIndependent))
    (t : ℝ) (ht : 0 < t) :
    μ {path | t ≤ |pauliPilotEstimate path j - theta j|} ≤
      2 * ENNReal.ofReal (Real.exp (-(q : ℝ) * t ^ 2 / 2)) := by
  let upper : Set (PauliPilotPath q) :=
    {path | theta j + t ≤ pauliPilotEstimate path j}
  let lower : Set (PauliPilotPath q) :=
    {path | pauliPilotEstimate path j ≤ theta j - t}
  have hsubset :
      {path | t ≤ |pauliPilotEstimate path j - theta j|} ⊆ upper ∪ lower := by
    intro path hpath
    change t ≤ |pauliPilotEstimate path j - theta j| at hpath
    rw [le_abs] at hpath
    rcases hpath with hpath | hpath
    · exact Or.inl (by dsimp [upper]; linarith)
    · exact Or.inr (by dsimp [lower]; linarith)
  calc
    μ {path | t ≤ |pauliPilotEstimate path j - theta j|} ≤
        μ (upper ∪ lower) := measure_mono hsubset
    _ ≤ μ upper + μ lower := measure_union_le upper lower
    _ ≤ ENNReal.ofReal (Real.exp (-(q : ℝ) * t ^ 2 / 2)) +
          ENNReal.ofReal (Real.exp (-(q : ℝ) * t ^ 2 / 2)) :=
      add_le_add
        (pauliPilot_upperTail_of_hoeffding2 hq μ theta j hProbability
          hIndependent hBornMean hPositive t ht)
        (pauliPilot_lowerTail_of_hoeffding2 hq μ theta j hProbability
          hIndependent hBornMean hNegative t ht)
    _ = 2 * ENNReal.ofReal (Real.exp (-(q : ℝ) * t ^ 2 / 2)) := by
      ring

end

end QubitOracle.Paper
