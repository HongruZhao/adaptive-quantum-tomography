import QubitOracle.OneQubitInformationConvergenceInProbability

/-!
# Finite-coordinate continuous mapping in probability

This file discharges `FiniteCoordinateContinuousMappingProbabilityContract`
without an axiom.  Sequential coordinatewise continuity first gives a common
epsilon--delta bound by the standard `1 / (n + 1)` counterexample argument.
The scalar bad event is then contained in the finite union of coordinate bad
events.  Finite subadditivity and a finite sum of `ℝ≥0∞` sequences tending to
zero complete the proof.

No finite-mass assumption is needed: coordinatewise convergence in probability
already supplies convergence to zero for every summand, and only finitely many
summands occur.  Probability measures are recorded as a direct specialization.
-/

open Filter MeasureTheory
open scoped BigOperators ENNReal

namespace QubitOracle

/-! ## Sequential continuity gives a uniform coordinate radius -/

/-- In a finite real coordinate space, the sequential premise in the contract
implies the common-coordinate epsilon--delta condition needed for the event
inclusion. -/
theorem sequentialCoordinatewiseContinuity_epsilonDelta
    {d : ℕ} {x : Fin d → ℝ} {F : (Fin d → ℝ) → ℝ} {y : ℝ}
    (hSequential : ∀ z : ℕ → Fin d → ℝ,
      (∀ k, Tendsto (fun n => z n k) atTop (nhds (x k))) →
        Tendsto (fun n => F (z n)) atTop (nhds y))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ z : Fin d → ℝ,
        (∀ k, |z k - x k| < δ) → |F z - y| < ε := by
  classical
  by_contra hNoRadius
  push_neg at hNoRadius
  let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hδPositive : ∀ n, 0 < δ n := by
    intro n
    dsimp [δ]
    positivity
  have hCounterexample : ∀ n : ℕ, ∃ z : Fin d → ℝ,
      (∀ k, |z k - x k| < δ n) ∧ ε ≤ |F z - y| := by
    intro n
    exact hNoRadius (δ n) (hδPositive n)
  choose z hzClose hzBad using hCounterexample
  have hδTendsto : Tendsto δ atTop (nhds 0) := by
    simpa [δ, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0))
  have hzTendsto : ∀ k : Fin d,
      Tendsto (fun n => z n k) atTop (nhds (x k)) := by
    intro k
    apply Metric.tendsto_atTop.2
    intro η hη
    have hδEventually : ∀ᶠ n in atTop, δ n < η := by
      exact hδTendsto.eventually (Iio_mem_nhds hη)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hδEventually
    refine ⟨N, ?_⟩
    intro n hn
    rw [Real.dist_eq]
    exact lt_trans (hzClose n k) (hN n hn)
  have hOutputTendsto := hSequential z hzTendsto
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hOutputTendsto) ε hε
  have hGood := hN N le_rfl
  rw [Real.dist_eq] at hGood
  exact (not_lt_of_ge (hzBad N)) hGood

/-! ## Finite union and finite ENNReal sum -/

/-- The coordinate bad event has measure at most the finite sum of its
coordinate tail measures. -/
theorem measure_coordinateDeltaBadEvent_le_finset_sum
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (μ : Measure Ω)
    (X : ℕ → Ω → Fin d → ℝ) (x : Fin d → ℝ)
    (n : ℕ) (δ : ℝ) :
    μ (coordinateDeltaBadEvent X x n δ) ≤
      ∑ k : Fin d, μ {ω | δ ≤ |X n ω k - x k|} := by
  rw [show coordinateDeltaBadEvent X x n δ =
      ⋃ k : Fin d, {ω | δ ≤ |X n ω k - x k|} by
    ext ω
    simp [coordinateDeltaBadEvent]]
  calc
    μ (⋃ k : Fin d, {ω | δ ≤ |X n ω k - x k|}) ≤
        ∑' k : Fin d, μ {ω | δ ≤ |X n ω k - x k|} :=
      measure_iUnion_le (fun k : Fin d =>
        {ω | δ ≤ |X n ω k - x k|})
    _ = ∑ k : Fin d, μ {ω | δ ≤ |X n ω k - x k|} := by
      simp

/-- A finite sum of coordinate epsilon-tail probabilities tends to zero. -/
theorem coordinateTailMeasure_finsetSum_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (μ : Measure Ω)
    (X : ℕ → Ω → Fin d → ℝ) (x : Fin d → ℝ)
    (hCoordinate : ∀ k : Fin d,
      EpsilonConvergesInProbability μ (fun n ω => X n ω k) (x k))
    (δ : ℝ) (hδ : 0 < δ) :
    Tendsto
      (fun n => ∑ k : Fin d, μ {ω | δ ≤ |X n ω k - x k|})
      atTop (nhds 0) := by
  have hSum :
      Tendsto
        (fun n => ∑ k : Fin d,
          μ {ω | δ ≤ |X n ω k - x k|})
        atTop (nhds (∑ _k : Fin d, (0 : ℝ≥0∞))) := by
    apply tendsto_finset_sum
    intro k _hk
    exact hCoordinate k δ hδ
  simpa using hSum

/-! ## The contract is proved -/

/-- The finite-coordinate continuous-mapping contract holds for every measure.
In particular, no finite-measure premise needs to be added to the original
contract. -/
theorem finiteCoordinateContinuousMappingProbabilityContract
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) :
    FiniteCoordinateContinuousMappingProbabilityContract μ := by
  intro d X x F y hSequential hCoordinate
  intro ε hε
  obtain ⟨δ, hδ, hControl⟩ :=
    sequentialCoordinatewiseContinuity_epsilonDelta hSequential ε hε
  have hFiniteSum := coordinateTailMeasure_finsetSum_tendsto_zero
    μ X x hCoordinate δ hδ
  have hBound : ∀ n,
      μ {ω | ε ≤ |F (X n ω) - y|} ≤
        ∑ k : Fin d, μ {ω | δ ≤ |X n ω k - x k|} := by
    intro n
    calc
      μ {ω | ε ≤ |F (X n ω) - y|} =
          μ (scalarEpsilonBadEvent X F y n ε) := rfl
      _ ≤ μ (coordinateDeltaBadEvent X x n δ) :=
        measure_scalarEpsilonBadEvent_le_coordinateDeltaBadEvent
          μ X x F y n ε δ hControl
      _ ≤ ∑ k : Fin d, μ {ω | δ ≤ |X n ω k - x k|} :=
        measure_coordinateDeltaBadEvent_le_finset_sum μ X x n δ
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hFiniteSum
    (fun _n => bot_le)
    hBound

/-! ## Probability-law specialization -/

/-- A probability law has finite total mass.  This fact is not needed by the
proof above, but records the requested bridge from a qubit probability law to
the stronger-than-necessary finite-measure condition. -/
theorem probabilityLaw_measure_univ_lt_top
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] : μ Set.univ < ⊤ := by
  simp

/-- Direct specialization of the proved contract to a probability law. -/
theorem finiteCoordinateContinuousMappingProbabilityContract_probabilityLaw
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    FiniteCoordinateContinuousMappingProbabilityContract μ :=
  finiteCoordinateContinuousMappingProbabilityContract μ

namespace Label

/-- Source-facing label: the finite-coordinate continuous-mapping probability
boundary used by the concrete one-qubit information theorem is discharged. -/
theorem lem_SI_finite_coordinate_CMT_qubit_reduction
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    FiniteCoordinateContinuousMappingProbabilityContract μ :=
  finiteCoordinateContinuousMappingProbabilityContract_probabilityLaw μ

end Label
end QubitOracle
