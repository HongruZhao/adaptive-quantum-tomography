import QubitOracle.Paper.OneQubitPauliPilotBornProductLaw
import QubitOracle.OneQubitInformationConvergenceClosed
import Mathlib.Probability.ProductMeasure

/-!
# Consistency of the deterministic three-Pauli pilot

For every pilot block count `n + 1`, the corresponding finite Born product law
lives on a different finite path space.  This file places all of those laws on
one countable product probability space.  The `n`th estimator reads only the
`n`th coordinate, whose marginal is exactly the finite Born product law.

The only probabilistic input is the paired positive/negative Hoeffding Theorem 2
contract already isolated in `OneQubitPauliPilotBornProductLaw`.  All remaining
steps--marginal transfer, the three-coordinate union bound, and specialization
of the closed mixed/pure information theorems--are internal.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory Set
open scoped ENNReal

local instance pauliPilotConsistencyPathMeasurableSpace (q : ℕ) :
    MeasurableSpace (PauliPilotPath q) := ⊤

/-- One coordinate for every positive number of complete three-Pauli blocks. -/
abbrev PauliPilotConsistencySampleSpace :=
  (n : ℕ) → PauliPilotPath (Nat.succ n)

/-- The countable product of the finite Born laws for `1, 2, ...` pilot blocks. -/
noncomputable def pauliPilotConsistencyMeasure (theta : RLSVector 3) :
    Measure PauliPilotConsistencySampleSpace :=
  Measure.infinitePi (fun n : ℕ =>
    pauliPilotBornProductMeasure (q := Nat.succ n) theta)

/-- At sample index `n`, use the empirical three-Pauli estimate from `n + 1`
complete deterministic Pauli blocks. -/
noncomputable def pauliPilotConsistencyEstimator
    (n : ℕ) (omega : PauliPilotConsistencySampleSpace) : RLSVector 3 :=
  pauliPilotEstimate (omega n)

/-- The exact approved external contracts, one paired Hoeffding contract for
 each block count and each of the three Pauli coordinates. -/
def PauliPilotConsistencyHoeffdingContracts
    (theta : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta) : Prop :=
  ∀ (n : ℕ) (j : Fin 3),
    PauliPilotBornTwoSidedHoeffdingTheorem2Contract
      (q := Nat.succ n) (Nat.zero_lt_succ n) theta hphysical j

private theorem pauliPilotBornProductMeasure_isProbability
    {q : ℕ} (theta : RLSVector 3)
    (hphysical : PauliPilotPhysicalBloch theta) :
    IsProbabilityMeasure (pauliPilotBornProductMeasure (q := q) theta) :=
  ⟨pauliPilotBornProductMeasure_univ theta hphysical⟩

/-- Physicality normalizes every finite marginal, hence also their countable
product. -/
theorem pauliPilotConsistencyMeasure_isProbability
    (theta : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta) :
    IsProbabilityMeasure (pauliPilotConsistencyMeasure theta) := by
  letI : ∀ n : ℕ,
      IsProbabilityMeasure
        (pauliPilotBornProductMeasure (q := Nat.succ n) theta) :=
    fun _ => pauliPilotBornProductMeasure_isProbability theta hphysical
  change IsProbabilityMeasure
    (Measure.infinitePi (fun n : ℕ =>
      pauliPilotBornProductMeasure (q := Nat.succ n) theta))
  infer_instance

/-- The `n`th coordinate marginal of the common probability space is exactly
 the Born product law with `n + 1` complete Pauli blocks. -/
theorem pauliPilotConsistencyMeasure_map_eval
    (theta : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (n : ℕ) :
    (pauliPilotConsistencyMeasure theta).map (Function.eval n) =
      pauliPilotBornProductMeasure (q := Nat.succ n) theta := by
  letI : ∀ k : ℕ,
      IsProbabilityMeasure
        (pauliPilotBornProductMeasure (q := Nat.succ k) theta) :=
    fun _ => pauliPilotBornProductMeasure_isProbability theta hphysical
  simpa only [pauliPilotConsistencyMeasure] using
    (Measure.infinitePi_map_eval
      (μ := fun k : ℕ =>
        pauliPilotBornProductMeasure (q := Nat.succ k) theta) n)

/-- The deterministic two-sided coordinate envelope supplied by the paired
Hoeffding contracts. -/
noncomputable def pauliPilotCoordinateHoeffdingEnvelope
    (n : ℕ) (epsilon : ℝ) : ℝ≥0∞ :=
  2 * ENNReal.ofReal
    (Real.exp (-((Nat.succ n : ℝ) * epsilon ^ 2 / 2)))

/-- Three times the coordinate envelope, used by the explicit `Fin 3` union
bound. -/
noncomputable def pauliPilotFiniteHoeffdingEnvelope
    (n : ℕ) (epsilon : ℝ) : ℝ≥0∞ :=
  3 * pauliPilotCoordinateHoeffdingEnvelope n epsilon

/-- Transfer of the finite-law Hoeffding inequality to the common product
space through its exact coordinate marginal. -/
theorem pauliPilotConsistency_coordinate_tail
    (theta : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (hHoeffding : PauliPilotConsistencyHoeffdingContracts theta hphysical)
    (n : ℕ) (j : Fin 3) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    pauliPilotConsistencyMeasure theta
        {omega |
          epsilon ≤
            |pauliPilotConsistencyEstimator n omega j - theta j|} ≤
      pauliPilotCoordinateHoeffdingEnvelope n epsilon := by
  have hEvent :
      MeasurableSet
        {path : PauliPilotPath (Nat.succ n) |
          epsilon ≤ |pauliPilotEstimate path j - theta j|} := by
    exact MeasurableSet.of_discrete
  calc
    pauliPilotConsistencyMeasure theta
        {omega |
          epsilon ≤
            |pauliPilotConsistencyEstimator n omega j - theta j|} =
      ((pauliPilotConsistencyMeasure theta).map (Function.eval n))
        {path : PauliPilotPath (Nat.succ n) |
          epsilon ≤ |pauliPilotEstimate path j - theta j|} := by
            rw [Measure.map_apply (measurable_pi_apply n) hEvent]
            rfl
    _ = pauliPilotBornProductMeasure (q := Nat.succ n) theta
        {path : PauliPilotPath (Nat.succ n) |
          epsilon ≤ |pauliPilotEstimate path j - theta j|} := by
            rw [pauliPilotConsistencyMeasure_map_eval theta hphysical n]
    _ ≤ 2 * ENNReal.ofReal
        (Real.exp (-((Nat.succ n : ℝ) * epsilon ^ 2 / 2))) :=
      by
        simpa only [neg_div, neg_mul] using
          pauliPilotBorn_twoSidedTail_of_hoeffding2
            (Nat.zero_lt_succ n) theta hphysical j
            (hHoeffding n j) epsilon hepsilon
    _ = pauliPilotCoordinateHoeffdingEnvelope n epsilon := rfl

private theorem pauliPilotSampleSizeReal_tendsto :
    Tendsto (fun n : ℕ => (Nat.succ n : ℝ)) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards
    [(tendsto_atTop.1 tendsto_natCast_atTop_atTop) b] with n hn
  calc
    b ≤ (n : ℝ) := hn
    _ ≤ (Nat.succ n : ℝ) := by
      simp only [Nat.cast_succ]
      linarith

/-- For every positive tolerance, the paired-Hoeffding coordinate envelope
vanishes as the number of complete Pauli blocks diverges. -/
theorem pauliPilotCoordinateHoeffdingEnvelope_tendsto_zero
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    Tendsto (fun n : ℕ =>
      pauliPilotCoordinateHoeffdingEnvelope n epsilon) atTop (nhds 0) := by
  have hsquare : 0 < epsilon ^ 2 := sq_pos_of_pos hepsilon
  have hnegative : -(epsilon ^ 2 / 2) < 0 := by
    nlinarith
  have hscaled :
      Tendsto
        (fun n : ℕ => (Nat.succ n : ℝ) * (-(epsilon ^ 2 / 2)))
        atTop atBot :=
    pauliPilotSampleSizeReal_tendsto.atTop_mul_const_of_neg hnegative
  have hfun :
      (fun n : ℕ => (Nat.succ n : ℝ) * (-(epsilon ^ 2 / 2))) =
        (fun n : ℕ => -((Nat.succ n : ℝ) * epsilon ^ 2 / 2)) := by
    funext n
    ring
  have htoBot :
      Tendsto
        (fun n : ℕ => -((Nat.succ n : ℝ) * epsilon ^ 2 / 2))
        atTop atBot :=
    hfun ▸ hscaled
  have hexp :
      Tendsto
        (fun n : ℕ =>
          Real.exp (-((Nat.succ n : ℝ) * epsilon ^ 2 / 2)))
        atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp htoBot
  have hofReal :
      Tendsto
        (fun n : ℕ => ENNReal.ofReal
          (Real.exp (-((Nat.succ n : ℝ) * epsilon ^ 2 / 2))))
        atTop (nhds 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hexp
  have hmul :
      Tendsto (fun x : ℝ≥0∞ => 2 * x) (nhds 0) (nhds 0) :=
    by
      simpa using
        (ENNReal.continuousAt_const_mul
          (a := (2 : ℝ≥0∞)) (b := (0 : ℝ≥0∞))
          (Or.inl (by norm_num))).tendsto
  simpa only [pauliPilotCoordinateHoeffdingEnvelope, Function.comp_def] using
    hmul.comp hofReal

/-- The explicit three-coordinate union-bound envelope also vanishes. -/
theorem pauliPilotFiniteHoeffdingEnvelope_tendsto_zero
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    Tendsto (fun n : ℕ =>
      pauliPilotFiniteHoeffdingEnvelope n epsilon) atTop (nhds 0) := by
  have hcoordinate :=
    pauliPilotCoordinateHoeffdingEnvelope_tendsto_zero epsilon hepsilon
  have hmul :
      Tendsto (fun x : ℝ≥0∞ => 3 * x) (nhds 0) (nhds 0) :=
    by
      simpa using
        (ENNReal.continuousAt_const_mul
          (a := (3 : ℝ≥0∞)) (b := (0 : ℝ≥0∞))
          (Or.inl (by norm_num))).tendsto
  simpa only [pauliPilotFiniteHoeffdingEnvelope, Function.comp_def] using
    hmul.comp hcoordinate

/-- The common-space pilot converges coordinatewise in probability.  Its only
probabilistic premise is the family of paired Hoeffding contracts. -/
theorem pauliPilotConsistency_coordinatewise_convergesInProbability
    (theta : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (hHoeffding : PauliPilotConsistencyHoeffdingContracts theta hphysical) :
    QubitOracle.BlochCoordinatewiseConvergesInProbability
      (pauliPilotConsistencyMeasure theta)
      pauliPilotConsistencyEstimator theta := by
  intro j epsilon hepsilon
  exact Tendsto.squeeze tendsto_const_nhds
    (pauliPilotCoordinateHoeffdingEnvelope_tendsto_zero epsilon hepsilon)
    (fun _ => bot_le)
    (fun n => pauliPilotConsistency_coordinate_tail
      theta hphysical hHoeffding n j epsilon hepsilon)

/-- Concrete finite-dimensional convergence: the probability that any of the
three coordinates misses by at least `epsilon` tends to zero. -/
def PauliPilotFiniteDimensionalConvergesInProbability
    (theta : RLSVector 3) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    Tendsto
      (fun n : ℕ =>
        pauliPilotConsistencyMeasure theta
          (QubitOracle.coordinateDeltaBadEvent
            pauliPilotConsistencyEstimator theta n epsilon))
      atTop (nhds 0)

/-- Explicit `Fin 3` union bound for the simultaneous coordinate bad event. -/
theorem pauliPilotConsistency_finite_tail
    (theta : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (hHoeffding : PauliPilotConsistencyHoeffdingContracts theta hphysical)
    (n : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    pauliPilotConsistencyMeasure theta
        (QubitOracle.coordinateDeltaBadEvent
          pauliPilotConsistencyEstimator theta n epsilon) ≤
      pauliPilotFiniteHoeffdingEnvelope n epsilon := by
  let E : Fin 3 → Set PauliPilotConsistencySampleSpace := fun j =>
    {omega |
      epsilon ≤ |pauliPilotConsistencyEstimator n omega j - theta j|}
  have hsubset :
      QubitOracle.coordinateDeltaBadEvent
          pauliPilotConsistencyEstimator theta n epsilon ⊆
        E 0 ∪ E 1 ∪ E 2 := by
    intro omega homega
    change ∃ j : Fin 3,
      epsilon ≤ |pauliPilotConsistencyEstimator n omega j - theta j| at homega
    rcases homega with ⟨j, hj⟩
    fin_cases j
    · exact Or.inl (Or.inl (by simpa [E] using hj))
    · exact Or.inl (Or.inr (by simpa [E] using hj))
    · exact Or.inr (by simpa [E] using hj)
  have hUnion :
      pauliPilotConsistencyMeasure theta (E 0 ∪ E 1 ∪ E 2) ≤
        (pauliPilotConsistencyMeasure theta (E 0) +
          pauliPilotConsistencyMeasure theta (E 1)) +
          pauliPilotConsistencyMeasure theta (E 2) := by
    calc
      pauliPilotConsistencyMeasure theta ((E 0 ∪ E 1) ∪ E 2) ≤
          pauliPilotConsistencyMeasure theta (E 0 ∪ E 1) +
            pauliPilotConsistencyMeasure theta (E 2) :=
        measure_union_le _ _
      _ ≤ (pauliPilotConsistencyMeasure theta (E 0) +
            pauliPilotConsistencyMeasure theta (E 1)) +
            pauliPilotConsistencyMeasure theta (E 2) :=
        add_le_add (measure_union_le _ _) le_rfl
  have h0 :
      pauliPilotConsistencyMeasure theta (E 0) ≤
        pauliPilotCoordinateHoeffdingEnvelope n epsilon := by
    simpa [E] using pauliPilotConsistency_coordinate_tail
      theta hphysical hHoeffding n (0 : Fin 3) epsilon hepsilon
  have h1 :
      pauliPilotConsistencyMeasure theta (E 1) ≤
        pauliPilotCoordinateHoeffdingEnvelope n epsilon := by
    simpa [E] using pauliPilotConsistency_coordinate_tail
      theta hphysical hHoeffding n (1 : Fin 3) epsilon hepsilon
  have h2 :
      pauliPilotConsistencyMeasure theta (E 2) ≤
        pauliPilotCoordinateHoeffdingEnvelope n epsilon := by
    simpa [E] using pauliPilotConsistency_coordinate_tail
      theta hphysical hHoeffding n (2 : Fin 3) epsilon hepsilon
  calc
    pauliPilotConsistencyMeasure theta
        (QubitOracle.coordinateDeltaBadEvent
          pauliPilotConsistencyEstimator theta n epsilon) ≤
      pauliPilotConsistencyMeasure theta (E 0 ∪ E 1 ∪ E 2) :=
        measure_mono hsubset
    _ ≤ (pauliPilotConsistencyMeasure theta (E 0) +
          pauliPilotConsistencyMeasure theta (E 1)) +
          pauliPilotConsistencyMeasure theta (E 2) := hUnion
    _ ≤ (pauliPilotCoordinateHoeffdingEnvelope n epsilon +
          pauliPilotCoordinateHoeffdingEnvelope n epsilon) +
          pauliPilotCoordinateHoeffdingEnvelope n epsilon :=
      add_le_add (add_le_add h0 h1) h2
    _ = 3 * pauliPilotCoordinateHoeffdingEnvelope n epsilon := by ring
    _ = pauliPilotFiniteHoeffdingEnvelope n epsilon := rfl

/-- Simultaneous finite-dimensional pilot consistency, obtained from the
explicit three-coordinate union bound. -/
theorem pauliPilotConsistency_finiteDimensional_convergesInProbability
    (theta : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (hHoeffding : PauliPilotConsistencyHoeffdingContracts theta hphysical) :
    PauliPilotFiniteDimensionalConvergesInProbability theta := by
  intro epsilon hepsilon
  exact Tendsto.squeeze tendsto_const_nhds
    (pauliPilotFiniteHoeffdingEnvelope_tendsto_zero epsilon hepsilon)
    (fun _ => bot_le)
    (fun n => pauliPilotConsistency_finite_tail
      theta hphysical hHoeffding n epsilon hepsilon)

/-- A mixed nonzero-interior truth is automatically a physical Bloch vector. -/
theorem mixedNonzeroInterior_pauliPilotPhysical
    (theta : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta) :
    PauliPilotPhysicalBloch theta :=
  hTruth.2.le

/-- Closed mixed-qubit information convergence for the concrete deterministic
three-Pauli pilot.  Beyond the paired Hoeffding contracts, the only premises are
the genuine nonzero-interior truth and nonparallel local-frame seed conditions
of the existing information theorem. -/
theorem pauliPilot_mixedNonzeroInteriorInformation_convergesInProbability
    (theta b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hHoeffding :
      PauliPilotConsistencyHoeffdingContracts theta
        (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)) :
    QubitOracle.MatrixEntrywiseEpsilonConvergesInProbability
      (pauliPilotConsistencyMeasure theta)
      (fun n omega =>
        QubitOracle.mixedLocalSafeguardedPerObservationInformation
          b theta (pauliPilotConsistencyEstimator n omega))
      (QubitOracle.mixedOraclePerObservationInformation theta) := by
  let hphysical := mixedNonzeroInterior_pauliPilotPhysical theta hTruth
  letI : IsProbabilityMeasure (pauliPilotConsistencyMeasure theta) :=
    pauliPilotConsistencyMeasure_isProbability theta hphysical
  exact
    QubitOracle.mixedLocalInformation_entrywise_convergesInProbability_closed
      (μ := pauliPilotConsistencyMeasure theta)
      (b := b) (theta := theta)
      (xHat := pauliPilotConsistencyEstimator)
      (pauliPilotConsistency_coordinatewise_convergesInProbability
        theta hphysical hHoeffding)
      hTruth hSeed

/-- A unit pure-state Bloch vector is physical for the pilot Born law. -/
theorem pureUnit_pauliPilotPhysical
    (r : RLSVector 3) (hTruthUnit : QubitOracle.blochNormSq r = 1) :
    PauliPilotPhysicalBloch r := by
  unfold PauliPilotPhysicalBloch
  simpa [QubitOracle.blochNormSq] using hTruthUnit.le

/-- Direct pure-state specialization of the same concrete pilot to the existing
closed pure information-convergence theorem. -/
theorem pauliPilot_pureInformation_convergesInProbability
    (r b : RLSVector 3)
    (hTruthUnit : QubitOracle.blochNormSq r = 1)
    (hSeed : LocalFrameSeedNonparallelAt b r)
    (hHoeffding :
      PauliPilotConsistencyHoeffdingContracts r
        (pureUnit_pauliPilotPhysical r hTruthUnit)) :
    QubitOracle.MatrixEntrywiseEpsilonConvergesInProbability
      (pauliPilotConsistencyMeasure r)
      (fun n omega =>
        QubitOracle.pureLocalSafeguardedPerObservationInformation
          b r (pauliPilotConsistencyEstimator n omega))
      (QubitOracle.pureOraclePerObservationInformation r) := by
  let hphysical := pureUnit_pauliPilotPhysical r hTruthUnit
  letI : IsProbabilityMeasure (pauliPilotConsistencyMeasure r) :=
    pauliPilotConsistencyMeasure_isProbability r hphysical
  exact
    QubitOracle.pureLocalInformation_entrywise_convergesInProbability_closed
      (μ := pauliPilotConsistencyMeasure r)
      (b := b) (r := r)
      (xHat := pauliPilotConsistencyEstimator)
      (pauliPilotConsistency_coordinatewise_convergesInProbability
        r hphysical hHoeffding)
      hTruthUnit hSeed

end QubitOracle.Paper
