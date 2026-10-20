import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.OneQubitPauliPilotBornProductLaw

/-!
# Finite law for the mixed-qubit two-stage experiment

This module defines one finite triangular row directly.  A row consists of a
complete deterministic Pauli pilot, followed by a finite binary final stage.
The final measurement frame is a function only of the completed pilot path,
and the final axes cycle deterministically through its three orthonormal
columns.

The joint mass is the pilot Born mass multiplied by the pilot-conditional
finite product of final Born probabilities.  Normalization is proved by
successively summing the final product and the pilot product.  No infinite
protocol, LAN statement, or asymptotic construction is used.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace QubitOracle.Paper

noncomputable section

local instance mixedTwoStagePropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Binary final-stage paths of finite horizon `T`. -/
abbrev MixedTwoStageFinalPath (T : ℕ) := Fin T → Bool

/-- One finite triangular row: the Pauli pilot and the subsequent final path. -/
abbrev MixedTwoStageFiniteRow (q T : ℕ) :=
  PauliPilotPath q × MixedTwoStageFinalPath T

local instance mixedTwoStagePilotPathMeasurableSpace (q : ℕ) :
    MeasurableSpace (PauliPilotPath q) := ⊤

local instance mixedTwoStageFrameMeasurableSpace :
    MeasurableSpace (Matrix (Fin 3) (Fin 3) ℝ) := ⊤

local instance mixedTwoStageFiniteRowMeasurableSpace (q T : ℕ) :
    MeasurableSpace (MixedTwoStageFiniteRow q T) := ⊤

local instance mixedTwoStageFiniteRowMeasurableSingletonClass (q T : ℕ) :
    MeasurableSingletonClass (MixedTwoStageFiniteRow q T) where
  measurableSet_singleton _ := MeasurableSet.of_discrete

/-! ## Pilot-selected final frame and deterministic allocation -/

/-- The `k`th column of a real three-dimensional frame. -/
def mixedTwoStageFrameAxis
    (R : Matrix (Fin 3) (Fin 3) ℝ) (k : Fin 3) : Fin 3 → ℝ :=
  fun i => R i k

/-- A final frame selected from the completed pilot.  Unit columns are the
physicality condition needed for the projective Born law; orthogonality records
that the three selected axes form a complete frame. -/
structure PilotSelectedFinalFrame (q : ℕ) where
  frame : PauliPilotPath q → Matrix (Fin 3) (Fin 3) ℝ
  axis_unit : ∀ pilot k,
    QubitOracle.blochNormSq (mixedTwoStageFrameAxis (frame pilot) k) = 1
  axes_orthogonal : ∀ pilot k l,
    QubitOracle.blochDot
        (mixedTwoStageFrameAxis (frame pilot) k)
        (mixedTwoStageFrameAxis (frame pilot) l) =
      if k = l then 1 else 0

/-- Every pilot-selected finite frame is measurable because the pilot path
space carries its finite discrete sigma algebra. -/
theorem PilotSelectedFinalFrame.measurable_frame
    {q : ℕ} (selected : PilotSelectedFinalFrame q) :
    Measurable selected.frame :=
  Measurable.of_discrete

/-- Deterministic cycling index `0,1,2,0,1,2,...`. -/
def mixedTwoStageCycleIndex {T : ℕ} (t : Fin T) : Fin 3 :=
  ⟨t.1 % 3, Nat.mod_lt _ (by norm_num)⟩

/-- At final time `t`, use the corresponding cyclic column of the frame
selected by the completed pilot. -/
def mixedTwoStageFinalAxis
    {q T : ℕ} (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) (t : Fin T) : Fin 3 → ℝ :=
  mixedTwoStageFrameAxis (selected.frame pilot)
    (mixedTwoStageCycleIndex t)

@[simp]
theorem mixedTwoStageFinalAxis_unit
    {q T : ℕ} (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) (t : Fin T) :
    QubitOracle.blochNormSq
      (mixedTwoStageFinalAxis selected pilot t) = 1 :=
  selected.axis_unit pilot (mixedTwoStageCycleIndex t)

/-- The deterministic final-axis allocation is measurable with respect to the
completed pilot. -/
theorem mixedTwoStageFinalAxis_pilotMeasurable
    {q T : ℕ} (selected : PilotSelectedFinalFrame q)
    (t : Fin T) :
    Measurable (fun pilot : PauliPilotPath q =>
      mixedTwoStageFinalAxis selected pilot t) :=
  Measurable.of_discrete

/-- Orthonormality inherited by any two cyclically allocated final axes. -/
theorem mixedTwoStageFinalAxes_dot
    {q T : ℕ} (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) (s t : Fin T) :
    QubitOracle.blochDot
        (mixedTwoStageFinalAxis selected pilot s)
        (mixedTwoStageFinalAxis selected pilot t) =
      if mixedTwoStageCycleIndex s = mixedTwoStageCycleIndex t then 1 else 0 :=
  selected.axes_orthogonal pilot
    (mixedTwoStageCycleIndex s) (mixedTwoStageCycleIndex t)

/-! ## Conditional final Born law -/

/-- Binary projective Born probability at one pilot-selected final axis. -/
def mixedTwoStageFinalBornProbability
    {q T : ℕ} (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) (t : Fin T) (outcome : Bool) : ℝ :=
  if outcome then
    (1 + QubitOracle.blochDot
      (mixedTwoStageFinalAxis selected pilot t) theta) / 2
  else
    (1 - QubitOracle.blochDot
      (mixedTwoStageFinalAxis selected pilot t) theta) / 2

/-- Physical state and unit-axis assumptions make every final Born factor
nonnegative. -/
theorem mixedTwoStageFinalBornProbability_nonnegative
    {q T : ℕ} (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q)
    (hphysical : PauliPilotPhysicalBloch theta)
    (pilot : PauliPilotPath q) (t : Fin T) (outcome : Bool) :
    0 ≤ mixedTwoStageFinalBornProbability
      theta selected pilot t outcome := by
  let axis := mixedTwoStageFinalAxis selected pilot t
  have hCauchy :
      QubitOracle.blochDot axis theta ^ 2 ≤
        QubitOracle.blochNormSq axis * QubitOracle.blochNormSq theta := by
    simpa [QubitOracle.blochDot, QubitOracle.blochNormSq] using
      (Finset.sum_mul_sq_le_sq_mul_sq
        (Finset.univ : Finset (Fin 3)) axis theta)
  have hDotSq : QubitOracle.blochDot axis theta ^ 2 ≤ 1 := by
    calc
      QubitOracle.blochDot axis theta ^ 2 ≤
          QubitOracle.blochNormSq axis * QubitOracle.blochNormSq theta :=
        hCauchy
      _ = QubitOracle.blochNormSq theta := by
        rw [show QubitOracle.blochNormSq axis = 1 by
          exact mixedTwoStageFinalAxis_unit selected pilot t, one_mul]
      _ ≤ 1 := hphysical
  have hLower : -1 ≤ QubitOracle.blochDot axis theta := by
    nlinarith [sq_nonneg (QubitOracle.blochDot axis theta + 1)]
  have hUpper : QubitOracle.blochDot axis theta ≤ 1 := by
    nlinarith [sq_nonneg (QubitOracle.blochDot axis theta - 1)]
  cases outcome <;>
    simp [mixedTwoStageFinalBornProbability, axis] <;> linarith

/-- Each pilot-conditioned one-shot binary Born law is normalized. -/
theorem mixedTwoStageFinalBornProbability_sum_one
    {q T : ℕ} (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) (t : Fin T) :
    (∑ outcome : Bool,
      mixedTwoStageFinalBornProbability theta selected pilot t outcome) = 1 := by
  simp [mixedTwoStageFinalBornProbability]
  ring

/-- Product Born mass of the final path conditional on the completed pilot. -/
def mixedTwoStageConditionalFinalPathMass
    {q T : ℕ} (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q)
    (finalPath : MixedTwoStageFinalPath T) : ℝ :=
  ∏ t : Fin T,
    mixedTwoStageFinalBornProbability theta selected pilot t (finalPath t)

/-- Conditional final-path masses are nonnegative. -/
theorem mixedTwoStageConditionalFinalPathMass_nonnegative
    {q T : ℕ} (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q)
    (hphysical : PauliPilotPhysicalBloch theta)
    (pilot : PauliPilotPath q)
    (finalPath : MixedTwoStageFinalPath T) :
    0 ≤ mixedTwoStageConditionalFinalPathMass
      theta selected pilot finalPath := by
  unfold mixedTwoStageConditionalFinalPathMass
  exact Finset.prod_nonneg fun t _ =>
    mixedTwoStageFinalBornProbability_nonnegative
      theta selected hphysical pilot t (finalPath t)

/-- Iterated finite-product normalization of the final path, including
`T = 0`. -/
theorem mixedTwoStageConditionalFinalPathMass_sum_one
    {q T : ℕ} (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) :
    (∑ finalPath : MixedTwoStageFinalPath T,
      mixedTwoStageConditionalFinalPathMass
        theta selected pilot finalPath) = 1 := by
  unfold mixedTwoStageConditionalFinalPathMass
  rw [← Fintype.prod_sum]
  simp_rw [mixedTwoStageFinalBornProbability_sum_one]
  simp

/-- Real conditional mass assigned to an arbitrary final-path event. -/
def mixedTwoStageConditionalFinalEventMass
    {q T : ℕ} (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q)
    (event : Set (MixedTwoStageFinalPath T)) : ℝ :=
  ∑ finalPath : MixedTwoStageFinalPath T,
    if finalPath ∈ event then
      mixedTwoStageConditionalFinalPathMass
        theta selected pilot finalPath
    else 0

/-- The conditional final event mass of the whole fiber is one. -/
theorem mixedTwoStageConditionalFinalEventMass_univ
    {q T : ℕ} (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) :
    mixedTwoStageConditionalFinalEventMass (T := T)
      theta selected pilot
        (univ : Set (MixedTwoStageFinalPath T)) = 1 := by
  simp [mixedTwoStageConditionalFinalEventMass,
    mixedTwoStageConditionalFinalPathMass_sum_one]

/-! ## Joint finite-row mass -/

/-- Joint two-stage mass: pilot mass times the final mass conditional on that
pilot. -/
def mixedTwoStageFiniteRowMass
    {q T : ℕ} (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q)
    (row : MixedTwoStageFiniteRow q T) : ℝ :=
  pauliPilotPathMass theta row.1 *
    mixedTwoStageConditionalFinalPathMass theta selected row.1 row.2

/-- The joint finite-row mass is nonnegative under physicality. -/
theorem mixedTwoStageFiniteRowMass_nonnegative
    {q T : ℕ} (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q)
    (hphysical : PauliPilotPhysicalBloch theta)
    (row : MixedTwoStageFiniteRow q T) :
    0 ≤ mixedTwoStageFiniteRowMass theta selected row := by
  exact mul_nonneg
    (pauliPilotPathMass_nonnegative theta hphysical row.1)
    (mixedTwoStageConditionalFinalPathMass_nonnegative
      theta selected hphysical row.1 row.2)

/-- Exact conditional final Born factorization of every joint atom. -/
theorem mixedTwoStageFiniteRowMass_conditional_factorization
    {q T : ℕ} (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q)
    (finalPath : MixedTwoStageFinalPath T) :
    mixedTwoStageFiniteRowMass theta selected (pilot, finalPath) =
      pauliPilotPathMass theta pilot *
        ∏ t : Fin T,
          mixedTwoStageFinalBornProbability
            theta selected pilot t (finalPath t) :=
  rfl

/-- On every pilot fiber, joint event mass is the pilot mass times the
pilot-conditional final event mass.  This is the division-free conditional
factorization, valid even when a pilot atom has zero mass. -/
theorem mixedTwoStageFiniteRowMass_pilotFiberEvent_factorization
    {q T : ℕ} (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q)
    (event : Set (MixedTwoStageFinalPath T)) :
    (∑ finalPath : MixedTwoStageFinalPath T,
      if finalPath ∈ event then
        mixedTwoStageFiniteRowMass theta selected (pilot, finalPath)
      else 0) =
      pauliPilotPathMass theta pilot *
        mixedTwoStageConditionalFinalEventMass
          theta selected pilot event := by
  unfold mixedTwoStageConditionalFinalEventMass
  calc
    (∑ finalPath : MixedTwoStageFinalPath T,
      if finalPath ∈ event then
        mixedTwoStageFiniteRowMass theta selected (pilot, finalPath)
      else 0) =
        ∑ finalPath : MixedTwoStageFinalPath T,
          pauliPilotPathMass theta pilot *
            (if finalPath ∈ event then
              mixedTwoStageConditionalFinalPathMass
                theta selected pilot finalPath
            else 0) := by
      apply Finset.sum_congr rfl
      intro finalPath _
      by_cases hfinal : finalPath ∈ event <;>
        simp [hfinal, mixedTwoStageFiniteRowMass]
    _ = pauliPilotPathMass theta pilot *
        ∑ finalPath : MixedTwoStageFinalPath T,
          if finalPath ∈ event then
            mixedTwoStageConditionalFinalPathMass
              theta selected pilot finalPath
          else 0 := by
      rw [Finset.mul_sum]

/-- Summing a joint mass over one complete final fiber returns the exact pilot
mass. -/
theorem mixedTwoStageFiniteRowMass_pilotFiber
    {q T : ℕ} (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) :
    (∑ finalPath : MixedTwoStageFinalPath T,
      mixedTwoStageFiniteRowMass theta selected (pilot, finalPath)) =
      pauliPilotPathMass theta pilot := by
  unfold mixedTwoStageFiniteRowMass
  simp only [Prod.fst, Prod.snd]
  rw [← Finset.mul_sum,
    mixedTwoStageConditionalFinalPathMass_sum_one, mul_one]

/-- Exact real pilot marginal for every pilot event. -/
theorem mixedTwoStageFiniteRowMass_pilotEventMarginal
    {q T : ℕ} (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q)
    (event : Set (PauliPilotPath q)) :
    (∑ row : MixedTwoStageFiniteRow q T,
      if row.1 ∈ event then
        mixedTwoStageFiniteRowMass theta selected row
      else 0) =
      ∑ pilot : PauliPilotPath q,
        if pilot ∈ event then pauliPilotPathMass theta pilot else 0 := by
  classical
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro pilot _
  by_cases hpilot : pilot ∈ event
  · simpa [hpilot] using
      (mixedTwoStageFiniteRowMass_pilotFiber
        (T := T) theta selected pilot)
  · simp [hpilot]

/-- Total joint mass is one by first normalizing each conditional final fiber
and then the Pauli pilot product. -/
theorem mixedTwoStageFiniteRowMass_sum_one
    {q T : ℕ} (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q) :
    (∑ row : MixedTwoStageFiniteRow q T,
      mixedTwoStageFiniteRowMass theta selected row) = 1 := by
  calc
    (∑ row : MixedTwoStageFiniteRow q T,
      mixedTwoStageFiniteRowMass theta selected row) =
        ∑ pilot : PauliPilotPath q,
          ∑ finalPath : MixedTwoStageFinalPath T,
            mixedTwoStageFiniteRowMass theta selected
              (pilot, finalPath) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ pilot : PauliPilotPath q,
        pauliPilotPathMass theta pilot := by
      apply Finset.sum_congr rfl
      intro pilot _
      exact mixedTwoStageFiniteRowMass_pilotFiber theta selected pilot
    _ = 1 := pauliPilotPathMass_sum_one (q := q) theta

/-! ## Explicit finite measure and its pilot marginal -/

/-- Explicit finite Dirac-sum measure generated by the joint two-stage mass. -/
def mixedTwoStageFiniteBornMeasure
    {q T : ℕ} (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q) :
    Measure (MixedTwoStageFiniteRow q T) :=
  Measure.sum fun row : MixedTwoStageFiniteRow q T =>
    ENNReal.ofReal (mixedTwoStageFiniteRowMass theta selected row) •
      Measure.dirac row

private theorem mixedTwoStage_ennreal_ofReal_finset_sum_nonnegative
    {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    ENNReal.ofReal (∑ a ∈ s, f a) =
      ∑ a ∈ s, ENNReal.ofReal (f a) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        ENNReal.ofReal_add (hf a)
          (Finset.sum_nonneg fun i _ => hf i), ih]

/-- Evaluation of the explicit finite joint measure on any event. -/
theorem mixedTwoStageFiniteBornMeasure_apply
    {q T : ℕ} (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q)
    (hphysical : PauliPilotPhysicalBloch theta)
    (event : Set (MixedTwoStageFiniteRow q T)) :
    mixedTwoStageFiniteBornMeasure theta selected event =
      ENNReal.ofReal
        (∑ row : MixedTwoStageFiniteRow q T,
          if row ∈ event then
            mixedTwoStageFiniteRowMass theta selected row
          else 0) := by
  unfold mixedTwoStageFiniteBornMeasure
  rw [Measure.sum_apply _ MeasurableSet.of_discrete, tsum_fintype]
  calc
    (∑ row : MixedTwoStageFiniteRow q T,
      (ENNReal.ofReal (mixedTwoStageFiniteRowMass theta selected row) •
        Measure.dirac row) event) =
        ∑ row : MixedTwoStageFiniteRow q T,
          ENNReal.ofReal
            (if row ∈ event then
              mixedTwoStageFiniteRowMass theta selected row
            else 0) := by
      apply Finset.sum_congr rfl
      intro row _
      by_cases hrow : row ∈ event
      · simp [Measure.smul_apply, hrow]
      · simp [Measure.smul_apply, hrow]
    _ = ENNReal.ofReal
        (∑ row : MixedTwoStageFiniteRow q T,
          if row ∈ event then
            mixedTwoStageFiniteRowMass theta selected row
          else 0) := by
      symm
      apply mixedTwoStage_ennreal_ofReal_finset_sum_nonnegative
      intro row
      by_cases hrow : row ∈ event
      · simp [hrow,
          mixedTwoStageFiniteRowMass_nonnegative
            theta selected hphysical row]
      · simp [hrow]

/-- The explicit finite joint measure has total mass one. -/
theorem mixedTwoStageFiniteBornMeasure_univ
    {q T : ℕ} (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q)
    (hphysical : PauliPilotPhysicalBloch theta) :
    mixedTwoStageFiniteBornMeasure (T := T) theta selected
      (univ : Set (MixedTwoStageFiniteRow q T)) = 1 := by
  rw [mixedTwoStageFiniteBornMeasure_apply
    (T := T) theta selected hphysical]
  simp [mixedTwoStageFiniteRowMass_sum_one]

/-- The first-coordinate marginal of the joint finite measure is exactly the
original Pauli pilot product measure, on every pilot event. -/
theorem mixedTwoStageFiniteBornMeasure_pilotMarginal
    {q T : ℕ} (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q)
    (hphysical : PauliPilotPhysicalBloch theta)
    (event : Set (PauliPilotPath q)) :
    mixedTwoStageFiniteBornMeasure theta selected
        ((fun row : MixedTwoStageFiniteRow q T => row.1) ⁻¹' event) =
      pauliPilotBornProductMeasure (q := q) theta event := by
  calc
    mixedTwoStageFiniteBornMeasure theta selected
        ((fun row : MixedTwoStageFiniteRow q T => row.1) ⁻¹' event) =
      ENNReal.ofReal
        (∑ row : MixedTwoStageFiniteRow q T,
          if row ∈
              ((fun row : MixedTwoStageFiniteRow q T => row.1) ⁻¹' event)
          then mixedTwoStageFiniteRowMass theta selected row
          else 0) :=
      mixedTwoStageFiniteBornMeasure_apply
        theta selected hphysical _
    _ = ENNReal.ofReal
        (∑ pilot : PauliPilotPath q,
          if pilot ∈ event then pauliPilotPathMass theta pilot else 0) := by
      simpa only [Set.mem_preimage] using
        congrArg ENNReal.ofReal
          (mixedTwoStageFiniteRowMass_pilotEventMarginal
            (T := T) theta selected event)
    _ = pauliPilotBornProductMeasure (q := q) theta event :=
      (pauliPilotBornProductMeasure_apply
        (q := q) theta hphysical event).symm

end

end QubitOracle.Paper
