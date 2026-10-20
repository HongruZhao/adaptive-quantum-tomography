import QubitOracle.Paper.OneQubitMixedPolynomialExactBuresRiskClosed
import QubitOracle.Paper.OneQubitMixedFiniteInfinitePilotIntegrationBridge
import QubitOracle.Paper.OneQubitMixedPolynomialQuadraticRiskClosed

/-!
# Polynomial two-stage mixed-qubit exact Bures endpoint

This file identifies the safeguarded exact-loss conditional average with the
explicit finite two-stage row, averages the frame-uniform conditional transfer,
and transports the established quadratic `9/4` limit to exact squared Bures
loss.  Final-stage scaling and pilot-plus-final scaling remain separate.
-/

open scoped BigOperators ENNReal
open Filter Topology MeasureTheory

namespace QubitOracle
namespace Paper

noncomputable section

/-! ## Explicit final-row exact losses -/

/-- Scaled safeguarded squared-Bures loss on one explicit cyclic two-stage
row.  The final path is transported to the three equal-allocation blocks by
the proved path equivalence. -/
def mixedTwoStageFiniteRowScaledSafeguardedBuresLoss
    {q r : ℕ} (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q)
    (row : MixedTwoStageFiniteRow q (3 * r)) : ℝ :=
  (3 * (r : ℝ)) *
    mixedFrameSafeguardedSquaredBuresLoss (q := r) theta
      (selected.frame row.1)
      (mixedTwoStageFinalPathPauliEquiv r row.2)

/-- Real expectation under the explicit joint finite-row mass. -/
def mixedTwoStageFiniteRowExpectedScaledSafeguardedBuresRisk
    {q : ℕ} (r : ℕ) (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q) : ℝ :=
  ∑ row : MixedTwoStageFiniteRow q (3 * r),
    mixedTwoStageFiniteRowMass theta selected row *
      mixedTwoStageFiniteRowScaledSafeguardedBuresLoss
        theta selected row

/-- On one pilot fiber, the explicit final-path mass and loss transport to the
concrete three-axis conditional safeguarded Bures risk. -/
theorem mixedTwoStageFiniteRow_scaledSafeguardedBuresLoss_pilotFiber
    {q : ℕ} (r : ℕ) (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) :
    (∑ finalPath : MixedTwoStageFinalPath (3 * r),
      mixedTwoStageFiniteRowMass theta selected (pilot, finalPath) *
        mixedTwoStageFiniteRowScaledSafeguardedBuresLoss
          theta selected (pilot, finalPath)) =
      pauliPilotPathMass theta pilot *
        mixedFrameConditionalScaledSafeguardedBuresRisk
          (q := r) theta (selected.frame pilot) := by
  classical
  have hFinal :
      (∑ finalPath : MixedTwoStageFinalPath (3 * r),
        mixedTwoStageConditionalFinalPathMass
            theta selected pilot finalPath *
          mixedFrameSafeguardedSquaredBuresLoss (q := r) theta
            (selected.frame pilot)
            (mixedTwoStageFinalPathPauliEquiv r finalPath)) =
        pauliPilotFiniteExpectation (q := r)
          (qubitFrameCoordinates (selected.frame pilot) theta)
          (mixedFrameSafeguardedSquaredBuresLoss (q := r) theta
            (selected.frame pilot)) := by
    unfold pauliPilotFiniteExpectation
    exact Fintype.sum_equiv (mixedTwoStageFinalPathPauliEquiv r)
      (fun finalPath : MixedTwoStageFinalPath (3 * r) =>
        mixedTwoStageConditionalFinalPathMass
            theta selected pilot finalPath *
          mixedFrameSafeguardedSquaredBuresLoss (q := r) theta
            (selected.frame pilot)
            (mixedTwoStageFinalPathPauliEquiv r finalPath))
      (fun path : PauliPilotPath r =>
        pauliPilotPathMass
            (qubitFrameCoordinates (selected.frame pilot) theta) path *
          mixedFrameSafeguardedSquaredBuresLoss (q := r) theta
            (selected.frame pilot) path)
      (fun finalPath => by
        rw [mixedTwoStageConditionalFinalPathMass_eq_pauliPilotPathMass])
  unfold mixedTwoStageFiniteRowMass
    mixedTwoStageFiniteRowScaledSafeguardedBuresLoss
    mixedFrameConditionalScaledSafeguardedBuresRisk
  calc
    (∑ finalPath : MixedTwoStageFinalPath (3 * r),
      (pauliPilotPathMass theta pilot *
          mixedTwoStageConditionalFinalPathMass
            theta selected pilot finalPath) *
        ((3 * (r : ℝ)) *
          mixedFrameSafeguardedSquaredBuresLoss (q := r) theta
            (selected.frame pilot)
            (mixedTwoStageFinalPathPauliEquiv r finalPath))) =
      pauliPilotPathMass theta pilot * (3 * (r : ℝ)) *
        (∑ finalPath : MixedTwoStageFinalPath (3 * r),
          mixedTwoStageConditionalFinalPathMass
              theta selected pilot finalPath *
            mixedFrameSafeguardedSquaredBuresLoss (q := r) theta
              (selected.frame pilot)
              (mixedTwoStageFinalPathPauliEquiv r finalPath)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro finalPath hfinal
        ring
    _ = pauliPilotPathMass theta pilot * (3 * (r : ℝ)) *
        pauliPilotFiniteExpectation (q := r)
          (qubitFrameCoordinates (selected.frame pilot) theta)
          (mixedFrameSafeguardedSquaredBuresLoss (q := r) theta
            (selected.frame pilot)) := by rw [hFinal]
    _ = pauliPilotPathMass theta pilot *
        ((3 * (r : ℝ)) *
          pauliPilotFiniteExpectation (q := r)
            (qubitFrameCoordinates (selected.frame pilot) theta)
            (mixedFrameSafeguardedSquaredBuresLoss (q := r) theta
              (selected.frame pilot))) := by ring

/-- Summing the explicit final row first gives exactly the pilot average of the
conditional exact risk. -/
theorem mixedTwoStageFiniteRow_scaledSafeguardedBuresRisk_eq_pilotAverage
    {q : ℕ} (r : ℕ) (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q) :
    mixedTwoStageFiniteRowExpectedScaledSafeguardedBuresRisk
        r theta selected =
      pauliPilotFiniteExpectation (q := q) theta
        (fun pilot : PauliPilotPath q =>
          mixedFrameConditionalScaledSafeguardedBuresRisk
            (q := r) theta (selected.frame pilot)) := by
  classical
  unfold mixedTwoStageFiniteRowExpectedScaledSafeguardedBuresRisk
    pauliPilotFiniteExpectation
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro pilot hpilot
  exact mixedTwoStageFiniteRow_scaledSafeguardedBuresLoss_pilotFiber
    r theta selected pilot

/-! ## Polynomial specialization and finite/infinite bridge -/

/-- Explicit polynomial two-stage expected safeguarded squared-Bures risk,
scaled by the final-stage observation count `3 * qFinal`. -/
def mixedPolynomialFinalStageExpectedScaledExactBuresRiskReal
    (theta b : RLSVector 3) (n : ℕ) : ℝ :=
  mixedTwoStageFiniteRowExpectedScaledSafeguardedBuresRisk
    (mixedPolynomialQuadraticQFinal n) theta
    (mixedPilotLocalSelectedFinalFrame
      (Nat.succ (polynomialPilotIndex n)) b)

/-- Nonnegative extended-real presentation used by the established quadratic
endpoint. -/
def mixedPolynomialFinalStageExpectedScaledExactBuresRisk
    (theta b : RLSVector 3) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (mixedPolynomialFinalStageExpectedScaledExactBuresRiskReal theta b n)

/-- The explicit joint-row definition equals its finite pilot average. -/
theorem mixedPolynomialFinalStageExpectedScaledExactBuresRiskReal_eq_pilotAverage
    (theta b : RLSVector 3) (n : ℕ) :
    mixedPolynomialFinalStageExpectedScaledExactBuresRiskReal theta b n =
      pauliPilotFiniteExpectation theta
        (fun pilot : PauliPilotPath (Nat.succ (polynomialPilotIndex n)) =>
          mixedFrameConditionalScaledSafeguardedBuresRisk
            (q := mixedPolynomialQuadraticQFinal n) theta
            (mixedPilotSelectedLocalFrame b (pauliPilotEstimate pilot))) := by
  simpa [mixedPolynomialFinalStageExpectedScaledExactBuresRiskReal,
    mixedPilotLocalSelectedFinalFrame] using
    (mixedTwoStageFiniteRow_scaledSafeguardedBuresRisk_eq_pilotAverage
      (mixedPolynomialQuadraticQFinal n) theta
      (mixedPilotLocalSelectedFinalFrame
        (Nat.succ (polynomialPilotIndex n)) b))

private theorem ENNReal_ofReal_finiteWeightedSum
    {α : Type*} [Fintype α] (weight value : α → ℝ)
    (hWeight : ∀ a, 0 ≤ weight a)
    (hValue : ∀ a, 0 ≤ value a) :
    ENNReal.ofReal (∑ a, weight a * value a) =
      ∑ a, ENNReal.ofReal (weight a) * ENNReal.ofReal (value a) := by
  classical
  have hAux : ∀ s : Finset α,
      ENNReal.ofReal (∑ a ∈ s, weight a * value a) =
        ∑ a ∈ s,
          ENNReal.ofReal (weight a) * ENNReal.ofReal (value a) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        have hTerm : 0 ≤ weight a * value a :=
          mul_nonneg (hWeight a) (hValue a)
        have hRest : 0 ≤ ∑ x ∈ s, weight x * value x :=
          Finset.sum_nonneg fun x hx => mul_nonneg (hWeight x) (hValue x)
        rw [Finset.sum_insert ha, Finset.sum_insert ha,
          ENNReal.ofReal_add hTerm hRest, ENNReal.ofReal_mul (hWeight a), ih]
  simpa using hAux Finset.univ

theorem mixedFrameConditionalScaledSafeguardedBuresRisk_nonnegative
    {q : ℕ} (theta : RLSVector 3)
    (hPhysical : PauliPilotPhysicalBloch theta)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : MixedFrameOrthonormal R) :
    0 ≤ mixedFrameConditionalScaledSafeguardedBuresRisk
      (q := q) theta R := by
  have hzPhysical := qubitFrameCoordinates_physical theta R hR hPhysical
  unfold mixedFrameConditionalScaledSafeguardedBuresRisk
    pauliPilotFiniteExpectation
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun path _ =>
      mul_nonneg
        (pauliPilotPathMass_nonnegative
          (qubitFrameCoordinates R theta) hzPhysical path)
        (mixedFrameSafeguardedSquaredBuresLoss_nonnegative theta R path))

/-- The explicit finite joint-row exact risk equals the common-infinite-pilot
integral from the preceding reduction. -/
theorem mixedPolynomialFinalStageExpectedScaledExactBuresRisk_eq_integral
    (theta b : RLSVector 3)
    (hPhysical : PauliPilotPhysicalBloch theta) (n : ℕ) :
    mixedPolynomialFinalStageExpectedScaledExactBuresRisk theta b n =
      mixedPolynomialFinalStageExactBuresRiskIntegral theta b n := by
  letI : MeasurableSpace
      (PauliPilotPath (Nat.succ (polynomialPilotIndex n))) :=
    mixedFiniteInfiniteBridgePilotPathMeasurableSpace _
  let qPilot := Nat.succ (polynomialPilotIndex n)
  let qFinal := mixedPolynomialQuadraticQFinal n
  have hFrame : ∀ pilot : PauliPilotPath qPilot,
      MixedFrameOrthonormal
        (mixedPilotSelectedLocalFrame b (pauliPilotEstimate pilot)) :=
    fun pilot => mixedPilotSelectedLocalFrame_orthonormal _ _
  have hConditional : ∀ pilot : PauliPilotPath qPilot,
      0 ≤ mixedFrameConditionalScaledSafeguardedBuresRisk
        (q := qFinal) theta
        (mixedPilotSelectedLocalFrame b (pauliPilotEstimate pilot)) :=
    fun pilot => mixedFrameConditionalScaledSafeguardedBuresRisk_nonnegative
      theta hPhysical _ (hFrame pilot)
  have hFiniteOfReal :
      ENNReal.ofReal
        (pauliPilotFiniteExpectation theta
          (fun pilot : PauliPilotPath qPilot =>
            mixedFrameConditionalScaledSafeguardedBuresRisk
              (q := qFinal) theta
              (mixedPilotSelectedLocalFrame b (pauliPilotEstimate pilot)))) =
        ∑ pilot : PauliPilotPath qPilot,
          ENNReal.ofReal (pauliPilotPathMass theta pilot) *
            ENNReal.ofReal
              (mixedFrameConditionalScaledSafeguardedBuresRisk
                (q := qFinal) theta
                (mixedPilotSelectedLocalFrame b
                  (pauliPilotEstimate pilot))) := by
    unfold pauliPilotFiniteExpectation
    exact ENNReal_ofReal_finiteWeightedSum
      (fun pilot : PauliPilotPath qPilot => pauliPilotPathMass theta pilot)
      (fun pilot => mixedFrameConditionalScaledSafeguardedBuresRisk
        (q := qFinal) theta
        (mixedPilotSelectedLocalFrame b (pauliPilotEstimate pilot)))
      (fun pilot => pauliPilotPathMass_nonnegative theta hPhysical pilot)
      hConditional
  have hBridge :=
    lintegral_pauliPilotConsistency_pullback_eq_finiteMassSum
      theta hPhysical (polynomialPilotIndex n)
      (fun pilot : PauliPilotPath (Nat.succ (polynomialPilotIndex n)) =>
        ENNReal.ofReal
          (mixedFrameConditionalScaledSafeguardedBuresRisk
            (q := mixedPolynomialQuadraticQFinal n) theta
            (mixedPilotSelectedLocalFrame b (pauliPilotEstimate pilot))))
      Measurable.of_discrete
  rw [mixedPolynomialFinalStageExpectedScaledExactBuresRisk,
    mixedPolynomialFinalStageExpectedScaledExactBuresRiskReal_eq_pilotAverage]
  rw [hFiniteOfReal]
  simpa [mixedPolynomialFinalStageExactBuresRiskIntegral,
    polynomialPilotEstimator, pauliPilotConsistencyEstimator,
    qPilot, qFinal] using hBridge.symm

/-- The previously isolated finite-pilot averaging statement is now supplied
by the explicit final-path equivalence and finite marginal bridge. -/
theorem mixedPolynomialExactBuresFinitePilotAveragingLemma_closed
    (theta b : RLSVector 3)
    (hPhysical : PauliPilotPhysicalBloch theta) :
    MixedPolynomialExactBuresFinitePilotAveragingLemma theta b
      (mixedPolynomialFinalStageExpectedScaledExactBuresRisk theta b) := by
  intro n
  exact mixedPolynomialFinalStageExpectedScaledExactBuresRisk_eq_integral
    theta b hPhysical n

/-! ## Averaging the uniform conditional transfer -/

private theorem pauliPilotFiniteExpectation_abs_sub_le_const
    {q : ℕ} (theta : RLSVector 3)
    (hPhysical : PauliPilotPhysicalBloch theta)
    (f g : PauliPilotPath q → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hPointwise : ∀ pilot, |f pilot - g pilot| ≤ c) :
    |pauliPilotFiniteExpectation theta f -
        pauliPilotFiniteExpectation theta g| ≤ c := by
  unfold pauliPilotFiniteExpectation
  rw [← Finset.sum_sub_distrib]
  have hRewrite :
      (∑ pilot : PauliPilotPath q,
        (pauliPilotPathMass theta pilot * f pilot -
          pauliPilotPathMass theta pilot * g pilot)) =
        ∑ pilot : PauliPilotPath q,
          pauliPilotPathMass theta pilot * (f pilot - g pilot) := by
    apply Finset.sum_congr rfl
    intro pilot hpilot
    ring
  rw [hRewrite]
  calc
    |∑ pilot : PauliPilotPath q,
      pauliPilotPathMass theta pilot * (f pilot - g pilot)| ≤
        ∑ pilot : PauliPilotPath q,
          |pauliPilotPathMass theta pilot * (f pilot - g pilot)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ pilot : PauliPilotPath q,
        pauliPilotPathMass theta pilot * |f pilot - g pilot| := by
      apply Finset.sum_congr rfl
      intro pilot hpilot
      rw [abs_mul,
        abs_of_nonneg
          (pauliPilotPathMass_nonnegative theta hPhysical pilot)]
    _ ≤ ∑ pilot : PauliPilotPath q,
        pauliPilotPathMass theta pilot * c := by
      exact Finset.sum_le_sum fun pilot _ =>
        mul_le_mul_of_nonneg_left (hPointwise pilot)
          (pauliPilotPathMass_nonnegative theta hPhysical pilot)
    _ = c := by
      rw [← Finset.sum_mul, pauliPilotPathMass_sum_one]
      ring

/-- Real finite-pilot average of the established conditional quadratic risk. -/
def mixedPolynomialFinalStageExpectedScaledQuadraticRiskReal
    (theta b : RLSVector 3) (n : ℕ) : ℝ :=
  pauliPilotFiniteExpectation theta
    (fun pilot : PauliPilotPath (Nat.succ (polynomialPilotIndex n)) =>
      mixedFrameConditionalScaledQuadraticRisk
        (q := mixedPolynomialQuadraticQFinal n) theta
        (mixedPilotSelectedLocalFrame b (pauliPilotEstimate pilot)))

theorem mixedPolynomialFinalStageExpectedScaledQuadraticRiskReal_nonnegative
    (theta b : RLSVector 3)
    (hInterior : blochNormSq theta < 1)
    (hPhysical : PauliPilotPhysicalBloch theta) (n : ℕ) :
    0 ≤ mixedPolynomialFinalStageExpectedScaledQuadraticRiskReal theta b n := by
  unfold mixedPolynomialFinalStageExpectedScaledQuadraticRiskReal
    pauliPilotFiniteExpectation
  exact Finset.sum_nonneg fun pilot _ =>
    mul_nonneg
      (pauliPilotPathMass_nonnegative theta hPhysical pilot)
      (mixedFrameConditionalScaledQuadraticRisk_nonnegative_closed
        (mixedPolynomialQuadraticQFinal_pos n) theta hInterior
        (mixedPilotSelectedLocalFrame b (pauliPilotEstimate pilot))
        (mixedPilotSelectedLocalFrame_orthonormal _ _))

/-- The real quadratic pilot average is exactly the finite `ENNReal` object
used by the proved quadratic endpoint. -/
theorem mixedPolynomialFinalStageExpectedScaledQuadraticRisk_eq_ofReal_real
    (theta b : RLSVector 3)
    (hInterior : blochNormSq theta < 1)
    (hPhysical : PauliPilotPhysicalBloch theta) (n : ℕ) :
    mixedPolynomialFinalStageExpectedScaledQuadraticRisk theta b n =
      ENNReal.ofReal
        (mixedPolynomialFinalStageExpectedScaledQuadraticRiskReal theta b n) := by
  let qPilot := Nat.succ (polynomialPilotIndex n)
  have hValue : ∀ pilot : PauliPilotPath qPilot,
      0 ≤ mixedFrameConditionalScaledQuadraticRisk
        (q := mixedPolynomialQuadraticQFinal n) theta
        (mixedPilotSelectedLocalFrame b (pauliPilotEstimate pilot)) :=
    fun pilot => mixedFrameConditionalScaledQuadraticRisk_nonnegative_closed
      (mixedPolynomialQuadraticQFinal_pos n) theta hInterior
      (mixedPilotSelectedLocalFrame b (pauliPilotEstimate pilot))
      (mixedPilotSelectedLocalFrame_orthonormal _ _)
  have hMap := ENNReal_ofReal_finiteWeightedSum
    (fun pilot : PauliPilotPath qPilot => pauliPilotPathMass theta pilot)
    (fun pilot => mixedFrameConditionalScaledQuadraticRisk
      (q := mixedPolynomialQuadraticQFinal n) theta
      (mixedPilotSelectedLocalFrame b (pauliPilotEstimate pilot)))
    (fun pilot => pauliPilotPathMass_nonnegative theta hPhysical pilot)
    hValue
  simpa [mixedPolynomialFinalStageExpectedScaledQuadraticRisk,
    mixedPolynomialFinitePilotAverageScaledRisk,
    mixedPolynomialFinalStageExpectedScaledQuadraticRiskReal,
    pauliPilotFiniteExpectation, mixedPolynomialQuadraticQFinal, qPilot] using hMap.symm

/-- Averaging does not enlarge the frame-uniform conditional transfer rate. -/
theorem mixedPolynomialFinalStageExactBures_abs_sub_quadraticReal_le
    (theta b : RLSVector 3)
    (hInterior : blochNormSq theta < 1)
    (hPhysical : PauliPilotPhysicalBloch theta) (n : ℕ) :
    |mixedPolynomialFinalStageExpectedScaledExactBuresRiskReal theta b n -
        mixedPolynomialFinalStageExpectedScaledQuadraticRiskReal theta b n| ≤
      mixedFrameExactBuresTransferRate theta
        (mixedPolynomialQuadraticQFinal n) := by
  rw [mixedPolynomialFinalStageExpectedScaledExactBuresRiskReal_eq_pilotAverage]
  apply pauliPilotFiniteExpectation_abs_sub_le_const theta hPhysical
  · have hGap : 0 < 1 - blochNormSq theta := by linarith
    have hEta := mixedBuresFidelityLocalRadius_pos hInterior
    unfold mixedFrameExactBuresTransferRate
    dsimp only
    positivity
  · intro pilot
    exact mixedFrameConditionalScaledSafeguardedBuresRisk_transfer
      (mixedPolynomialQuadraticQFinal_pos n) theta hInterior
      (mixedPilotSelectedLocalFrame b (pauliPilotEstimate pilot))
      (mixedPilotSelectedLocalFrame_orthonormal _ _)

/-- The explicit transfer rate also vanishes along the degree-six final
allocation. -/
theorem mixedPolynomialExactBuresTransferRate_tendsto_zero
    (theta : RLSVector 3) (hInterior : blochNormSq theta < 1) :
    Tendsto
      (fun n => mixedFrameExactBuresTransferRate theta
        (mixedPolynomialQuadraticQFinal n))
      atTop (nhds 0) := by
  let N : ℕ → ℝ := fun n => (n + 1 : ℕ)
  let gap := 1 - blochNormSq theta
  let eta := mixedBuresFidelityLocalRadius theta
  have hN : Tendsto N atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ tendsto_natCast_atTop_atTop
    exact Eventually.of_forall fun n => by
      dsimp [N]
      norm_cast
      exact Nat.le_succ n
  have hInvN : Tendsto (fun n => (N n)⁻¹) atTop (nhds 0) :=
    hN.inv_tendsto_atTop
  have hInvThree := hInvN.pow 3
  have hInvSix := hInvN.pow 6
  have hConstOne : Tendsto (fun _ : ℕ => 54 / gap ^ 2)
      atTop (nhds (54 / gap ^ 2)) := tendsto_const_nhds
  have hConstTwo : Tendsto (fun _ : ℕ => 90 / gap ^ 3)
      atTop (nhds (90 / gap ^ 3)) := tendsto_const_nhds
  have hConstThree : Tendsto (fun _ : ℕ => 90 / eta ^ 4)
      atTop (nhds (90 / eta ^ 4)) := tendsto_const_nhds
  have hConstFour : Tendsto (fun _ : ℕ => 45 / (4 * gap * eta ^ 2))
      atTop (nhds (45 / (4 * gap * eta ^ 2))) := tendsto_const_nhds
  have hOne : Tendsto (fun n => (54 / gap ^ 2) * ((N n)⁻¹) ^ 3)
      atTop (nhds 0) := by simpa using hConstOne.mul hInvThree
  have hTwo : Tendsto (fun n => (90 / gap ^ 3) * ((N n)⁻¹) ^ 6)
      atTop (nhds 0) := by simpa using hConstTwo.mul hInvSix
  have hThree : Tendsto (fun n => (90 / eta ^ 4) * ((N n)⁻¹) ^ 6)
      atTop (nhds 0) := by simpa using hConstThree.mul hInvSix
  have hFour : Tendsto
      (fun n => (45 / (4 * gap * eta ^ 2)) * ((N n)⁻¹) ^ 6)
      atTop (nhds 0) := by simpa using hConstFour.mul hInvSix
  have hSum : Tendsto
      (fun n =>
        (54 / gap ^ 2) * ((N n)⁻¹) ^ 3 +
          (90 / gap ^ 3) * ((N n)⁻¹) ^ 6 +
          (90 / eta ^ 4) * ((N n)⁻¹) ^ 6 +
          (45 / (4 * gap * eta ^ 2)) * ((N n)⁻¹) ^ 6)
      atTop (nhds 0) := by
    simpa using ((hOne.add hTwo).add hThree).add hFour
  apply hSum.congr'
  exact Eventually.of_forall fun n => by
    have hNpos : 0 < N n := by
      dsimp [N]
      positivity
    have hQ : (mixedPolynomialQuadraticQFinal n : ℝ) = (N n) ^ 6 := by
      simp [mixedPolynomialQuadraticQFinal, polynomialFinalShots,
        polynomialScheduleM, N, Nat.cast_pow]
    have hSqrt :
        Real.sqrt (mixedPolynomialQuadraticQFinal n : ℝ) = (N n) ^ 3 := by
      rw [hQ, show (N n) ^ 6 = ((N n) ^ 3) ^ 2 by ring,
        Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
    unfold mixedFrameExactBuresTransferRate
    dsimp only
    rw [hSqrt, hQ]
    field_simp [hNpos.ne']
    ring

/-! ## The exact `9/4` endpoints -/

theorem mixedPolynomialFinalStageExpectedScaledQuadraticRiskReal_tendsto_nine_fourths
    (theta b : RLSVector 3)
    (hPositive : 0 < blochNormSq theta)
    (hInterior : blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hPhysical : PauliPilotPhysicalBloch theta)
    (hHoeffding : PauliPilotConsistencyHoeffdingContracts theta hPhysical) :
    Tendsto (mixedPolynomialFinalStageExpectedScaledQuadraticRiskReal theta b)
      atTop (nhds (9 / 4 : ℝ)) := by
  have hENN :=
    mixedPolynomialFinalStageExpectedScaledQuadraticRisk_tendsto_nine_fourths
      theta b hPositive hInterior hSeed hPhysical hHoeffding
  have hToReal := (ENNReal.tendsto_toReal (by simp)).comp hENN
  have hToReal' : Tendsto
      (ENNReal.toReal ∘
        mixedPolynomialFinalStageExpectedScaledQuadraticRisk theta b)
      atTop (nhds (9 / 4 : ℝ)) := by
    convert hToReal using 1 <;> norm_num
  apply hToReal'.congr'
  exact Eventually.of_forall fun n => by
    change (mixedPolynomialFinalStageExpectedScaledQuadraticRisk theta b n).toReal =
      mixedPolynomialFinalStageExpectedScaledQuadraticRiskReal theta b n
    rw [mixedPolynomialFinalStageExpectedScaledQuadraticRisk_eq_ofReal_real
      theta b hInterior hPhysical]
    simp [mixedPolynomialFinalStageExpectedScaledQuadraticRiskReal_nonnegative
      theta b hInterior hPhysical]

theorem mixedPolynomialFinalStageExpectedScaledExactBuresRiskReal_tendsto_nine_fourths
    (theta b : RLSVector 3)
    (hPositive : 0 < blochNormSq theta)
    (hInterior : blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hPhysical : PauliPilotPhysicalBloch theta)
    (hHoeffding : PauliPilotConsistencyHoeffdingContracts theta hPhysical) :
    Tendsto (mixedPolynomialFinalStageExpectedScaledExactBuresRiskReal theta b)
      atTop (nhds (9 / 4 : ℝ)) := by
  have hQuadratic :=
    mixedPolynomialFinalStageExpectedScaledQuadraticRiskReal_tendsto_nine_fourths
      theta b hPositive hInterior hSeed hPhysical hHoeffding
  have hRate := mixedPolynomialExactBuresTransferRate_tendsto_zero
    theta hInterior
  have hLower : Tendsto
      (fun n => mixedPolynomialFinalStageExpectedScaledQuadraticRiskReal theta b n -
        mixedFrameExactBuresTransferRate theta
          (mixedPolynomialQuadraticQFinal n))
      atTop (nhds (9 / 4 : ℝ)) := by
    simpa using hQuadratic.sub hRate
  have hUpper : Tendsto
      (fun n => mixedPolynomialFinalStageExpectedScaledQuadraticRiskReal theta b n +
        mixedFrameExactBuresTransferRate theta
          (mixedPolynomialQuadraticQFinal n))
      atTop (nhds (9 / 4 : ℝ)) := by
    simpa using hQuadratic.add hRate
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hLower hUpper
    (Eventually.of_forall fun n => by
      have hBound :=
        mixedPolynomialFinalStageExactBures_abs_sub_quadraticReal_le
          theta b hInterior hPhysical n
      rw [abs_le] at hBound
      linarith)
    (Eventually.of_forall fun n => by
      have hBound :=
        mixedPolynomialFinalStageExactBures_abs_sub_quadraticReal_le
          theta b hInterior hPhysical n
      rw [abs_le] at hBound
      linarith)

/-- Final-stage-scaled exact safeguarded squared-Bures risk tends to `9/4`. -/
theorem mixedPolynomialFinalStageExpectedScaledExactBuresRisk_tendsto_nine_fourths
    (theta b : RLSVector 3)
    (hPositive : 0 < blochNormSq theta)
    (hInterior : blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hPhysical : PauliPilotPhysicalBloch theta)
    (hHoeffding : PauliPilotConsistencyHoeffdingContracts theta hPhysical) :
    Tendsto (mixedPolynomialFinalStageExpectedScaledExactBuresRisk theta b)
      atTop (nhds (ENNReal.ofReal (9 / 4 : ℝ))) := by
  exact (ENNReal.continuous_ofReal.tendsto (9 / 4 : ℝ)).comp
    (mixedPolynomialFinalStageExpectedScaledExactBuresRiskReal_tendsto_nine_fourths
      theta b hPositive hInterior hSeed hPhysical hHoeffding)

/-- Total-observation scaling multiplies the final-stage risk by the already
proved pilot-plus-final to final-stage ratio. -/
def mixedPolynomialTotalObservationScaledExpectedExactBuresRisk
    (theta b : RLSVector 3) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (mixedPolynomialExactCycleTotalToFinalRatio n) *
    mixedPolynomialFinalStageExpectedScaledExactBuresRisk theta b n

/-- Pilot-plus-final total-observation-scaled exact squared-Bures risk also
tends to `9/4`. -/
theorem mixedPolynomialTotalObservationScaledExpectedExactBuresRisk_tendsto_nine_fourths
    (theta b : RLSVector 3)
    (hPositive : 0 < blochNormSq theta)
    (hInterior : blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hPhysical : PauliPilotPhysicalBloch theta)
    (hHoeffding : PauliPilotConsistencyHoeffdingContracts theta hPhysical) :
    Tendsto
      (mixedPolynomialTotalObservationScaledExpectedExactBuresRisk theta b)
      atTop (nhds (ENNReal.ofReal (9 / 4 : ℝ))) := by
  have hRatioReal := mixedPolynomialExactCycleTotalToFinalRatio_tendsto_one
  have hRatio : Tendsto
      (fun n => ENNReal.ofReal
        (mixedPolynomialExactCycleTotalToFinalRatio n))
      atTop (nhds (ENNReal.ofReal (1 : ℝ))) := by
    change Tendsto
      (ENNReal.ofReal ∘ mixedPolynomialExactCycleTotalToFinalRatio)
      atTop (nhds (ENNReal.ofReal (1 : ℝ)))
    exact (ENNReal.continuous_ofReal.tendsto 1).comp hRatioReal
  have hExact :=
    mixedPolynomialFinalStageExpectedScaledExactBuresRisk_tendsto_nine_fourths
      theta b hPositive hInterior hSeed hPhysical hHoeffding
  change Tendsto
    (fun n => ENNReal.ofReal (mixedPolynomialExactCycleTotalToFinalRatio n) *
      mixedPolynomialFinalStageExpectedScaledExactBuresRisk theta b n)
    atTop (nhds (ENNReal.ofReal (9 / 4 : ℝ)))
  simpa using
    ENNReal.Tendsto.mul hRatio (by simp) hExact (by simp)

/-! ## Root-infidelity constants -/

/-- Explicit final-row root-infidelity loss under the same `3r` scaling. -/
def mixedTwoStageFiniteRowScaledRootInfidelityLoss
    {q r : ℕ} (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q)
    (row : MixedTwoStageFiniteRow q (3 * r)) : ℝ :=
  (3 * (r : ℝ)) *
    mixedFrameSafeguardedRootInfidelityLoss (q := r) theta
      (selected.frame row.1)
      (mixedTwoStageFinalPathPauliEquiv r row.2)

def mixedPolynomialFinalStageExpectedScaledRootInfidelityRiskReal
    (theta b : RLSVector 3) (n : ℕ) : ℝ :=
  ∑ row : MixedTwoStageFiniteRow
      (Nat.succ (polynomialPilotIndex n))
      (3 * mixedPolynomialQuadraticQFinal n),
    mixedTwoStageFiniteRowMass theta
        (mixedPilotLocalSelectedFinalFrame
          (Nat.succ (polynomialPilotIndex n)) b) row *
      mixedTwoStageFiniteRowScaledRootInfidelityLoss theta
        (mixedPilotLocalSelectedFinalFrame
          (Nat.succ (polynomialPilotIndex n)) b) row

def mixedPolynomialFinalStageExpectedScaledRootInfidelityRisk
    (theta b : RLSVector 3) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (mixedPolynomialFinalStageExpectedScaledRootInfidelityRiskReal theta b n)

theorem mixedPolynomialFinalStageExactBures_eq_two_mul_rootInfidelityReal
    (theta b : RLSVector 3) (n : ℕ) :
    mixedPolynomialFinalStageExpectedScaledExactBuresRiskReal theta b n =
      2 * mixedPolynomialFinalStageExpectedScaledRootInfidelityRiskReal
        theta b n := by
  classical
  unfold mixedPolynomialFinalStageExpectedScaledExactBuresRiskReal
    mixedTwoStageFiniteRowExpectedScaledSafeguardedBuresRisk
    mixedTwoStageFiniteRowScaledSafeguardedBuresLoss
    mixedPolynomialFinalStageExpectedScaledRootInfidelityRiskReal
    mixedTwoStageFiniteRowScaledRootInfidelityLoss
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro row hrow
  rw [mixedFrameSafeguardedSquaredBuresLoss_eq_two_mul_rootInfidelity]
  ring

/-- Final-stage-scaled root infidelity tends to `9/8`. -/
theorem mixedPolynomialFinalStageExpectedScaledRootInfidelityRisk_tendsto_nine_eighths
    (theta b : RLSVector 3)
    (hPositive : 0 < blochNormSq theta)
    (hInterior : blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hPhysical : PauliPilotPhysicalBloch theta)
    (hHoeffding : PauliPilotConsistencyHoeffdingContracts theta hPhysical) :
    Tendsto (mixedPolynomialFinalStageExpectedScaledRootInfidelityRisk theta b)
      atTop (nhds (ENNReal.ofReal (9 / 8 : ℝ))) := by
  have hReal :=
    mixedPolynomialFinalStageExpectedScaledExactBuresRiskReal_tendsto_nine_fourths
      theta b hPositive hInterior hSeed hPhysical hHoeffding
  have hHalf : Tendsto
      (fun n => (2 : ℝ)⁻¹ *
        mixedPolynomialFinalStageExpectedScaledExactBuresRiskReal theta b n)
      atTop (nhds (9 / 8 : ℝ)) := by
    convert tendsto_const_nhds.mul hReal using 1 <;> norm_num
  have hRootReal : Tendsto
      (mixedPolynomialFinalStageExpectedScaledRootInfidelityRiskReal theta b)
      atTop (nhds (9 / 8 : ℝ)) := by
    apply hHalf.congr'
    exact Eventually.of_forall fun n => by
      change (2 : ℝ)⁻¹ *
          mixedPolynomialFinalStageExpectedScaledExactBuresRiskReal theta b n =
        mixedPolynomialFinalStageExpectedScaledRootInfidelityRiskReal theta b n
      rw [mixedPolynomialFinalStageExactBures_eq_two_mul_rootInfidelityReal]
      ring
  exact (ENNReal.continuous_ofReal.tendsto (9 / 8 : ℝ)).comp hRootReal

def mixedPolynomialTotalObservationScaledExpectedRootInfidelityRisk
    (theta b : RLSVector 3) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (mixedPolynomialExactCycleTotalToFinalRatio n) *
    mixedPolynomialFinalStageExpectedScaledRootInfidelityRisk theta b n

theorem mixedPolynomialTotalObservationScaledExpectedRootInfidelityRisk_tendsto_nine_eighths
    (theta b : RLSVector 3)
    (hPositive : 0 < blochNormSq theta)
    (hInterior : blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hPhysical : PauliPilotPhysicalBloch theta)
    (hHoeffding : PauliPilotConsistencyHoeffdingContracts theta hPhysical) :
    Tendsto
      (mixedPolynomialTotalObservationScaledExpectedRootInfidelityRisk theta b)
      atTop (nhds (ENNReal.ofReal (9 / 8 : ℝ))) := by
  have hRatioReal := mixedPolynomialExactCycleTotalToFinalRatio_tendsto_one
  have hRatio : Tendsto
      (fun n => ENNReal.ofReal
        (mixedPolynomialExactCycleTotalToFinalRatio n))
      atTop (nhds (ENNReal.ofReal (1 : ℝ))) := by
    change Tendsto
      (ENNReal.ofReal ∘ mixedPolynomialExactCycleTotalToFinalRatio)
      atTop (nhds (ENNReal.ofReal (1 : ℝ)))
    exact (ENNReal.continuous_ofReal.tendsto 1).comp hRatioReal
  have hRoot :=
    mixedPolynomialFinalStageExpectedScaledRootInfidelityRisk_tendsto_nine_eighths
      theta b hPositive hInterior hSeed hPhysical hHoeffding
  change Tendsto
    (fun n => ENNReal.ofReal (mixedPolynomialExactCycleTotalToFinalRatio n) *
      mixedPolynomialFinalStageExpectedScaledRootInfidelityRisk theta b n)
    atTop (nhds (ENNReal.ofReal (9 / 8 : ℝ)))
  simpa using
    ENNReal.Tendsto.mul hRatio (by simp) hRoot (by simp)

/-! ## Precise ordinary-infidelity boundary -/

/-- Safeguarded ordinary infidelity `1 - F` on one explicit final row. -/
def mixedTwoStageFiniteRowScaledOrdinaryInfidelityLoss
    {q r : ℕ} (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q)
    (row : MixedTwoStageFiniteRow q (3 * r)) : ℝ :=
  (3 * (r : ℝ)) * max 0
    (mixedQubitBlochInfidelityBetween theta
      (mixedFrameSafeguardedFinalEstimator (q := r) (selected.frame row.1)
        (mixedTwoStageFinalPathPauliEquiv r row.2)))

def mixedPolynomialFinalStageExpectedScaledOrdinaryInfidelityRiskReal
    (theta b : RLSVector 3) (n : ℕ) : ℝ :=
  ∑ row : MixedTwoStageFiniteRow
      (Nat.succ (polynomialPilotIndex n))
      (3 * mixedPolynomialQuadraticQFinal n),
    mixedTwoStageFiniteRowMass theta
        (mixedPilotLocalSelectedFinalFrame
          (Nat.succ (polynomialPilotIndex n)) b) row *
      mixedTwoStageFiniteRowScaledOrdinaryInfidelityLoss theta
        (mixedPilotLocalSelectedFinalFrame
          (Nat.succ (polynomialPilotIndex n)) b) row

/-- Exact remaining fourth-order requirement for ordinary infidelity.  It asks
for the scaled difference from squared Bures to be `O(1/qFinal)`, which is the
finite-row expectation of the squared root-infidelity remainder. -/
def MixedPolynomialOrdinaryInfidelityHigherOrderExpectationBound
    (theta b : RLSVector 3) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
    |mixedPolynomialFinalStageExpectedScaledOrdinaryInfidelityRiskReal
        theta b n -
      mixedPolynomialFinalStageExpectedScaledExactBuresRiskReal theta b n| ≤
      C / (mixedPolynomialQuadraticQFinal n : ℝ)

/-- The isolated fourth-order expectation estimate is sufficient for the
ordinary-infidelity `9/4` endpoint. -/
theorem mixedPolynomialFinalStageExpectedScaledOrdinaryInfidelityRiskReal_tendsto_nine_fourths_of_higherOrder
    (theta b : RLSVector 3)
    (hPositive : 0 < blochNormSq theta)
    (hInterior : blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hPhysical : PauliPilotPhysicalBloch theta)
    (hHoeffding : PauliPilotConsistencyHoeffdingContracts theta hPhysical)
    (hHigher : MixedPolynomialOrdinaryInfidelityHigherOrderExpectationBound
      theta b) :
    Tendsto
      (mixedPolynomialFinalStageExpectedScaledOrdinaryInfidelityRiskReal theta b)
      atTop (nhds (9 / 4 : ℝ)) := by
  rcases hHigher with ⟨C, hC, hBound⟩
  have hExact :=
    mixedPolynomialFinalStageExpectedScaledExactBuresRiskReal_tendsto_nine_fourths
      theta b hPositive hInterior hSeed hPhysical hHoeffding
  have hQAtTop : Tendsto
      (fun n => (mixedPolynomialQuadraticQFinal n : ℝ)) atTop atTop := by
    let N : ℕ → ℝ := fun n => (n + 1 : ℕ)
    have hN : Tendsto N atTop atTop := by
      refine tendsto_atTop_mono' atTop ?_ tendsto_natCast_atTop_atTop
      exact Eventually.of_forall fun n => by
        dsimp [N]
        norm_cast
        exact Nat.le_succ n
    refine tendsto_atTop_mono' atTop ?_ hN
    exact Eventually.of_forall fun n => by
      change N n ≤ (mixedPolynomialQuadraticQFinal n : ℝ)
      rw [show (mixedPolynomialQuadraticQFinal n : ℝ) = (N n) ^ 6 by
        simp [mixedPolynomialQuadraticQFinal, polynomialFinalShots,
          polynomialScheduleM, N, Nat.cast_pow]]
      have hNge : (1 : ℝ) ≤ N n := by
        dsimp [N]
        norm_cast
        exact Nat.succ_le_succ (Nat.zero_le n)
      exact le_self_pow₀ hNge (by norm_num)
  have hInv : Tendsto
      (fun n => ((mixedPolynomialQuadraticQFinal n : ℝ))⁻¹)
      atTop (nhds 0) := hQAtTop.inv_tendsto_atTop
  have hRate : Tendsto
      (fun n => C / (mixedPolynomialQuadraticQFinal n : ℝ))
      atTop (nhds 0) := by
    have hConst : Tendsto (fun _ : ℕ => C) atTop (nhds C) :=
      tendsto_const_nhds
    simpa [div_eq_mul_inv] using hConst.mul hInv
  have hLower : Tendsto
      (fun n => mixedPolynomialFinalStageExpectedScaledExactBuresRiskReal theta b n -
        C / (mixedPolynomialQuadraticQFinal n : ℝ))
      atTop (nhds (9 / 4 : ℝ)) := by
    simpa using hExact.sub hRate
  have hUpper : Tendsto
      (fun n => mixedPolynomialFinalStageExpectedScaledExactBuresRiskReal theta b n +
        C / (mixedPolynomialQuadraticQFinal n : ℝ))
      atTop (nhds (9 / 4 : ℝ)) := by
    simpa using hExact.add hRate
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hLower hUpper
    (Eventually.of_forall fun n => by
      have hn := hBound n
      rw [abs_le] at hn
      linarith)
    (Eventually.of_forall fun n => by
      have hn := hBound n
      rw [abs_le] at hn
      linarith)

namespace Label

/-- Paper-facing concrete mixed-qubit exact-Bures endpoint, including the
pilot-plus-final normalization. -/
theorem thm_mixed_polynomial_exact_bures_risk_endpoint_qubit
    (theta b : RLSVector 3)
    (hPositive : 0 < blochNormSq theta)
    (hInterior : blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hPhysical : PauliPilotPhysicalBloch theta)
    (hHoeffding : PauliPilotConsistencyHoeffdingContracts theta hPhysical) :
    Tendsto
      (mixedPolynomialTotalObservationScaledExpectedExactBuresRisk theta b)
      atTop (nhds (ENNReal.ofReal (9 / 4 : ℝ))) :=
  mixedPolynomialTotalObservationScaledExpectedExactBuresRisk_tendsto_nine_fourths
    theta b hPositive hInterior hSeed hPhysical hHoeffding

end Label

end
end Paper
end QubitOracle
