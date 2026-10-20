import QubitOracle.Paper.OneQubitMixedTwoStageFiniteLaw
import QubitOracle.Paper.OneQubitMixedExactCycleInformation
import QubitOracle.Paper.OneQubitMixedPilotFrameRiskTransfer
import QubitOracle.Paper.OneQubitMixedPolynomialBadBranchRisk

/-!
# Exact final-estimator law for one mixed-qubit two-stage row

At final horizon `3 * r`, a binary cyclic path is equivalent to `r` complete
three-axis blocks.  This file transports every Born atom, the linear estimator,
and the quadratic loss across that equivalence.  It then proves the exact
finite-sum conditional-risk and joint pilot-average identities.

No asymptotic statement or infinite-protocol joint law is asserted.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace QubitOracle.Paper

noncomputable section

/-! ## Final-path equivalence -/

/-- A cyclic binary path of length `3 * r` is exactly one block of `r`
outcomes for each of the three frame columns. -/
def mixedTwoStageFinalPathPauliEquiv (r : ℕ) :
    MixedTwoStageFinalPath (3 * r) ≃ PauliPilotPath r where
  toFun finalPath block k :=
    finalPath (mixedTwoStageExactCycleEquiv r (block, k))
  invFun path t :=
    path ((mixedTwoStageExactCycleEquiv r).symm t).1
      ((mixedTwoStageExactCycleEquiv r).symm t).2
  left_inv finalPath := by
    funext t
    simp
  right_inv path := by
    funext block k
    simp

@[simp]
theorem mixedTwoStageFinalPathPauliEquiv_apply
    (r : ℕ) (finalPath : MixedTwoStageFinalPath (3 * r))
    (block : Fin r) (k : Fin 3) :
    mixedTwoStageFinalPathPauliEquiv r finalPath block k =
      finalPath (mixedTwoStageExactCycleEquiv r (block, k)) :=
  rfl

/-- Under the path equivalence, the cyclic time indexed by `(block,k)` uses
exactly frame column `k`. -/
@[simp]
theorem mixedTwoStageFinalAxis_exactCycle
    {q : ℕ} (r : ℕ) (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) (block : Fin r) (k : Fin 3) :
    mixedTwoStageFinalAxis selected pilot
        (mixedTwoStageExactCycleEquiv r (block, k)) =
      mixedTwoStageFrameAxis (selected.frame pilot) k := by
  simp [mixedTwoStageFinalAxis]

/-- Each cyclic one-shot Born factor is the corresponding frame-coordinate
Pauli Born factor. -/
@[simp]
theorem mixedTwoStageFinalBornProbability_exactCycle
    {q : ℕ} (r : ℕ) (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) (block : Fin r) (k : Fin 3)
    (outcome : Bool) :
    mixedTwoStageFinalBornProbability theta selected pilot
        (mixedTwoStageExactCycleEquiv r (block, k)) outcome =
      pauliBornProbability
        (qubitFrameCoordinates (selected.frame pilot) theta) k outcome := by
  cases outcome <;>
    simp [mixedTwoStageFinalBornProbability, mixedTwoStageFinalAxis,
      pauliBornProbability, qubitFrameCoordinates] <;>
    rfl

/-- Conditional product masses coincide atom by atom under the final-path
bijection. -/
theorem mixedTwoStageConditionalFinalPathMass_eq_pauliPilotPathMass
    {q : ℕ} (r : ℕ) (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q)
    (finalPath : MixedTwoStageFinalPath (3 * r)) :
    mixedTwoStageConditionalFinalPathMass
        theta selected pilot finalPath =
      pauliPilotPathMass
        (qubitFrameCoordinates (selected.frame pilot) theta)
        (mixedTwoStageFinalPathPauliEquiv r finalPath) := by
  unfold mixedTwoStageConditionalFinalPathMass
  calc
    (∏ t : Fin (3 * r),
      mixedTwoStageFinalBornProbability
        theta selected pilot t (finalPath t)) =
      ∏ p : Fin r × Fin 3,
        mixedTwoStageFinalBornProbability theta selected pilot
          (mixedTwoStageExactCycleEquiv r p)
          (finalPath (mixedTwoStageExactCycleEquiv r p)) := by
      exact (Fintype.prod_equiv (mixedTwoStageExactCycleEquiv r)
        (fun p : Fin r × Fin 3 =>
          mixedTwoStageFinalBornProbability theta selected pilot
            (mixedTwoStageExactCycleEquiv r p)
            (finalPath (mixedTwoStageExactCycleEquiv r p)))
        (fun t : Fin (3 * r) =>
          mixedTwoStageFinalBornProbability
            theta selected pilot t (finalPath t))
        (fun _ => rfl)).symm
    _ = ∏ block : Fin r, ∏ k : Fin 3,
        mixedTwoStageFinalBornProbability theta selected pilot
          (mixedTwoStageExactCycleEquiv r (block, k))
          (finalPath (mixedTwoStageExactCycleEquiv r (block, k))) := by
      rw [Fintype.prod_prod_type]
    _ = ∏ block : Fin r, ∏ k : Fin 3,
        pauliBornProbability
          (qubitFrameCoordinates (selected.frame pilot) theta) k
          (mixedTwoStageFinalPathPauliEquiv r finalPath block k) := by
      apply Finset.prod_congr rfl
      intro block _
      apply Finset.prod_congr rfl
      intro k _
      exact mixedTwoStageFinalBornProbability_exactCycle
        r theta selected pilot block k _
    _ = pauliPilotPathMass
        (qubitFrameCoordinates (selected.frame pilot) theta)
        (mixedTwoStageFinalPathPauliEquiv r finalPath) := by
      simp [pauliPilotPathMass, pauliPilotBlockMass]

/-! ## Estimator and quadratic-loss transport -/

/-- The three cyclic signed sample means, expressed on the established
complete-block sample space. -/
def mixedTwoStageExactCycleSignedMeans
    (r : ℕ) (finalPath : MixedTwoStageFinalPath (3 * r)) : RLSVector 3 :=
  pauliPilotEstimate (mixedTwoStageFinalPathPauliEquiv r finalPath)

/-- Linear reconstruction from the cyclic final path and the pilot-selected
frame. -/
def mixedTwoStageExactCycleLinearEstimator
    {q : ℕ} (r : ℕ) (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q)
    (finalPath : MixedTwoStageFinalPath (3 * r)) : RLSVector 3 :=
  mixedFrameReconstruct (selected.frame pilot)
    (mixedTwoStageExactCycleSignedMeans r finalPath)

/-- The explicit cyclic estimator is exactly the existing frame linear
estimator after transport by the path equivalence. -/
theorem mixedTwoStageExactCycleLinearEstimator_eq_mixedFrameLinearEstimate
    {q : ℕ} (r : ℕ) (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q)
    (finalPath : MixedTwoStageFinalPath (3 * r)) :
    mixedTwoStageExactCycleLinearEstimator r selected pilot finalPath =
      mixedFrameLinearEstimate (selected.frame pilot)
        (mixedTwoStageFinalPathPauliEquiv r finalPath) :=
  rfl

/-- Interior mixed-qubit quadratic loss of the explicit cyclic estimator. -/
def mixedTwoStageExactCycleQuadraticLoss
    {q : ℕ} (r : ℕ) (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q)
    (finalPath : MixedTwoStageFinalPath (3 * r)) : ℝ :=
  mixedInteriorBuresQuadraticLoss theta
    (fun i =>
      mixedTwoStageExactCycleLinearEstimator
        r selected pilot finalPath i - theta i)

/-- Quadratic loss is preserved exactly by the final-path equivalence. -/
theorem mixedTwoStageExactCycleQuadraticLoss_eq_mixedFrame
    {q : ℕ} (r : ℕ) (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q)
    (finalPath : MixedTwoStageFinalPath (3 * r)) :
    mixedTwoStageExactCycleQuadraticLoss
        r theta selected pilot finalPath =
      mixedInteriorBuresQuadraticLoss theta
        (fun i => mixedFrameLinearEstimate (selected.frame pilot)
          (mixedTwoStageFinalPathPauliEquiv r finalPath) i - theta i) :=
  rfl

/-! ## Conditional and joint finite-row identities -/

/-- Conditional scaled quadratic risk computed directly from the explicit
length-`3 * r` cyclic product law. -/
def mixedTwoStageExactCycleConditionalScaledQuadraticRisk
    {q : ℕ} (r : ℕ) (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) : ℝ :=
  (3 * (r : ℝ)) *
    ∑ finalPath : MixedTwoStageFinalPath (3 * r),
      mixedTwoStageConditionalFinalPathMass
          theta selected pilot finalPath *
        mixedTwoStageExactCycleQuadraticLoss
          r theta selected pilot finalPath

/-- The explicit conditional product-law risk is exactly the established
`mixedFrameConditionalScaledQuadraticRisk`. -/
theorem mixedTwoStageExactCycleConditionalScaledQuadraticRisk_eq_mixedFrame
    {q : ℕ} (r : ℕ) (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) :
    mixedTwoStageExactCycleConditionalScaledQuadraticRisk
        r theta selected pilot =
      mixedFrameConditionalScaledQuadraticRisk (q := r) theta
        (selected.frame pilot) := by
  unfold mixedTwoStageExactCycleConditionalScaledQuadraticRisk
    mixedFrameConditionalScaledQuadraticRisk
    mixedFrameConditionalQuadraticRisk pauliPilotFiniteExpectation
  apply congrArg (fun x : ℝ => (3 * (r : ℝ)) * x)
  exact Fintype.sum_equiv (mixedTwoStageFinalPathPauliEquiv r)
    (fun finalPath : MixedTwoStageFinalPath (3 * r) =>
      mixedTwoStageConditionalFinalPathMass
          theta selected pilot finalPath *
        mixedTwoStageExactCycleQuadraticLoss
          r theta selected pilot finalPath)
    (fun path : PauliPilotPath r =>
      pauliPilotPathMass
          (qubitFrameCoordinates (selected.frame pilot) theta) path *
        mixedInteriorBuresQuadraticLoss theta
          (fun i => mixedFrameLinearEstimate (selected.frame pilot) path i -
            theta i))
    (fun finalPath => by
      rw [mixedTwoStageConditionalFinalPathMass_eq_pauliPilotPathMass]
      rfl)

/-- Scaled quadratic loss assigned to one explicit finite-row atom. -/
def mixedTwoStageFiniteRowScaledQuadraticLoss
    {q r : ℕ} (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q)
    (row : MixedTwoStageFiniteRow q (3 * r)) : ℝ :=
  (3 * (r : ℝ)) *
    mixedTwoStageExactCycleQuadraticLoss
      r theta selected row.1 row.2

/-- On one pilot fiber, summing joint atom mass times scaled loss gives the
pilot mass times the established conditional scaled risk. -/
theorem mixedTwoStageFiniteRow_scaledQuadraticLoss_pilotFiber
    {q : ℕ} (r : ℕ) (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) :
    (∑ finalPath : MixedTwoStageFinalPath (3 * r),
      mixedTwoStageFiniteRowMass theta selected (pilot, finalPath) *
        mixedTwoStageFiniteRowScaledQuadraticLoss
          theta selected (pilot, finalPath)) =
      pauliPilotPathMass theta pilot *
        mixedFrameConditionalScaledQuadraticRisk (q := r) theta
          (selected.frame pilot) := by
  rw [← mixedTwoStageExactCycleConditionalScaledQuadraticRisk_eq_mixedFrame]
  unfold mixedTwoStageFiniteRowMass
    mixedTwoStageFiniteRowScaledQuadraticLoss
    mixedTwoStageExactCycleConditionalScaledQuadraticRisk
  calc
    (∑ finalPath : MixedTwoStageFinalPath (3 * r),
      (pauliPilotPathMass theta pilot *
          mixedTwoStageConditionalFinalPathMass
            theta selected pilot finalPath) *
        ((3 * (r : ℝ)) *
          mixedTwoStageExactCycleQuadraticLoss
            r theta selected pilot finalPath)) =
      ∑ finalPath : MixedTwoStageFinalPath (3 * r),
        (pauliPilotPathMass theta pilot * (3 * (r : ℝ))) *
          (mixedTwoStageConditionalFinalPathMass
              theta selected pilot finalPath *
            mixedTwoStageExactCycleQuadraticLoss
              r theta selected pilot finalPath) := by
        apply Finset.sum_congr rfl
        intro finalPath _
        ring
    _ = (pauliPilotPathMass theta pilot * (3 * (r : ℝ))) *
        ∑ finalPath : MixedTwoStageFinalPath (3 * r),
          mixedTwoStageConditionalFinalPathMass
              theta selected pilot finalPath *
            mixedTwoStageExactCycleQuadraticLoss
              r theta selected pilot finalPath := by
      rw [Finset.mul_sum]
    _ = pauliPilotPathMass theta pilot *
        ((3 * (r : ℝ)) *
          ∑ finalPath : MixedTwoStageFinalPath (3 * r),
            mixedTwoStageConditionalFinalPathMass
                theta selected pilot finalPath *
              mixedTwoStageExactCycleQuadraticLoss
                r theta selected pilot finalPath) := by
      ring

/-- Summing over all explicit joint finite-row atoms gives the exact finite
pilot average of the conditional scaled quadratic risk. -/
theorem mixedTwoStageFiniteRow_scaledQuadraticRisk_eq_pilotAverage
    {q : ℕ} (r : ℕ) (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q) :
    (∑ row : MixedTwoStageFiniteRow q (3 * r),
      mixedTwoStageFiniteRowMass theta selected row *
        mixedTwoStageFiniteRowScaledQuadraticLoss theta selected row) =
      pauliPilotFiniteExpectation theta
        (fun pilot =>
          mixedFrameConditionalScaledQuadraticRisk (q := r) theta
            (selected.frame pilot)) := by
  rw [Fintype.sum_prod_type]
  unfold pauliPilotFiniteExpectation
  apply Finset.sum_congr rfl
  intro pilot _
  exact mixedTwoStageFiniteRow_scaledQuadraticLoss_pilotFiber
    r theta selected pilot

/-! ## Concrete safeguarded pilot controller -/

/-- The safeguarded local frame selected from the finite Pauli pilot is a
`PilotSelectedFinalFrame`. -/
def mixedPilotLocalSelectedFinalFrame
    (q : ℕ) (b : RLSVector 3) : PilotSelectedFinalFrame q where
  frame pilot := mixedPilotSelectedLocalFrame b (pauliPilotEstimate pilot)
  axis_unit pilot k := by
    change blochNormSq
      (qubitFrameAxis
        (mixedPilotSelectedLocalFrame b (pauliPilotEstimate pilot)) k) = 1
    exact mixedPilotSelectedLocalFrame_axis_unit
      b (pauliPilotEstimate pilot) k
  axes_orthogonal pilot k l := by
    change blochDot
      (qubitFrameAxis
        (mixedPilotSelectedLocalFrame b (pauliPilotEstimate pilot)) k)
      (qubitFrameAxis
        (mixedPilotSelectedLocalFrame b (pauliPilotEstimate pilot)) l) =
      if k = l then 1 else 0
    exact mixedPilotSelectedLocalFrame_axes_orthogonal
      b (pauliPilotEstimate pilot) k l

/-- The finite-row statement matching the role of a final joint-law premise. -/
def MixedPilotFiniteRowFinalJointLaw
    {q : ℕ} (r : ℕ) (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q) : Prop :=
  (∑ row : MixedTwoStageFiniteRow q (3 * r),
    mixedTwoStageFiniteRowMass theta selected row *
      mixedTwoStageFiniteRowScaledQuadraticLoss theta selected row) =
    pauliPilotFiniteExpectation theta
      (fun pilot =>
        mixedFrameConditionalScaledQuadraticRisk (q := r) theta
          (selected.frame pilot))

/-- The exact finite-row joint law is proved for every pilot-selected frame. -/
theorem mixedPilotFiniteRowFinalJointLaw
    {q : ℕ} (r : ℕ) (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q) :
    MixedPilotFiniteRowFinalJointLaw r theta selected :=
  mixedTwoStageFiniteRow_scaledQuadraticRisk_eq_pilotAverage
    r theta selected

/-- Concrete specialization to the safeguarded local frame selected from the
finite Pauli pilot. -/
theorem mixedPilotLocalFiniteRowFinalJointLaw
    (q r : ℕ) (theta b : RLSVector 3) :
    MixedPilotFiniteRowFinalJointLaw r theta
      (mixedPilotLocalSelectedFinalFrame q b) :=
  mixedPilotFiniteRowFinalJointLaw
    r theta (mixedPilotLocalSelectedFinalFrame q b)

namespace Label

/-- Paper-facing exact finite-row final-estimator law.  This is deliberately
named as a finite-row reduction rather than the common-space asymptotic law. -/
theorem lem_SI_mixed_two_stage_final_estimator_law_finite_row_qubit
    (q r : ℕ) (theta b : RLSVector 3) :
    MixedPilotFiniteRowFinalJointLaw r theta
      (mixedPilotLocalSelectedFinalFrame q b) :=
  mixedPilotLocalFiniteRowFinalJointLaw q r theta b

end Label

end

end QubitOracle.Paper
