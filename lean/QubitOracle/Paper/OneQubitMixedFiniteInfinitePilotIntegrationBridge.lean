import QubitOracle.Paper.OneQubitMixedTwoStageFinalEstimatorLaw
import QubitOracle.Paper.OneQubitPauliPilotConsistency

/-!
# Finite/infinite pilot integration bridge for the mixed-qubit protocol

The common pilot probability space is a countable product whose `n`th
coordinate is the finite Born law with `n + 1` complete Pauli blocks.  This
file transports measurable `ENNReal` observables through that coordinate and
then evaluates the finite integral as an explicit pilot-mass sum.

For the polynomial controller, coordinate `polynomialPilotIndex n` has exactly
`polynomialPilotBlocks n` blocks, while the final row retains the exact horizon
`3 * qFinal n` from the cycle construction.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace QubitOracle.Paper

noncomputable section

local instance mixedFiniteInfiniteBridgePilotPathMeasurableSpace (q : ℕ) :
    MeasurableSpace (PauliPilotPath q) := ⊤

local instance mixedFiniteInfiniteBridgePilotPathMeasurableSingletonClass
    (q : ℕ) : MeasurableSingletonClass (PauliPilotPath q) where
  measurableSet_singleton _ := MeasurableSet.of_discrete

/-! ## Exact coordinate marginal -/

/-- The finite path read by `pauliPilotConsistencyEstimator` at stage `n` has
exactly the `n + 1` block Born product law. -/
theorem pauliPilotConsistencyEstimator_input_marginal
    (theta : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (n : ℕ) :
    (pauliPilotConsistencyMeasure theta).map (Function.eval n) =
      pauliPilotBornProductMeasure (q := Nat.succ n) theta :=
  pauliPilotConsistencyMeasure_map_eval theta hphysical n

/-- The common-space estimator is literally the finite Pauli estimator of its
selected coordinate. -/
@[simp]
theorem pauliPilotConsistencyEstimator_eq_finiteCoordinate
    (n : ℕ) (omega : PauliPilotConsistencySampleSpace) :
    pauliPilotConsistencyEstimator n omega =
      pauliPilotEstimate (omega n) :=
  rfl

/-! ## Finite mass-sum formula and pullback bridge -/

/-- On a finite Pauli path space, the `ENNReal` integral is the explicit sum
of the finite Born atom masses times the observable. -/
theorem lintegral_pauliPilotBornProductMeasure_eq_finiteMassSum
    {q : ℕ} (theta : RLSVector 3)
    (hphysical : PauliPilotPhysicalBloch theta)
    (f : PauliPilotPath q → ℝ≥0∞) :
    (∫⁻ path, f path ∂pauliPilotBornProductMeasure theta) =
      ∑ path : PauliPilotPath q,
        ENNReal.ofReal (pauliPilotPathMass theta path) * f path := by
  rw [lintegral_fintype]
  apply Finset.sum_congr rfl
  intro path _
  rw [pauliPilotBornProductMeasure_apply theta hphysical]
  simp [mul_comm]

/-- Every measurable nonnegative finite-pilot observable has the same integral
when pulled back to the matching coordinate of the common infinite pilot
space, and that integral is the explicit finite mass sum. -/
theorem lintegral_pauliPilotConsistency_pullback_eq_finiteMassSum
    (theta : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (n : ℕ) (f : PauliPilotPath (Nat.succ n) → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ omega, f (omega n) ∂pauliPilotConsistencyMeasure theta) =
      ∑ path : PauliPilotPath (Nat.succ n),
        ENNReal.ofReal (pauliPilotPathMass theta path) * f path := by
  calc
    (∫⁻ omega, f (omega n) ∂pauliPilotConsistencyMeasure theta) =
      ∫⁻ path, f path ∂
        (pauliPilotConsistencyMeasure theta).map (Function.eval n) := by
          exact (lintegral_map hf (measurable_pi_apply n)).symm
    _ = ∫⁻ path, f path ∂
        pauliPilotBornProductMeasure (q := Nat.succ n) theta := by
          rw [pauliPilotConsistencyEstimator_input_marginal
            theta hphysical n]
    _ = ∑ path : PauliPilotPath (Nat.succ n),
        ENNReal.ofReal (pauliPilotPathMass theta path) * f path :=
      lintegral_pauliPilotBornProductMeasure_eq_finiteMassSum
        theta hphysical f

/-! ## Conditional-risk specialization -/

/-- Specialization of the bridge to the `ENNReal` form of the conditional
scaled quadratic risk for an arbitrary finite pilot-selected frame. -/
theorem lintegral_pauliPilotConsistency_conditionalScaledRisk_eq_finiteMassSum
    (theta : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (n r : ℕ) (selected : PilotSelectedFinalFrame (Nat.succ n)) :
    (∫⁻ omega,
      ENNReal.ofReal
        (mixedFrameConditionalScaledQuadraticRisk (q := r) theta
          (selected.frame (omega n)))
      ∂pauliPilotConsistencyMeasure theta) =
      ∑ pilot : PauliPilotPath (Nat.succ n),
        ENNReal.ofReal (pauliPilotPathMass theta pilot) *
          ENNReal.ofReal
            (mixedFrameConditionalScaledQuadraticRisk (q := r) theta
              (selected.frame pilot)) := by
  exact lintegral_pauliPilotConsistency_pullback_eq_finiteMassSum
    theta hphysical n
    (fun pilot =>
      ENNReal.ofReal
        (mixedFrameConditionalScaledQuadraticRisk (q := r) theta
          (selected.frame pilot)))
    Measurable.of_discrete

/-- The polynomial row uses exactly the scheduled number of complete pilot
blocks.  This records the absence of an off-by-one schedule mismatch. -/
theorem mixedPolynomialFinitePilot_coordinateBlockCount (n : ℕ) :
    Nat.succ (polynomialPilotIndex n) = polynomialPilotBlocks n :=
  polynomialPilotIndex_succ n

/-- Explicit finite-pilot average of the conditional scaled risk in polynomial
row `n`.  This is an `ENNReal` finite mass sum, not an assumed adaptive law. -/
def mixedPolynomialFinitePilotAverageScaledRisk
    (theta b : RLSVector 3) (qFinal : ℕ → ℕ) (n : ℕ) : ℝ≥0∞ :=
  ∑ pilot : PauliPilotPath (Nat.succ (polynomialPilotIndex n)),
    ENNReal.ofReal (pauliPilotPathMass theta pilot) *
      ENNReal.ofReal
        (mixedFrameConditionalScaledQuadraticRisk (q := qFinal n) theta
          (mixedPilotSelectedLocalFrame b (pauliPilotEstimate pilot)))

/-- The explicit finite-pilot average is exactly the common-space integral of
the existing polynomial conditional scaled loss. -/
theorem mixedPolynomialFinitePilotAverageScaledRisk_eq_lintegral
    (theta b : RLSVector 3) (qFinal : ℕ → ℕ)
    (hphysical : PauliPilotPhysicalBloch theta) (n : ℕ) :
    mixedPolynomialFinitePilotAverageScaledRisk theta b qFinal n =
      ∫⁻ omega,
        mixedPolynomialPilotConditionalScaledLoss theta b qFinal n omega
        ∂pauliPilotConsistencyMeasure theta := by
  have hBridge :=
    lintegral_pauliPilotConsistency_pullback_eq_finiteMassSum
      theta hphysical (polynomialPilotIndex n)
      (fun pilot : PauliPilotPath (Nat.succ (polynomialPilotIndex n)) =>
        ENNReal.ofReal
          (mixedFrameConditionalScaledQuadraticRisk (q := qFinal n) theta
            (mixedPilotSelectedLocalFrame b (pauliPilotEstimate pilot))))
      Measurable.of_discrete
  simpa [mixedPolynomialFinitePilotAverageScaledRisk,
    mixedPolynomialPilotConditionalScaledLoss, polynomialPilotEstimator,
    pauliPilotConsistencyEstimator] using hBridge.symm

/-! ## Exact polynomial specialization of the joint-law contract -/

/-- At every polynomial row, the finite exact-cycle experiment has final
horizon `3 * qFinal n` and the same finite pilot coordinate used by the
integration bridge. -/
theorem mixedPolynomialExactCycleFiniteRowJointLaw
    (theta b : RLSVector 3) (qFinal : ℕ → ℕ) (n : ℕ) :
    MixedPilotFiniteRowFinalJointLaw (qFinal n) theta
      (mixedPilotLocalSelectedFinalFrame
        (Nat.succ (polynomialPilotIndex n)) b) :=
  mixedPilotLocalFiniteRowFinalJointLaw
    (Nat.succ (polynomialPilotIndex n)) (qFinal n) theta b

/-- The existing common-space `MixedPilotFinalJointLawPremise` is instantiated
by the explicit finite-pilot mass average, with no probability or integration
premise left over. -/
theorem mixedPolynomialFinitePilotAverage_finalJointLawPremise
    (theta b : RLSVector 3) (qFinal : ℕ → ℕ)
    (hphysical : PauliPilotPhysicalBloch theta) :
    MixedPilotFinalJointLawPremise theta b qFinal
      (mixedPolynomialFinitePilotAverageScaledRisk theta b qFinal) := by
  unfold MixedPilotFinalJointLawPremise
  intro n
  exact mixedPolynomialFinitePilotAverageScaledRisk_eq_lintegral
    theta b qFinal hphysical n

namespace Label

/-- Paper-facing finite/infinite pilot integration bridge and exact polynomial
specialization of the common-space final-law contract. -/
theorem lem_SI_mixed_finite_infinite_pilot_integration_bridge_qubit
    (theta b : RLSVector 3) (qFinal : ℕ → ℕ)
    (hphysical : PauliPilotPhysicalBloch theta) :
    MixedPilotFinalJointLawPremise theta b qFinal
      (mixedPolynomialFinitePilotAverageScaledRisk theta b qFinal) :=
  mixedPolynomialFinitePilotAverage_finalJointLawPremise
    theta b qFinal hphysical

end Label

end

end QubitOracle.Paper
