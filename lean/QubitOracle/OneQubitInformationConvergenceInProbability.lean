import QubitOracle.Paper.OneQubitLocalFrameDomainClosure

/-!
# One-qubit information convergence in probability

This source candidate works on one common probability space.  It does not use
a triangular array.  Convergence in probability is encoded by the explicit
epsilon-tail predicate below, so the probability-library boundary is visible.

The concrete part is proved here: every deterministic coordinatewise
convergent realization eventually enters the safeguarded local-frame domain,
the resulting controller converges entrywise to its fixed oracle frame, and
the mixed and pure per-observation information entries converge to the exact
fixed-design limits.  The sole remaining probability premise is a generic
finite-coordinate continuous-mapping principle, represented as a `Prop`, not
as an axiom and not as either desired information-convergence conclusion.
-/

open Filter MeasureTheory

namespace QubitOracle

open Paper

/-! ## Explicit convergence-in-probability predicates -/

/-- Epsilon-tail convergence in probability for real random variables on one
fixed measure space. -/
def EpsilonConvergesInProbability
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (x : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n => μ {ω | ε ≤ |X n ω - x|}) atTop (nhds 0)

/-- Coordinatewise convergence in probability of a three-dimensional Bloch
estimator on the same probability space for every sample size. -/
def BlochCoordinatewiseConvergesInProbability
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (xHat : ℕ → Ω → Fin 3 → ℝ) (x : Fin 3 → ℝ) : Prop :=
  ∀ k : Fin 3,
    EpsilonConvergesInProbability μ (fun n ω => xHat n ω k) (x k)

/-- Entrywise convergence in probability for a fixed finite square matrix. -/
def MatrixEntrywiseEpsilonConvergesInProbability
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (μ : Measure Ω)
    (M : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ)
    (limit : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∀ i j : Fin d,
    EpsilonConvergesInProbability μ (fun n ω => M n ω i j) (limit i j)

/-! ## Exact event-inclusion reduction -/

/-- The scalar output epsilon-bad event. -/
def scalarEpsilonBadEvent
    {Ω : Type*} {d : ℕ} (X : ℕ → Ω → Fin d → ℝ)
    (F : (Fin d → ℝ) → ℝ) (y : ℝ) (n : ℕ) (ε : ℝ) : Set Ω :=
  {ω | ε ≤ |F (X n ω) - y|}

/-- Failure of a common coordinatewise delta bound. -/
def coordinateDeltaBadEvent
    {Ω : Type*} {d : ℕ} (X : ℕ → Ω → Fin d → ℝ)
    (x : Fin d → ℝ) (n : ℕ) (δ : ℝ) : Set Ω :=
  {ω | ∃ k : Fin d, δ ≤ |X n ω k - x k|}

/-- A deterministic local epsilon-delta bound gives the exact bad-event
inclusion used by the finite union-bound proof of the continuous-mapping
theorem. -/
theorem scalarEpsilonBadEvent_subset_coordinateDeltaBadEvent
    {Ω : Type*} {d : ℕ} (X : ℕ → Ω → Fin d → ℝ)
    (x : Fin d → ℝ) (F : (Fin d → ℝ) → ℝ) (y : ℝ)
    (n : ℕ) (ε δ : ℝ)
    (hControl : ∀ z : Fin d → ℝ,
      (∀ k, |z k - x k| < δ) → |F z - y| < ε) :
    scalarEpsilonBadEvent X F y n ε ⊆
      coordinateDeltaBadEvent X x n δ := by
  intro ω hBad
  change ε ≤ |F (X n ω) - y| at hBad
  change ∃ k : Fin d, δ ≤ |X n ω k - x k|
  by_contra hNoCoordinate
  have hClose : ∀ k : Fin d, |X n ω k - x k| < δ := by
    intro k
    exact lt_of_not_ge (fun hk => hNoCoordinate ⟨k, hk⟩)
  exact (not_lt_of_ge hBad) (hControl (X n ω) hClose)

/-- The corresponding probability inequality; no measurability side
condition is needed for monotonicity of a measure. -/
theorem measure_scalarEpsilonBadEvent_le_coordinateDeltaBadEvent
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (μ : Measure Ω)
    (X : ℕ → Ω → Fin d → ℝ)
    (x : Fin d → ℝ) (F : (Fin d → ℝ) → ℝ) (y : ℝ)
    (n : ℕ) (ε δ : ℝ)
    (hControl : ∀ z : Fin d → ℝ,
      (∀ k, |z k - x k| < δ) → |F z - y| < ε) :
    μ (scalarEpsilonBadEvent X F y n ε) ≤
      μ (coordinateDeltaBadEvent X x n δ) :=
  measure_mono
    (scalarEpsilonBadEvent_subset_coordinateDeltaBadEvent
      X x F y n ε δ hControl)

/-! ## Honest generic probability boundary -/

/-- Exact contract for the standard finite-dimensional continuous-mapping
theorem in probability.  Its analytic premise is sequential coordinatewise
continuity at one fixed point.  The conclusion is the explicit epsilon-tail
predicate above.  This contract is a `Prop` parameter awaiting a direct
Mathlib probability proof; it is not an axiom. -/
def FiniteCoordinateContinuousMappingProbabilityContract
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) : Prop :=
  ∀ {d : ℕ} (X : ℕ → Ω → Fin d → ℝ) (x : Fin d → ℝ)
      (F : (Fin d → ℝ) → ℝ) (y : ℝ),
    (∀ z : ℕ → Fin d → ℝ,
      (∀ k, Tendsto (fun n => z n k) atTop (nhds (x k))) →
        Tendsto (fun n => F (z n)) atTop (nhds y)) →
    (∀ k, EpsilonConvergesInProbability μ
      (fun n ω => X n ω k) (x k)) →
    EpsilonConvergesInProbability μ (fun n ω => F (X n ω)) y

/-! ## A positive-denominator local pilot -/

/-- The local safeguarded controller needs only positivity of its two truth
denominators.  Unit norm is unnecessary for the mixed interior branch. -/
noncomputable def localContinuousFramePilot_of_positive_denominators
    (b r : Fin 3 → ℝ) (x : ℕ → Fin 3 → ℝ)
    (hRadialPositive : 0 < blochNormSq r)
    (hTangentPositive : 0 < blochNormSq (localFrameFirstResidual b r))
    (hx : ∀ i, Tendsto (fun n => x n i) atTop (nhds (r i))) :
    QubitPilotFrameConvergence r := by
  let hTruthDomain : LocalContinuousFrameDomain b r :=
    { radial_denominator_pos := hRadialPositive
      tangent_denominator_pos := hTangentPositive }
  have hEventuallyDomain :
      ∀ᶠ n in atTop, LocalContinuousFrameDomain b (x n) :=
    eventually_localContinuousFrameDomain b hx hRadialPositive
      hTangentPositive
  exact
    { estimatedFrame := fun n =>
        safeguardedLocalContinuousControllerFrame b r (x n)
      axis_unit := fun n k =>
        safeguardedLocalContinuousControllerFrame_axis_unit
          hTruthDomain k
      axes_orthogonal := fun n k l =>
        safeguardedLocalContinuousControllerFrame_axes_orthogonal
          hTruthDomain k l
      entry_tendsto := fun i k =>
        safeguardedLocalContinuousControllerFrame_entry_tendsto
          b x r hx hTruthDomain hEventuallyDomain i k }

/-! ## Concrete per-observation information maps -/

/-- Mixed complete-block information divided by its three observations, using
the total safeguarded local controller. -/
noncomputable def mixedLocalSafeguardedPerObservationInformation
    (b theta x : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (1 / 3 : ℝ) • mixedRotatedPauliCompleteBlockFisher theta
    (safeguardedLocalContinuousControllerFrame b theta x)

/-- The fixed mixed oracle matrix at the interior truth. -/
noncomputable def mixedOraclePerObservationInformation
    (theta : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (1 / 3 : ℝ) • mixedRotatedPauliCompleteBlockFisher theta
    (qubitTruthAlignedHouseholderFrame theta)

/-- Pure tangent-block information divided by its two observations, using the
same total safeguarded local controller. -/
noncomputable def pureLocalSafeguardedPerObservationInformation
    (b r x : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / 2 : ℝ) • pureRotatedTangentCompleteBlockFisher r
    (safeguardedLocalContinuousControllerFrame b r x)

/-- The exact pure fixed-design oracle matrix, equal to `2 I_2` at a unit
truth by the clean fixed-design calculation. -/
noncomputable def pureOraclePerObservationInformation
    (r : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / 2 : ℝ) • pureTruthCompleteBlockFisher r

/-! ## Deterministic continuous-mapping inputs -/

/-- Every deterministic coordinatewise-convergent mixed realization has the
required per-observation information-entry limit.  No information convergence
is assumed. -/
theorem mixedLocalSafeguardedPerObservationInformation_entry_tendsto
    (b theta : Fin 3 → ℝ) (x : ℕ → Fin 3 → ℝ)
    (hx : ∀ k, Tendsto (fun n => x n k) atTop (nhds (theta k)))
    (hInterior : blochNormSq theta < 1)
    (hRadialPositive : 0 < blochNormSq theta)
    (hTangentPositive :
      0 < blochNormSq (localFrameFirstResidual b theta))
    (i j : Fin 3) :
    Tendsto
      (fun n => mixedLocalSafeguardedPerObservationInformation
        b theta (x n) i j)
      atTop (nhds (mixedOraclePerObservationInformation theta i j)) := by
  let pilot : QubitPilotFrameConvergence theta :=
    localContinuousFramePilot_of_positive_denominators
      b theta x hRadialPositive hTangentPositive hx
  have hInformation :=
    mixedRotatedPauliPerObservationInformation_tendsto
      pilot theta hInterior
  simpa [mixedLocalSafeguardedPerObservationInformation,
    mixedOraclePerObservationInformation, pilot,
    localContinuousFramePilot_of_positive_denominators] using
      (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hInformation i) j)

/-- Every deterministic coordinatewise-convergent pure realization has the
exact `2 I_2` per-observation information-entry limit. -/
theorem pureLocalSafeguardedPerObservationInformation_entry_tendsto
    (b r : Fin 3 → ℝ) (x : ℕ → Fin 3 → ℝ)
    (hx : ∀ k, Tendsto (fun n => x n k) atTop (nhds (r k)))
    (hTruthUnit : blochNormSq r = 1)
    (hRadialPositive : 0 < blochNormSq r)
    (hTangentPositive : 0 < blochNormSq (localFrameFirstResidual b r))
    (i j : Fin 2) :
    Tendsto
      (fun n => pureLocalSafeguardedPerObservationInformation
        b r (x n) i j)
      atTop (nhds (pureOraclePerObservationInformation r i j)) := by
  let pilot : QubitPilotFrameConvergence r :=
    localContinuousFramePilot_of_positive_denominators
      b r x hRadialPositive hTangentPositive hx
  have hInformation :=
    pureRotatedTangentPerObservationInformation_tendsto
      hTruthUnit pilot
  simpa [pureLocalSafeguardedPerObservationInformation,
    pureOraclePerObservationInformation, pilot,
    localContinuousFramePilot_of_positive_denominators] using
      (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hInformation i) j)

/-! ## Entrywise convergence in probability -/

/-- Concrete mixed continuous-mapping reduction on one probability space.
The generic contract is the only probability premise. -/
theorem mixedLocalInformation_entrywise_convergesInProbability
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (hCMT : FiniteCoordinateContinuousMappingProbabilityContract μ)
    (b theta : Fin 3 → ℝ) (xHat : ℕ → Ω → Fin 3 → ℝ)
    (hx : BlochCoordinatewiseConvergesInProbability μ xHat theta)
    (hInterior : blochNormSq theta < 1)
    (hRadialPositive : 0 < blochNormSq theta)
    (hTangentPositive :
      0 < blochNormSq (localFrameFirstResidual b theta)) :
    MatrixEntrywiseEpsilonConvergesInProbability μ
      (fun n ω => mixedLocalSafeguardedPerObservationInformation
        b theta (xHat n ω))
      (mixedOraclePerObservationInformation theta) := by
  intro i j
  apply hCMT xHat theta
      (fun x => mixedLocalSafeguardedPerObservationInformation
        b theta x i j)
      (mixedOraclePerObservationInformation theta i j)
  · intro z hz
    exact mixedLocalSafeguardedPerObservationInformation_entry_tendsto
      b theta z hz hInterior hRadialPositive hTangentPositive i j
  · exact hx

/-- Concrete pure continuous-mapping reduction on the same kind of fixed
probability space. -/
theorem pureLocalInformation_entrywise_convergesInProbability
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (hCMT : FiniteCoordinateContinuousMappingProbabilityContract μ)
    (b r : Fin 3 → ℝ) (xHat : ℕ → Ω → Fin 3 → ℝ)
    (hx : BlochCoordinatewiseConvergesInProbability μ xHat r)
    (hTruthUnit : blochNormSq r = 1)
    (hRadialPositive : 0 < blochNormSq r)
    (hTangentPositive : 0 < blochNormSq (localFrameFirstResidual b r)) :
    MatrixEntrywiseEpsilonConvergesInProbability μ
      (fun n ω => pureLocalSafeguardedPerObservationInformation
        b r (xHat n ω))
      (pureOraclePerObservationInformation r) := by
  intro i j
  apply hCMT xHat r
      (fun x => pureLocalSafeguardedPerObservationInformation b r x i j)
      (pureOraclePerObservationInformation r i j)
  · intro z hz
    exact pureLocalSafeguardedPerObservationInformation_entry_tendsto
      b r z hz hTruthUnit hRadialPositive hTangentPositive i j
  · exact hx

namespace Label

/-- Combined one-space mixed/pure information-convergence reduction.  Neither
conclusion occurs among the premises. -/
theorem eq_SI_information_convergence_in_probability_qubit_reduction
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (hCMT : FiniteCoordinateContinuousMappingProbabilityContract μ)
    (mixedSeed pureSeed mixedTruth pureTruth : Fin 3 → ℝ)
    (mixedHat pureHat : ℕ → Ω → Fin 3 → ℝ)
    (hMixedEstimator :
      BlochCoordinatewiseConvergesInProbability μ mixedHat mixedTruth)
    (hPureEstimator :
      BlochCoordinatewiseConvergesInProbability μ pureHat pureTruth)
    (hMixedInterior : blochNormSq mixedTruth < 1)
    (hMixedRadialPositive : 0 < blochNormSq mixedTruth)
    (hMixedTangentPositive :
      0 < blochNormSq
        (localFrameFirstResidual mixedSeed mixedTruth))
    (hPureUnit : blochNormSq pureTruth = 1)
    (hPureRadialPositive : 0 < blochNormSq pureTruth)
    (hPureTangentPositive :
      0 < blochNormSq
        (localFrameFirstResidual pureSeed pureTruth)) :
    MatrixEntrywiseEpsilonConvergesInProbability μ
        (fun n ω => mixedLocalSafeguardedPerObservationInformation
          mixedSeed mixedTruth (mixedHat n ω))
        (mixedOraclePerObservationInformation mixedTruth) ∧
      MatrixEntrywiseEpsilonConvergesInProbability μ
        (fun n ω => pureLocalSafeguardedPerObservationInformation
          pureSeed pureTruth (pureHat n ω))
        (pureOraclePerObservationInformation pureTruth) := by
  exact ⟨
    mixedLocalInformation_entrywise_convergesInProbability μ hCMT
      mixedSeed mixedTruth mixedHat hMixedEstimator hMixedInterior
      hMixedRadialPositive hMixedTangentPositive,
    pureLocalInformation_entrywise_convergesInProbability μ hCMT
      pureSeed pureTruth pureHat hPureEstimator hPureUnit
      hPureRadialPositive hPureTangentPositive⟩

end Label
end QubitOracle
