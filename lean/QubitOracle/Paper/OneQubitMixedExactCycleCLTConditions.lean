import QubitOracle.Paper.OneQubitMixedTwoStageFiniteScore
import QubitOracle.Paper.OneQubitMixedExactCycleObservedInformationLLN

/-!
# Exact-cycle scalar CLT conditions for the mixed qubit

This module packages the final-stage score of the concrete two-stage qubit
experiment as a scalar triangular array with varying finite pilot and final
sample spaces.  All row calculations use the explicit finite masses.  The
only asymptotic premise left as a parameter is convergence in probability of
the explicit pilot-dependent normalized Fisher expression to a chosen scalar
target variance.

No Gaussian convergence theorem is stated or invoked.  In particular, this
file does not import the polynomial-information module.
-/

open scoped BigOperators

namespace QubitOracle.Paper

open Filter Set

noncomputable section

/-- Concrete scalar triangular-array data for exact-cycle final scores.

For row `r`, the pilot space is `PauliPilotPath (pilotLength r)`, the final
space is `Fin (3*r) -> Bool`, and their product carries the explicit two-stage
Born mass.  The selected frame may depend on the completed pilot, while
`targetVariance` is the scalar variance appearing in the proposed Gaussian
limit. -/
structure MixedExactCycleScalarTriangularArrayData where
  pilotLength : ℕ -> ℕ
  theta : Fin 3 -> ℝ
  direction : Fin 3 -> ℝ
  selected : ∀ r : ℕ, PilotSelectedFinalFrame (pilotLength r)
  targetVariance : ℝ
  targetVariance_nonnegative : 0 ≤ targetVariance
  interior : QubitOracle.blochNormSq theta < 1

namespace MixedExactCycleScalarTriangularArrayData

/-- Varying finite pilot space in row `r`. -/
abbrev PilotSpace
    (A : MixedExactCycleScalarTriangularArrayData) (r : ℕ) :=
  PauliPilotPath (A.pilotLength r)

/-- Varying finite final binary path space in row `r`. -/
abbrev FinalSpace
    (_A : MixedExactCycleScalarTriangularArrayData) (r : ℕ) :=
  MixedTwoStageFinalPath (3 * r)

/-- Varying finite joint row space. -/
abbrev RowSpace
    (A : MixedExactCycleScalarTriangularArrayData) (r : ℕ) :=
  MixedTwoStageFiniteRow (A.pilotLength r) (3 * r)

/-- Explicit joint finite-row mass. -/
def jointRowMass
    (A : MixedExactCycleScalarTriangularArrayData) (r : ℕ)
    (row : A.RowSpace r) : ℝ :=
  mixedTwoStageFiniteRowMass A.theta (A.selected r) row

/-- Pilot-selected cyclic axis at one final time. -/
def finalAxis
    (A : MixedExactCycleScalarTriangularArrayData) (r : ℕ)
    (pilot : A.PilotSpace r) (t : Fin (3 * r)) : Fin 3 -> ℝ :=
  mixedTwoStageFinalAxis (A.selected r) pilot t

/-- Normalized scalar final-score increment for a specified one-shot
outcome. -/
def normalizedFinalScoreIncrement
    (A : MixedExactCycleScalarTriangularArrayData) (r : ℕ)
    (pilot : A.PilotSpace r) (t : Fin (3 * r))
    (outcome : Bool) : ℝ :=
  mixedTwoStageFinalShotDirectionalScore
      A.theta A.direction (A.selected r) pilot t outcome /
    Real.sqrt (3 * r : ℕ)

/-- The same increment evaluated on a complete joint row. -/
def rowNormalizedFinalScoreIncrement
    (A : MixedExactCycleScalarTriangularArrayData) (r : ℕ)
    (row : A.RowSpace r) (t : Fin (3 * r)) : ℝ :=
  A.normalizedFinalScoreIncrement r row.1 t (row.2 t)

/-- Pilot-independent deterministic envelope for the maximum absolute
increment in row `r`. -/
def maximumJumpEnvelope
    (A : MixedExactCycleScalarTriangularArrayData) (r : ℕ) : ℝ :=
  mixedProjectedScoreEnvelope A.theta A.direction /
    Real.sqrt (3 * r : ℕ)

/-- Explicit conditional variance sum, given the completed pilot. -/
def conditionalVariance
    (A : MixedExactCycleScalarTriangularArrayData) (r : ℕ)
    (pilot : A.PilotSpace r) : ℝ :=
  ∑ t : Fin (3 * r), ∑ outcome : Bool,
    mixedTwoStageFinalBornProbability
        A.theta (A.selected r) pilot t outcome *
      A.normalizedFinalScoreIncrement r pilot t outcome ^ 2

/-- Explicit normalized Fisher expression, given the completed pilot. -/
def explicitNormalizedFisher
    (A : MixedExactCycleScalarTriangularArrayData) (r : ℕ)
    (pilot : A.PilotSpace r) : ℝ :=
  mixedExactCycleNormalizedDirectionalFisher
    (r := r) A.theta A.direction (A.selected r) pilot

/-- Conditional Lindeberg sum with the stronger closed-tail indicator
`epsilon <= |X_{r,t}|`. -/
def conditionalLindebergSum
    (A : MixedExactCycleScalarTriangularArrayData) (r : ℕ)
    (pilot : A.PilotSpace r) (epsilon : ℝ) : ℝ :=
  ∑ t : Fin (3 * r), ∑ outcome : Bool,
    if epsilon ≤ |A.normalizedFinalScoreIncrement r pilot t outcome| then
      mixedTwoStageFinalBornProbability
          A.theta (A.selected r) pilot t outcome *
        A.normalizedFinalScoreIncrement r pilot t outcome ^ 2
    else 0

/-- Pilot-marginal probability that the explicit normalized Fisher differs
from the target scalar variance by at least `epsilon`. -/
def fisherDeviationProbability
    (A : MixedExactCycleScalarTriangularArrayData)
    (epsilon : ℝ) (r : ℕ) : ℝ :=
  ∑ pilot : A.PilotSpace r,
    if epsilon ≤
        |A.explicitNormalizedFisher r pilot - A.targetVariance| then
      pauliPilotPathMass A.theta pilot
    else 0

/-- Convergence in probability of the only remaining random CLT premise:
the explicit pilot-dependent Fisher sum.  The varying finite pilot spaces are
kept visible through `fisherDeviationProbability`. -/
def FisherConvergesInProbability
    (A : MixedExactCycleScalarTriangularArrayData) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon ->
    Tendsto (A.fisherDeviationProbability epsilon) atTop (nhds 0)

/-! ## Finite-row infrastructure -/

theorem jointRowMass_nonnegative
    (A : MixedExactCycleScalarTriangularArrayData) (r : ℕ)
    (row : A.RowSpace r) :
    0 ≤ A.jointRowMass r row := by
  exact mixedTwoStageFiniteRowMass_nonnegative
    A.theta (A.selected r) (le_of_lt A.interior) row

theorem jointRowMass_sum_one
    (A : MixedExactCycleScalarTriangularArrayData) (r : ℕ) :
    (∑ row : A.RowSpace r, A.jointRowMass r row) = 1 := by
  exact mixedTwoStageFiniteRowMass_sum_one A.theta (A.selected r)

theorem finalAxis_unit
    (A : MixedExactCycleScalarTriangularArrayData) (r : ℕ)
    (pilot : A.PilotSpace r) (t : Fin (3 * r)) :
    QubitOracle.blochNormSq (A.finalAxis r pilot t) = 1 := by
  exact mixedTwoStageFinalAxis_unit (A.selected r) pilot t

/-- The selected axis is measurable as a function of the completed finite
pilot under its discrete sigma algebra. -/
theorem finalAxis_pilotMeasurable
    (A : MixedExactCycleScalarTriangularArrayData) (r : ℕ)
    (t : Fin (3 * r)) :
    @Measurable (A.PilotSpace r) (Fin 3 -> ℝ)
      ⊤ (inferInstance : MeasurableSpace (Fin 3 -> ℝ))
      (fun pilot => A.finalAxis r pilot t) := by
  intro _set _hset
  simp

/-! ## Centering and jump control -/

/-- Item 1: exact conditional score centering for every completed pilot and
every final time. -/
theorem conditionalScoreCentering
    (A : MixedExactCycleScalarTriangularArrayData)
    (r : ℕ) (pilot : A.PilotSpace r) (t : Fin (3 * r)) :
    (∑ outcome : Bool,
      mixedTwoStageFinalBornProbability
          A.theta (A.selected r) pilot t outcome *
        A.normalizedFinalScoreIncrement r pilot t outcome) = 0 := by
  have hmean := mixedTwoStageFinalShotDirectionalScore_bornMean_zero
    A.theta A.direction (A.selected r) A.interior pilot t
  calc
    (∑ outcome : Bool,
      mixedTwoStageFinalBornProbability
          A.theta (A.selected r) pilot t outcome *
        A.normalizedFinalScoreIncrement r pilot t outcome) =
        ∑ outcome : Bool,
          (mixedTwoStageFinalBornProbability
              A.theta (A.selected r) pilot t outcome *
            mixedTwoStageFinalShotDirectionalScore
              A.theta A.direction (A.selected r) pilot t outcome) /
            Real.sqrt (3 * r : ℕ) := by
      apply Finset.sum_congr rfl
      intro outcome _houtcome
      unfold normalizedFinalScoreIncrement
      ring
    _ = (∑ outcome : Bool,
          mixedTwoStageFinalBornProbability
              A.theta (A.selected r) pilot t outcome *
            mixedTwoStageFinalShotDirectionalScore
              A.theta A.direction (A.selected r) pilot t outcome) /
          Real.sqrt (3 * r : ℕ) := by
      rw [Finset.sum_div]
    _ = 0 := by rw [hmean, zero_div]

/-- Every normalized increment is bounded by the deterministic row envelope,
uniformly over pilots, selected frames, times, and outcomes. -/
theorem normalizedFinalScoreIncrement_abs_le_maximumJumpEnvelope
    (A : MixedExactCycleScalarTriangularArrayData)
    (r : ℕ) (hr : 0 < r)
    (pilot : A.PilotSpace r) (t : Fin (3 * r))
    (outcome : Bool) :
    |A.normalizedFinalScoreIncrement r pilot t outcome| ≤
      A.maximumJumpEnvelope r := by
  let finalPath : A.FinalSpace r :=
    fun current => if current = t then outcome else false
  have hbound :=
    mixedExactCycleNormalizedDirectionalScore_abs_le_envelope
      A.theta A.direction (A.selected r) pilot finalPath t
      A.interior hr
  simpa [normalizedFinalScoreIncrement, maximumJumpEnvelope,
    mixedExactCycleNormalizedDirectionalScore,
    mixedTwoStageFinalPathDirectionalScore, finalPath] using hbound

/-- Item 2: the deterministic maximum-jump envelope tends to zero.  Together
with `normalizedFinalScoreIncrement_abs_le_maximumJumpEnvelope`, this is the
precise finite-row meaning of `max_t |X_{r,t}| -> 0`. -/
theorem maximumJumpEnvelope_tendsto_zero
    (A : MixedExactCycleScalarTriangularArrayData) :
    Tendsto A.maximumJumpEnvelope atTop (nhds 0) := by
  change Tendsto
    (fun r : ℕ => mixedProjectedScoreEnvelope A.theta A.direction /
      Real.sqrt (3 * r : ℕ)) atTop (nhds 0)
  exact mixedExactCycleNormalizedEnvelope_tendsto_zero
    A.theta A.direction

/-! ## Lindeberg and conditional variance -/

/-- If the deterministic envelope is below `epsilon`, the entire closed-tail
conditional Lindeberg sum is exactly zero. -/
theorem conditionalLindebergSum_eq_zero_of_envelope_lt
    (A : MixedExactCycleScalarTriangularArrayData)
    (r : ℕ) (hr : 0 < r) (pilot : A.PilotSpace r)
    (epsilon : ℝ) (henvelope : A.maximumJumpEnvelope r < epsilon) :
    A.conditionalLindebergSum r pilot epsilon = 0 := by
  unfold conditionalLindebergSum
  apply Finset.sum_eq_zero
  intro t _ht
  apply Finset.sum_eq_zero
  intro outcome _houtcome
  have hinc := A.normalizedFinalScoreIncrement_abs_le_maximumJumpEnvelope
    r hr pilot t outcome
  have hnot : ¬ epsilon ≤
      |A.normalizedFinalScoreIncrement r pilot t outcome| :=
    not_le_of_gt (lt_of_le_of_lt hinc henvelope)
  simp [hnot]

/-- Item 3: for every positive threshold, the conditional Lindeberg sum is
eventually exactly zero for every completed pilot. -/
theorem conditionalLindebergSum_eventually_zero
    (A : MixedExactCycleScalarTriangularArrayData)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ r : ℕ in atTop,
      0 < r ∧ ∀ pilot : A.PilotSpace r,
        A.conditionalLindebergSum r pilot epsilon = 0 := by
  have hsmall : ∀ᶠ r : ℕ in atTop,
      A.maximumJumpEnvelope r < epsilon :=
    (tendsto_order.1 A.maximumJumpEnvelope_tendsto_zero).2
      epsilon hepsilon
  filter_upwards [eventually_ge_atTop (1 : ℕ), hsmall]
    with r hr henvelope
  refine ⟨hr, ?_⟩
  intro pilot
  exact A.conditionalLindebergSum_eq_zero_of_envelope_lt
    r hr pilot epsilon henvelope

/-- Item 4: the conditional variance sum is exactly the explicit normalized
directional Fisher expression. -/
theorem conditionalVariance_eq_explicitNormalizedFisher
    (A : MixedExactCycleScalarTriangularArrayData)
    (r : ℕ) (hr : 0 < r) (pilot : A.PilotSpace r) :
    A.conditionalVariance r pilot =
      A.explicitNormalizedFisher r pilot := by
  unfold conditionalVariance explicitNormalizedFisher
    mixedExactCycleNormalizedDirectionalFisher
  apply Finset.sum_congr rfl
  intro t _ht
  exact
    mixedExactCycleFinalShotNormalizedSquare_bornExpectation_eq_fisher
      A.theta A.direction (A.selected r) pilot t A.interior hr

/-! ## Hall--Heyde finite-kernel premise package -/

/-- Exact finite-kernel premise package corresponding to Hall and Heyde
(1980), Corollary 3.1.

Field mapping:

* `conditionalScoreCentering` is the rowwise martingale-difference condition
  `E[X_{r,t} | F_{r,t-1}] = 0`, represented here by the exact one-step Born
  kernel after fixing the pilot.
* `maximumJumpEnvelopeTendstoZero` and `incrementBound` give the stronger
  deterministic infinitesimal-array property `max_t |X_{r,t}| -> 0`.
* `conditionalLindebergEventuallyZero` is the conditional Lindeberg condition
  of Corollary 3.1; the closed-tail sum is eventually identically zero.
* `conditionalVarianceIdentity` identifies the predictable variance sum
  `sum_t E[X_{r,t}^2 | F_{r,t-1}]` with the explicit normalized Fisher sum.
* `conditionalVarianceConvergenceInProbability` is precisely convergence in
  probability of that predictable variance to `targetVariance`.
* `targetVarianceNonnegative` records the required nonnegative scalar limit.

This structure is deliberately a finite-kernel package.  Literal application
of Hall--Heyde still requires a bridge constructing one filtered probability
space (or a theorem accepting row kernels directly) and proving that these
finite Born-kernel sums are the corresponding conditional expectations with
respect to `F_{r,t-1}`. -/
structure MixedExactCycleHallHeydeCorollary31FinitePremises
    (A : MixedExactCycleScalarTriangularArrayData) : Prop where
  conditionalScoreCentering :
    ∀ r : ℕ, 0 < r -> ∀ (pilot : A.PilotSpace r) (t : Fin (3 * r)),
      (∑ outcome : Bool,
        mixedTwoStageFinalBornProbability
            A.theta (A.selected r) pilot t outcome *
          A.normalizedFinalScoreIncrement r pilot t outcome) = 0
  maximumJumpEnvelopeTendstoZero :
    Tendsto A.maximumJumpEnvelope atTop (nhds 0)
  incrementBound :
    ∀ r : ℕ, 0 < r -> ∀ (pilot : A.PilotSpace r)
      (t : Fin (3 * r)) (outcome : Bool),
      |A.normalizedFinalScoreIncrement r pilot t outcome| ≤
        A.maximumJumpEnvelope r
  conditionalLindebergEventuallyZero :
    ∀ epsilon : ℝ, 0 < epsilon ->
      ∀ᶠ r : ℕ in atTop,
        0 < r ∧ ∀ pilot : A.PilotSpace r,
          A.conditionalLindebergSum r pilot epsilon = 0
  conditionalVarianceIdentity :
    ∀ r : ℕ, 0 < r -> ∀ pilot : A.PilotSpace r,
      A.conditionalVariance r pilot =
        A.explicitNormalizedFisher r pilot
  conditionalVarianceConvergenceInProbability :
    A.FisherConvergesInProbability
  targetVarianceNonnegative : 0 ≤ A.targetVariance

/-- Item 5: convergence in probability of the explicit Fisher expression is
the sole parameter needed to construct every field of the finite-kernel
Hall--Heyde premise package. -/
theorem hallHeydeCorollary31FinitePremises_of_fisherConvergence
    (A : MixedExactCycleScalarTriangularArrayData)
    (hFisher : A.FisherConvergesInProbability) :
    MixedExactCycleHallHeydeCorollary31FinitePremises A := by
  refine ⟨?_, A.maximumJumpEnvelope_tendsto_zero, ?_, ?_, ?_,
    hFisher, A.targetVariance_nonnegative⟩
  · intro r _hr pilot t
    exact A.conditionalScoreCentering r pilot t
  · intro r hr pilot t outcome
    exact A.normalizedFinalScoreIncrement_abs_le_maximumJumpEnvelope
      r hr pilot t outcome
  · intro epsilon hepsilon
    exact A.conditionalLindebergSum_eventually_zero epsilon hepsilon
  · intro r hr pilot
    exact A.conditionalVariance_eq_explicitNormalizedFisher r hr pilot

end MixedExactCycleScalarTriangularArrayData

end

end QubitOracle.Paper
