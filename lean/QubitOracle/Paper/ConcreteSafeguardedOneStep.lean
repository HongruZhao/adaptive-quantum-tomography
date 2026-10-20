import QubitOracle.Paper.AdaptiveMLEEfficiency
import QubitOracle.Paper.SafeguardEventProofs
import QubitOracle.Paper.MomentRiskTransfer
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# The concrete safeguarded one-step estimator

This file formalizes the estimator that is actually computed. All quantities are
written on the local `sqrt n` scale:

* `pilotError = sqrt n (thetaTilde - theta)`;
* `normalizedScore = S_n(thetaTilde) / sqrt n`;
* `normalizedInformation = J_n(thetaTilde) / n`;
* `ridge` is the vanishing regularization coefficient.

The raw update uses `(normalizedInformation + ridge * I)⁻¹`. The safeguarded
update returns the raw update on the accepted Hessian/step event and a specified
physical fallback otherwise. The central theorem below is an exact finite-sample
identity, not an asymptotic or literature assumption.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory Set

noncomputable section

variable {D Omega : Type*}

/-- Normalized observed information with a scalar ridge. -/
def regularizedNormalizedInformation [Fintype D] [DecidableEq D]
    (J : Matrix D D Real) (ridge : Real) : Matrix D D Real :=
  J + ridge • (1 : Matrix D D Real)

/-- The normalized local error of the raw regularized one-step update. -/
def normalizedRegularizedOneStepError [Fintype D] [DecidableEq D]
    (pilotError normalizedScore : LANParameter D)
    (normalizedInformation : Matrix D D Real) (ridge : Real) : LANParameter D :=
  pilotError +
    lanMatrixAction (regularizedNormalizedInformation normalizedInformation ridge)⁻¹
      normalizedScore

/-- The exact Newton linearization defect at the pilot. -/
def normalizedNewtonDefect [Fintype D] [DecidableEq D]
    (pilotError normalizedScore centralScore : LANParameter D)
    (normalizedInformation : Matrix D D Real) (ridge : Real) : LANParameter D :=
  normalizedScore -
    (centralScore -
      lanMatrixAction (regularizedNormalizedInformation normalizedInformation ridge)
        pilotError)

/--
Exact finite-sample cancellation for the regularized one-step update.

If `A = J/n + ridge * I`, then

`oneStepError - A⁻¹ centralScore = A⁻¹ NewtonDefect`.

Thus the pilot error cancels exactly. This is the key algebraic fact that lets a
one-step estimator be efficient without being an exact score root.
-/
theorem normalizedRegularizedOneStepError_exact
    [Fintype D] [DecidableEq D]
    (pilotError normalizedScore centralScore : LANParameter D)
    (normalizedInformation : Matrix D D Real) (ridge : Real)
    (hA :
      (regularizedNormalizedInformation normalizedInformation ridge).PosDef) :
    normalizedRegularizedOneStepError pilotError normalizedScore
        normalizedInformation ridge -
      lanMatrixAction
        (regularizedNormalizedInformation normalizedInformation ridge)⁻¹ centralScore =
      lanMatrixAction
        (regularizedNormalizedInformation normalizedInformation ridge)⁻¹
        (normalizedNewtonDefect pilotError normalizedScore centralScore
          normalizedInformation ridge) := by
  simp only [normalizedRegularizedOneStepError, normalizedNewtonDefect,
    lanMatrixAction_vector_sub]
  rw [lanMatrixAction_inv_apply
    (regularizedNormalizedInformation normalizedInformation ridge) hA pilotError]
  abel

/-- Exact score linearity makes the raw one-step error the efficient score transform. -/
theorem normalizedRegularizedOneStepError_eq_efficient_of_zero_defect
    [Fintype D] [DecidableEq D]
    (pilotError normalizedScore centralScore : LANParameter D)
    (normalizedInformation : Matrix D D Real) (ridge : Real)
    (hA :
      (regularizedNormalizedInformation normalizedInformation ridge).PosDef)
    (hdefect : normalizedNewtonDefect pilotError normalizedScore centralScore
      normalizedInformation ridge = 0) :
    normalizedRegularizedOneStepError pilotError normalizedScore
        normalizedInformation ridge =
      lanMatrixAction
        (regularizedNormalizedInformation normalizedInformation ridge)⁻¹ centralScore := by
  apply sub_eq_zero.mp
  rw [normalizedRegularizedOneStepError_exact pilotError normalizedScore centralScore
    normalizedInformation ridge hA, hdefect]
  ext i
  simp [lanMatrixAction, Matrix.mulVec]

/--
The actual safeguarded estimator. `accept` is the conjunction of the Hessian
and step safeguards; `fallbackError` is the normalized error of a physical pilot
or another fixed physical state.
-/
def concreteSafeguardedRegularizedOneStepError
    [Fintype D] [DecidableEq D]
    (accept : Nat -> Set Omega)
    (pilotError normalizedScore : Nat -> Omega -> LANParameter D)
    (normalizedInformation : Nat -> Omega -> Matrix D D Real)
    (ridge : Nat -> Real)
    (fallbackError : Nat -> Omega -> LANParameter D)
    (n : Nat) (omega : Omega) : LANParameter D :=
  paperSafeguardedEstimator (accept n)
    (fun w => normalizedRegularizedOneStepError
      (pilotError n w) (normalizedScore n w)
      (normalizedInformation n w) (ridge n))
    (fallbackError n) omega

/-- On the accepted event, the implemented estimator is exactly the raw update. -/
theorem concreteSafeguardedRegularizedOneStepError_eq_raw
    [Fintype D] [DecidableEq D]
    (accept : Nat -> Set Omega)
    (pilotError normalizedScore : Nat -> Omega -> LANParameter D)
    (normalizedInformation : Nat -> Omega -> Matrix D D Real)
    (ridge : Nat -> Real)
    (fallbackError : Nat -> Omega -> LANParameter D)
    {n : Nat} {omega : Omega} (haccept : omega ∈ accept n) :
    concreteSafeguardedRegularizedOneStepError accept pilotError normalizedScore
        normalizedInformation ridge fallbackError n omega =
      normalizedRegularizedOneStepError
        (pilotError n omega) (normalizedScore n omega)
        (normalizedInformation n omega) (ridge n) := by
  exact paperSafeguardedEstimator_eq_raw_of_mem
    (accept n)
    (fun w => normalizedRegularizedOneStepError
      (pilotError n w) (normalizedScore n w)
      (normalizedInformation n w) (ridge n))
    (fallbackError n) haccept

/-- Eventual safeguard acceptance gives eventual pointwise equality with the raw update. -/
theorem concreteSafeguardedRegularizedOneStepError_eventuallyEq_raw
    [Fintype D] [DecidableEq D]
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (accept : Nat -> Set Omega)
    (pilotError normalizedScore : Nat -> Omega -> LANParameter D)
    (normalizedInformation : Nat -> Omega -> Matrix D D Real)
    (ridge : Nat -> Real)
    (fallbackError : Nat -> Omega -> LANParameter D)
    (haccept : ∀ᵐ omega ∂mu, ∀ᶠ n in atTop, omega ∈ accept n) :
    ∀ᵐ omega ∂mu, ∀ᶠ n in atTop,
      concreteSafeguardedRegularizedOneStepError accept pilotError normalizedScore
          normalizedInformation ridge fallbackError n omega =
        normalizedRegularizedOneStepError
          (pilotError n omega) (normalizedScore n omega)
          (normalizedInformation n omega) (ridge n) := by
  filter_upwards [haccept] with omega homega
  exact homega.mono fun _n hn =>
    concreteSafeguardedRegularizedOneStepError_eq_raw accept pilotError normalizedScore
      normalizedInformation ridge fallbackError hn

/--
First Borel-Cantelli closes safeguard inactivity from a checkable summability
condition: if rejection probabilities are summable, rejection occurs only finitely
often almost surely.
-/
theorem safeguard_accept_eventually_ae_of_summable_rejection
    [MeasurableSpace Omega]
    (mu : Measure Omega) (accept : Nat -> Set Omega)
    (hsum : (∑' n, mu (Set.compl (accept n))) ≠ ⊤) :
    ∀ᵐ omega ∂mu, ∀ᶠ n in atTop, omega ∈ accept n := by
  filter_upwards [ae_finite_setOfPred_mem hsum] with omega homega
  have hnot := homega.eventually_cofinite_notMem
  rw [Nat.cofinite_eq_atTop] at hnot
  filter_upwards [hnot] with n hn
  change ¬omega ∈ (accept n)ᶜ at hn
  simpa only [mem_compl_iff, not_not] using hn

/--
Consequently, summable rejection probabilities make the concrete safeguarded
estimator eventually identical to its raw regularized one-step update almost surely.
-/
theorem concreteSafeguardedRegularizedOneStepError_eventuallyEq_raw_of_summable_rejection
    [Fintype D] [DecidableEq D]
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (accept : Nat -> Set Omega)
    (pilotError normalizedScore : Nat -> Omega -> LANParameter D)
    (normalizedInformation : Nat -> Omega -> Matrix D D Real)
    (ridge : Nat -> Real)
    (fallbackError : Nat -> Omega -> LANParameter D)
    (hsum : (∑' n, mu (Set.compl (accept n))) ≠ ⊤) :
    ∀ᵐ omega ∂mu, ∀ᶠ n in atTop,
      concreteSafeguardedRegularizedOneStepError accept pilotError normalizedScore
          normalizedInformation ridge fallbackError n omega =
        normalizedRegularizedOneStepError
          (pilotError n omega) (normalizedScore n omega)
          (normalizedInformation n omega) (ridge n) :=
  concreteSafeguardedRegularizedOneStepError_eventuallyEq_raw mu accept pilotError
    normalizedScore normalizedInformation ridge fallbackError
    (safeguard_accept_eventually_ae_of_summable_rejection mu accept hsum)

/-- Summable rejection probabilities in particular converge to zero. -/
theorem safeguard_rejection_probability_tendsto_zero_of_summable
    [MeasurableSpace Omega]
    (mu : Measure Omega) (accept : Nat -> Set Omega)
    (hsum : (∑' n, mu (Set.compl (accept n))) ≠ ⊤) :
    Tendsto (fun n => mu (Set.compl (accept n))) atTop (nhds 0) :=
  ENNReal.tendsto_atTop_zero_of_tsum_ne_top hsum

/--
If safeguard rejection has probability tending to zero, the safeguarded update
minus the raw update converges to zero in probability. No bound on the fallback
is needed for this first-order statement because the two estimators are exactly
equal on the acceptance event.
-/
theorem concreteSafeguardedRegularizedOneStepError_sub_raw_tendstoInMeasure
    [Fintype D] [DecidableEq D]
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (accept : Nat -> Set Omega)
    (pilotError normalizedScore : Nat -> Omega -> LANParameter D)
    (normalizedInformation : Nat -> Omega -> Matrix D D Real)
    (ridge : Nat -> Real)
    (fallbackError : Nat -> Omega -> LANParameter D)
    (hreject :
      Tendsto (fun n => mu (Set.compl (accept n))) atTop (nhds 0)) :
    TendstoInMeasure mu
      (fun n omega =>
        concreteSafeguardedRegularizedOneStepError accept pilotError normalizedScore
            normalizedInformation ridge fallbackError n omega -
          normalizedRegularizedOneStepError
            (pilotError n omega) (normalizedScore n omega)
            (normalizedInformation n omega) (ridge n))
      atTop 0 := by
  rw [tendstoInMeasure_iff_norm]
  intro epsilon hepsilon
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hreject (fun _n => bot_le) ?_
  intro n
  apply measure_mono
  intro omega hlarge
  by_contra hnotReject
  have haccept : omega ∈ accept n := by
    by_contra hnotAccept
    exact hnotReject hnotAccept
  have heq :=
    concreteSafeguardedRegularizedOneStepError_eq_raw accept pilotError
      normalizedScore normalizedInformation ridge fallbackError haccept
  have hzero :
      concreteSafeguardedRegularizedOneStepError accept pilotError normalizedScore
          normalizedInformation ridge fallbackError n omega -
        normalizedRegularizedOneStepError
          (pilotError n omega) (normalizedScore n omega)
          (normalizedInformation n omega) (ridge n) -
        (0 : LANParameter D) = 0 := by
    rw [heq]
    simp
  change epsilon ≤ ‖
    concreteSafeguardedRegularizedOneStepError accept pilotError normalizedScore
        normalizedInformation ridge fallbackError n omega -
      normalizedRegularizedOneStepError
        (pilotError n omega) (normalizedScore n omega)
        (normalizedInformation n omega) (ridge n) -
      (0 : LANParameter D)‖ at hlarge
  rw [hzero, norm_zero] at hlarge
  exact (not_le_of_gt hepsilon) hlarge

/--
Direct asymptotic linearity of the raw regularized one-step update.

The two hypotheses are the two genuinely analytic remainders:

1. inverse-information times the Newton defect vanishes in probability;
2. replacing the regularized observed inverse by the limiting inverse, when
   applied to the central score, vanishes in probability.

The conclusion is proved from the exact finite-sample identity above and does
not use a score-root assumption.
-/
theorem normalizedRegularizedOneStepError_asymptoticallyLinear
    [Fintype D] [DecidableEq D]
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (pilotError normalizedScore centralScore :
      Nat -> Omega -> LANParameter D)
    (normalizedInformation : Nat -> Omega -> Matrix D D Real)
    (ridge : Nat -> Real)
    (limitingInformation : Matrix D D Real)
    (hA : ∀ n omega,
      (regularizedNormalizedInformation
        (normalizedInformation n omega) (ridge n)).PosDef)
    (hDefect :
      TendstoInMeasure mu
        (fun n omega =>
          lanMatrixAction
            (regularizedNormalizedInformation
              (normalizedInformation n omega) (ridge n))⁻¹
            (normalizedNewtonDefect
              (pilotError n omega) (normalizedScore n omega)
              (centralScore n omega) (normalizedInformation n omega) (ridge n)))
        atTop 0)
    (hInverseScore :
      TendstoInMeasure mu
        (fun n omega =>
          lanMatrixAction
              (regularizedNormalizedInformation
                (normalizedInformation n omega) (ridge n))⁻¹
              (centralScore n omega) -
            lanMatrixAction limitingInformation⁻¹ (centralScore n omega))
        atTop 0) :
    TendstoInMeasure mu
      (fun n omega =>
        normalizedRegularizedOneStepError
            (pilotError n omega) (normalizedScore n omega)
            (normalizedInformation n omega) (ridge n) -
          lanMatrixAction limitingInformation⁻¹ (centralScore n omega))
      atTop 0 := by
  have hsum := tendstoInMeasure_add_zero_vector hDefect hInverseScore
  refine hsum.congr' (Eventually.of_forall fun n => ?_) Filter.EventuallyEq.rfl
  exact ae_of_all mu fun omega => by
    have hexact :=
      normalizedRegularizedOneStepError_exact
        (pilotError n omega) (normalizedScore n omega) (centralScore n omega)
        (normalizedInformation n omega) (ridge n) (hA n omega)
    calc
      lanMatrixAction
            (regularizedNormalizedInformation
              (normalizedInformation n omega) (ridge n))⁻¹
            (normalizedNewtonDefect
              (pilotError n omega) (normalizedScore n omega)
              (centralScore n omega) (normalizedInformation n omega) (ridge n)) +
          (lanMatrixAction
              (regularizedNormalizedInformation
                (normalizedInformation n omega) (ridge n))⁻¹
              (centralScore n omega) -
            lanMatrixAction limitingInformation⁻¹ (centralScore n omega)) =
        (normalizedRegularizedOneStepError
            (pilotError n omega) (normalizedScore n omega)
            (normalizedInformation n omega) (ridge n) -
          lanMatrixAction
              (regularizedNormalizedInformation
                (normalizedInformation n omega) (ridge n))⁻¹
              (centralScore n omega)) +
          (lanMatrixAction
              (regularizedNormalizedInformation
                (normalizedInformation n omega) (ridge n))⁻¹
              (centralScore n omega) -
            lanMatrixAction limitingInformation⁻¹ (centralScore n omega)) := by
              rw [hexact]
      _ = normalizedRegularizedOneStepError
            (pilotError n omega) (normalizedScore n omega)
            (normalizedInformation n omega) (ridge n) -
          lanMatrixAction limitingInformation⁻¹ (centralScore n omega) := by
            abel

/--
Direct asymptotic linearity of the implemented safeguarded estimator.

This is the concrete efficiency theorem: exact Newton cancellation, the two
analytic remainder convergences, and vanishing rejection probability imply the
usual efficient inverse-information score representation.
-/
theorem concreteSafeguardedRegularizedOneStepError_asymptoticallyLinear
    [Fintype D] [DecidableEq D]
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (accept : Nat -> Set Omega)
    (pilotError normalizedScore centralScore :
      Nat -> Omega -> LANParameter D)
    (normalizedInformation : Nat -> Omega -> Matrix D D Real)
    (ridge : Nat -> Real)
    (fallbackError : Nat -> Omega -> LANParameter D)
    (limitingInformation : Matrix D D Real)
    (hA : ∀ n omega,
      (regularizedNormalizedInformation
        (normalizedInformation n omega) (ridge n)).PosDef)
    (hDefect :
      TendstoInMeasure mu
        (fun n omega =>
          lanMatrixAction
            (regularizedNormalizedInformation
              (normalizedInformation n omega) (ridge n))⁻¹
            (normalizedNewtonDefect
              (pilotError n omega) (normalizedScore n omega)
              (centralScore n omega) (normalizedInformation n omega) (ridge n)))
        atTop 0)
    (hInverseScore :
      TendstoInMeasure mu
        (fun n omega =>
          lanMatrixAction
              (regularizedNormalizedInformation
                (normalizedInformation n omega) (ridge n))⁻¹
              (centralScore n omega) -
            lanMatrixAction limitingInformation⁻¹ (centralScore n omega))
        atTop 0)
    (hreject :
      Tendsto (fun n => mu (Set.compl (accept n))) atTop (nhds 0)) :
    TendstoInMeasure mu
      (fun n omega =>
        concreteSafeguardedRegularizedOneStepError accept pilotError normalizedScore
            normalizedInformation ridge fallbackError n omega -
          lanMatrixAction limitingInformation⁻¹ (centralScore n omega))
      atTop 0 := by
  have hSafeRaw :=
    concreteSafeguardedRegularizedOneStepError_sub_raw_tendstoInMeasure
      mu accept pilotError normalizedScore normalizedInformation ridge
      fallbackError hreject
  have hRaw :=
    normalizedRegularizedOneStepError_asymptoticallyLinear
      mu pilotError normalizedScore centralScore normalizedInformation ridge
      limitingInformation hA hDefect hInverseScore
  have hsum := tendstoInMeasure_add_zero_vector hSafeRaw hRaw
  refine hsum.congr' (Eventually.of_forall fun n => ?_) Filter.EventuallyEq.rfl
  exact ae_of_all mu fun omega => by
    abel

/-- Summable rejection is a convenient sufficient condition for the concrete result. -/
theorem concreteSafeguardedRegularizedOneStepError_asymptoticallyLinear_of_summable_rejection
    [Fintype D] [DecidableEq D]
    [MeasurableSpace Omega]
    (mu : Measure Omega)
    (accept : Nat -> Set Omega)
    (pilotError normalizedScore centralScore :
      Nat -> Omega -> LANParameter D)
    (normalizedInformation : Nat -> Omega -> Matrix D D Real)
    (ridge : Nat -> Real)
    (fallbackError : Nat -> Omega -> LANParameter D)
    (limitingInformation : Matrix D D Real)
    (hA : ∀ n omega,
      (regularizedNormalizedInformation
        (normalizedInformation n omega) (ridge n)).PosDef)
    (hDefect :
      TendstoInMeasure mu
        (fun n omega =>
          lanMatrixAction
            (regularizedNormalizedInformation
              (normalizedInformation n omega) (ridge n))⁻¹
            (normalizedNewtonDefect
              (pilotError n omega) (normalizedScore n omega)
              (centralScore n omega) (normalizedInformation n omega) (ridge n)))
        atTop 0)
    (hInverseScore :
      TendstoInMeasure mu
        (fun n omega =>
          lanMatrixAction
              (regularizedNormalizedInformation
                (normalizedInformation n omega) (ridge n))⁻¹
              (centralScore n omega) -
            lanMatrixAction limitingInformation⁻¹ (centralScore n omega))
        atTop 0)
    (hsum : (∑' n, mu (Set.compl (accept n))) ≠ ⊤) :
    TendstoInMeasure mu
      (fun n omega =>
        concreteSafeguardedRegularizedOneStepError accept pilotError normalizedScore
            normalizedInformation ridge fallbackError n omega -
          lanMatrixAction limitingInformation⁻¹ (centralScore n omega))
      atTop 0 :=
  concreteSafeguardedRegularizedOneStepError_asymptoticallyLinear
    mu accept pilotError normalizedScore centralScore normalizedInformation ridge
    fallbackError limitingInformation hA hDefect hInverseScore
    (safeguard_rejection_probability_tendsto_zero_of_summable mu accept hsum)

/--
Pointwise form of the same implemented estimator.  Unlike the sequence-level
definition, this form allows the sample type to vary with the experiment index.
-/
def concreteSafeguardedRegularizedOneStepErrorAt
    {D Omega : Type*} [Fintype D] [DecidableEq D]
    (accept : Set Omega)
    (pilotError normalizedScore : Omega -> LANParameter D)
    (normalizedInformation : Omega -> Matrix D D Real)
    (ridge : Real)
    (fallbackError : Omega -> LANParameter D)
    (omega : Omega) : LANParameter D :=
  paperSafeguardedEstimator accept
    (fun w => normalizedRegularizedOneStepError
      (pilotError w) (normalizedScore w) (normalizedInformation w) ridge)
    fallbackError omega

/--
All data needed to turn the concrete safeguarded update into an actual statistic
of a sequence of local experiments.  The measurability field is implementation
bookkeeping; the formula itself is fixed by the preceding definition.
-/
structure ConcreteSafeguardedRegularizedOneStepStatisticData
    (D : Type*) [Fintype D] [DecidableEq D]
    (E : Nat -> StatisticalExperiment (LANParameter D)) where
  accept : (n : Nat) -> Set (E n).Sample
  pilotError : (n : Nat) -> (E n).Sample -> LANParameter D
  normalizedScore : (n : Nat) -> (E n).Sample -> LANParameter D
  normalizedInformation : (n : Nat) -> (E n).Sample -> Matrix D D Real
  ridge : Nat -> Real
  fallbackError : (n : Nat) -> (E n).Sample -> LANParameter D
  outputMeasurable : ∀ n,
    @Measurable (E n).Sample (LANParameter D)
      (E n).measurableSpace inferInstance
      (fun omega =>
        concreteSafeguardedRegularizedOneStepErrorAt
          (accept n) (pilotError n) (normalizedScore n)
          (normalizedInformation n) (ridge n) (fallbackError n) omega)

/-- The measurable statistic whose value is the implemented safeguarded update. -/
def ConcreteSafeguardedRegularizedOneStepStatisticData.toStatistic
    {D : Type*} [Fintype D] [DecidableEq D]
    {E : Nat -> StatisticalExperiment (LANParameter D)}
    (data : ConcreteSafeguardedRegularizedOneStepStatisticData D E)
    (n : Nat) : Statistic (E n) (LANParameter D) where
  toFun := fun omega =>
    concreteSafeguardedRegularizedOneStepErrorAt
      (data.accept n) (data.pilotError n) (data.normalizedScore n)
      (data.normalizedInformation n) (data.ridge n)
      (data.fallbackError n) omega
  measurable := data.outputMeasurable n

/--
Concrete one-step minimax-attainment theorem.

The statistic in the conclusion is literally the safeguarded regularized update.
The fourth-moment hypothesis is converted, inside Lean, to the uniform quadratic
tail condition.  Thus no unproved weak-convergence-to-unbounded-risk step is
hidden in the result.
-/
theorem concreteSafeguardedRegularizedOneStep_attains_localAsymptoticMinimax
    {D : Type*} [Fintype D] [DecidableEq D]
    (J : Matrix D D Real) (hJ : J.PosDef)
    (E : Nat -> StatisticalExperiment (LANParameter D))
    (data : ConcreteSafeguardedRegularizedOneStepStatisticData D E)
    (hExperiment : ExperimentsConverge E (gaussianScoreExperiment J))
    (hCapped :
      ∀ (I : Finset (LANParameter D)), I.Nonempty ->
        CappedFiniteLocalRisksConvergeToCenteredGaussian
          J E data.toStatistic I)
    (hFourth :
      ∀ (I : Finset (LANParameter D)), I.Nonempty ->
        ∃ C : ENNReal, C ≠ ⊤ ∧
          HasUniformFiniteLocalFourthMomentBound E data.toStatistic I C) :
    AttainsGaussianLocalAsymptoticMinimaxBound J E data.toStatistic := by
  apply gaussianScore_localAsymptoticMinimax_attained_of_cappedGaussian_of_uniformTails
    J hJ E hExperiment data.toStatistic hCapped
  intro I hI
  obtain ⟨C, hCTop, hMoment⟩ := hFourth I hI
  exact hasUniformFiniteLocalQuadraticTails_of_fourthMoment
    E data.toStatistic I C hCTop hMoment

/-- Mixed one-qubit specialization in the three Bloch coordinates. -/
theorem mixedQubit_concreteSafeguardedRegularizedOneStep_attains_localAsymptoticMinimax
    (J : Matrix (Fin 3) (Fin 3) Real) (hJ : J.PosDef)
    (E : Nat -> StatisticalExperiment (LANParameter (Fin 3)))
    (data : ConcreteSafeguardedRegularizedOneStepStatisticData (Fin 3) E)
    (hExperiment : ExperimentsConverge E (gaussianScoreExperiment J))
    (hCapped :
      ∀ (I : Finset (LANParameter (Fin 3))), I.Nonempty ->
        CappedFiniteLocalRisksConvergeToCenteredGaussian
          J E data.toStatistic I)
    (hFourth :
      ∀ (I : Finset (LANParameter (Fin 3))), I.Nonempty ->
        ∃ C : ENNReal, C ≠ ⊤ ∧
          HasUniformFiniteLocalFourthMomentBound E data.toStatistic I C) :
    AttainsGaussianLocalAsymptoticMinimaxBound J E data.toStatistic :=
  concreteSafeguardedRegularizedOneStep_attains_localAsymptoticMinimax
    J hJ E data hExperiment hCapped hFourth

/-- Pure one-qubit specialization in two tangent coordinates. -/
theorem pureQubit_concreteSafeguardedRegularizedOneStep_attains_localAsymptoticMinimax
    (J : Matrix (Fin 2) (Fin 2) Real) (hJ : J.PosDef)
    (E : Nat -> StatisticalExperiment (LANParameter (Fin 2)))
    (data : ConcreteSafeguardedRegularizedOneStepStatisticData (Fin 2) E)
    (hExperiment : ExperimentsConverge E (gaussianScoreExperiment J))
    (hCapped :
      ∀ (I : Finset (LANParameter (Fin 2))), I.Nonempty ->
        CappedFiniteLocalRisksConvergeToCenteredGaussian
          J E data.toStatistic I)
    (hFourth :
      ∀ (I : Finset (LANParameter (Fin 2))), I.Nonempty ->
        ∃ C : ENNReal, C ≠ ⊤ ∧
          HasUniformFiniteLocalFourthMomentBound E data.toStatistic I C) :
    AttainsGaussianLocalAsymptoticMinimaxBound J E data.toStatistic :=
  concreteSafeguardedRegularizedOneStep_attains_localAsymptoticMinimax
    J hJ E data hExperiment hCapped hFourth

end

end QubitOracle.Paper
