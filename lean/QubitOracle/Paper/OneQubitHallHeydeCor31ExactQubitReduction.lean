import QubitOracle.Paper.OneQubitMixedCommonSpaceCondExpPullbackClosed
import QubitOracle.Paper.SourceFaithfulHallHeydeCor31DeterministicVariance
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Hall--Heyde Corollary 3.1: exact mixed-qubit reduction

This file imports the source-faithful deterministic-variance statement of Hall
and Heyde (1980), Corollary 3.1, and reduces it to the concrete mixed
exact-cycle score array. The only scientific atom is the cited scalar
martingale-array CLT; every protocol-specific premise is proved here.

The source convention is zero based: increment `k` is measurable at time
`k + 1` and has conditional mean zero at time `k`. The field
`condition321` is the finite-row form of the printed condition (3.21).
The printed strict-tail conditional Lindeberg observable is used here, rather
than the closed-tail strengthening used in the earlier qubit preparation file.

Only convergence in distribution is requested in the conclusion. The book's
printed conclusion is the stronger stable convergence to a normal mixture.
For deterministic variance, ordinary convergence in distribution is its
immediate specialization. The remarks following Corollary 3.1 also permit
dropping (3.21) in that deterministic, non-stable specialization; this file
retains (3.21), because the concrete common-space construction proves it.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace QubitOracle.Paper

noncomputable section

/-! ## The concrete repeated mixed exact-cycle array -/

namespace MixedExactCycleScalarTriangularArrayData

attribute [local instance] rowMeasurableSpace rowMeasurableSingletonClass
  historyKeyMeasurableSpace

/-- One fixed qubit model repeated over the row index. -/
abbrev repeatedExactCycleData
    (B : MixedExactCycleScalarTriangularArrayData) :
    ℕ → MixedExactCycleScalarTriangularArrayData :=
  fun _ => B

/-- Row `n` contains `3 * n` final observations. -/
abbrev exactCycleIdentityRowSize : ℕ → ℕ := fun n => n

abbrev exactCycleCommonRowLength (n : ℕ) : ℕ := 3 * n

/-- Common product sample space for all exact-cycle rows of one fixed model. -/
abbrev ExactCycleCommonOmega
    (B : MixedExactCycleScalarTriangularArrayData) :=
  (CommonOmega B.repeatedExactCycleData exactCycleIdentityRowSize)

/-- The exact common product probability measure. -/
noncomputable abbrev exactCycleCommonMeasure
    (B : MixedExactCycleScalarTriangularArrayData) :
    Measure (CommonOmega B.repeatedExactCycleData exactCycleIdentityRowSize) :=
  commonMeasure B.repeatedExactCycleData exactCycleIdentityRowSize

noncomputable instance exactCycleCommonMeasure_isProbabilityMeasure
    (B : MixedExactCycleScalarTriangularArrayData) :
    IsProbabilityMeasure B.exactCycleCommonMeasure := by
  change IsProbabilityMeasure
    (commonMeasure B.repeatedExactCycleData exactCycleIdentityRowSize)
  exact commonMeasure_isProbabilityMeasure
    B.repeatedExactCycleData exactCycleIdentityRowSize

/-- The augmented common-space filtration for row `n`. -/
abbrev exactCycleCommonFiltration
    (B : MixedExactCycleScalarTriangularArrayData) (n : ℕ) :
    Filtration ℕ
      (inferInstance : MeasurableSpace (CommonOmega B.repeatedExactCycleData exactCycleIdentityRowSize)) :=
  augmentedRowFiltration B.repeatedExactCycleData
    exactCycleIdentityRowSize n

/-- The normalized scalar final score, lifted from finite row `n` to the
common product space. -/
abbrev exactCycleCommonScoreIncrement
    (B : MixedExactCycleScalarTriangularArrayData)
    (n : ℕ) (t : Fin (exactCycleCommonRowLength n)) :
    (CommonOmega B.repeatedExactCycleData exactCycleIdentityRowSize) → ℝ :=
  liftRowVariable B.repeatedExactCycleData exactCycleIdentityRowSize n
    (B.currentCoordinateObservable n t (B.scoreObservable n t))

/-- Chosen predictable conditional-variance version for one score increment. -/
abbrev exactCycleCommonConditionalVariance
    (B : MixedExactCycleScalarTriangularArrayData)
    (n : ℕ) (t : Fin (exactCycleCommonRowLength n)) :
    (CommonOmega B.repeatedExactCycleData exactCycleIdentityRowSize) → ℝ :=
  liftRowVariable B.repeatedExactCycleData exactCycleIdentityRowSize n
    (B.oneShotFisherKernel n t)

/-! ## Printed strict-tail Lindeberg observable -/

/-- Strict-tail observable appearing literally in the printed Corollary 3.1. -/
def strictLindebergObservable
    (B : MixedExactCycleScalarTriangularArrayData)
    (r : ℕ) (t : Fin (3 * r)) (epsilon : ℝ)
    (pilot : B.PilotSpace r) (outcome : Bool) : ℝ :=
  if epsilon < |B.normalizedFinalScoreIncrement r pilot t outcome| then
    B.normalizedFinalScoreIncrement r pilot t outcome ^ 2
  else 0

/-- Exact one-shot conditional expectation of the strict-tail observable. -/
def strictOneShotLindebergKernel
    (B : MixedExactCycleScalarTriangularArrayData)
    (r : ℕ) (t : Fin (3 * r)) (epsilon : ℝ)
    (row : B.RowSpace r) : ℝ :=
  ∑ outcome : Bool,
    mixedTwoStageFinalBornProbability
        B.theta (B.selected r) row.1 t outcome *
      B.strictLindebergObservable r t epsilon row.1 outcome

/-- The finite Born product gives the exact strict-tail conditional
expectation certificate. -/
theorem strictLindeberg_finiteConditionalExpectation_eq_kernel
    (B : MixedExactCycleScalarTriangularArrayData)
    (r : ℕ) (t : Fin (3 * r)) (epsilon : ℝ) :
    B.ExactFiniteStepConditionalExpectation r t
      (B.strictLindebergObservable r t epsilon)
      (B.strictOneShotLindebergKernel r t epsilon) := by
  refine ⟨?_, ?_⟩
  · intro row₁ row₂ hhistory
    have hpilot : row₁.1 = row₂.1 :=
      congrArg (fun history : B.HistoryKey r => history.1) hhistory
    simp [strictOneShotLindebergKernel, hpilot]
  · intro row
    rfl

/-- Literal finite-row Mathlib conditional expectation for the printed
strict-tail observable. -/
theorem strictLindeberg_literal_condExp_eq_kernel
    (B : MixedExactCycleScalarTriangularArrayData)
    (r : ℕ) (t : Fin (3 * r)) (epsilon : ℝ) :
    (B.mathlibRowMeasure r)[
        B.currentCoordinateObservable r t
          (B.strictLindebergObservable r t epsilon) |
        B.rowFiltrationSigma r t.1] =ᵐ[B.mathlibRowMeasure r]
      B.strictOneShotLindebergKernel r t epsilon := by
  exact (B.exactFiniteStepConditionalExpectation_ae_eq_condExp
    r t (B.strictLindebergObservable r t epsilon)
      (B.strictOneShotLindebergKernel r t epsilon)
      (B.strictLindeberg_finiteConditionalExpectation_eq_kernel
        r t epsilon)).symm

/-- Lift of the printed strict-tail random variable to the common space. -/
abbrev exactCycleCommonStrictLindebergObservable
    (B : MixedExactCycleScalarTriangularArrayData)
    (n : ℕ) (t : Fin (exactCycleCommonRowLength n)) (epsilon : ℝ) :
    (CommonOmega B.repeatedExactCycleData exactCycleIdentityRowSize) → ℝ :=
  liftRowVariable B.repeatedExactCycleData exactCycleIdentityRowSize n
    (B.currentCoordinateObservable n t
      (B.strictLindebergObservable n t epsilon))

/-- Lifted chosen conditional expectation of the strict-tail observable. -/
abbrev exactCycleCommonStrictLindebergKernel
    (B : MixedExactCycleScalarTriangularArrayData)
    (epsilon : ℝ) (n : ℕ)
    (t : Fin (exactCycleCommonRowLength n)) :
    (CommonOmega B.repeatedExactCycleData exactCycleIdentityRowSize) → ℝ :=
  liftRowVariable B.repeatedExactCycleData exactCycleIdentityRowSize n
    (B.strictOneShotLindebergKernel n t epsilon)

/-! ## Exact common-space conditional-expectation fields -/

theorem exactCycleCommonScore_measurable_succ
    (B : MixedExactCycleScalarTriangularArrayData)
    (n : ℕ) (t : Fin (exactCycleCommonRowLength n)) :
    Measurable[B.exactCycleCommonFiltration n (t.1 + 1)]
      (B.exactCycleCommonScoreIncrement n t) := by
  unfold exactCycleCommonScoreIncrement exactCycleCommonFiltration
  exact liftedScore_measurable_succ B.repeatedExactCycleData
    exactCycleIdentityRowSize n t

theorem exactCycleCommonScore_integrable
    (B : MixedExactCycleScalarTriangularArrayData)
    (n : ℕ) (t : Fin (exactCycleCommonRowLength n)) :
    Integrable (B.exactCycleCommonScoreIncrement n t)
      B.exactCycleCommonMeasure := by
  unfold exactCycleCommonScoreIncrement exactCycleCommonMeasure
  exact liftRowVariable_integrable B.repeatedExactCycleData
    exactCycleIdentityRowSize n
      (B.currentCoordinateObservable n t (B.scoreObservable n t))
      (B.integrable_mathlibRowMeasure n _)

theorem exactCycleCommonScore_square_integrable
    (B : MixedExactCycleScalarTriangularArrayData)
    (n : ℕ) (t : Fin (exactCycleCommonRowLength n)) :
    Integrable (fun omega =>
      B.exactCycleCommonScoreIncrement n t omega ^ 2)
      B.exactCycleCommonMeasure := by
  have hLift := liftRowVariable_integrable B.repeatedExactCycleData
    exactCycleIdentityRowSize n
      (fun row : B.RowSpace n =>
        B.currentCoordinateObservable n t (B.scoreObservable n t) row ^ 2)
      (B.integrable_mathlibRowMeasure n _)
  unfold exactCycleCommonScoreIncrement exactCycleCommonMeasure
  exact hLift.congr (Filter.Eventually.of_forall fun omega => rfl)

theorem exactCycleCommonScore_condExp_zero
    (B : MixedExactCycleScalarTriangularArrayData)
    (n : ℕ) (t : Fin (exactCycleCommonRowLength n)) :
    B.exactCycleCommonMeasure[
        B.exactCycleCommonScoreIncrement n t |
        B.exactCycleCommonFiltration n t.1] =ᵐ[
          B.exactCycleCommonMeasure]
      (fun _ : (CommonOmega B.repeatedExactCycleData exactCycleIdentityRowSize) => (0 : ℝ)) := by
  unfold exactCycleCommonMeasure exactCycleCommonScoreIncrement
    exactCycleCommonFiltration
  have hCommon :=
    commonCondExp_lift B.repeatedExactCycleData
      exactCycleIdentityRowSize n t.1
      (B.currentCoordinateObservable n t (B.scoreObservable n t))
      (fun _ : B.RowSpace n => (0 : ℝ))
      (B.scoreIncrement_literal_condExp_zero n t)
  exact hCommon.trans (Filter.Eventually.of_forall fun omega => rfl)

theorem exactCycleCommonScoreSquare_condExp_eq_fisher
    (B : MixedExactCycleScalarTriangularArrayData)
    (n : ℕ) (t : Fin (exactCycleCommonRowLength n)) :
    B.exactCycleCommonMeasure[
        (fun omega => B.exactCycleCommonScoreIncrement n t omega ^ 2) |
        B.exactCycleCommonFiltration n t.1] =ᵐ[
          B.exactCycleCommonMeasure]
      B.exactCycleCommonConditionalVariance n t := by
  have ht : t.1 < 3 * n := t.2
  have hn : 0 < n := by omega
  unfold exactCycleCommonMeasure exactCycleCommonScoreIncrement
    exactCycleCommonConditionalVariance exactCycleCommonFiltration
  have hCommon :=
    commonCondExp_lift B.repeatedExactCycleData
      exactCycleIdentityRowSize n t.1
      (B.currentCoordinateObservable n t (B.squaredScoreObservable n t))
      (B.oneShotFisherKernel n t)
      (B.squaredScore_literal_condExp_eq_oneShotFisher n hn t)
  have hObservable :
      liftRowVariable B.repeatedExactCycleData exactCycleIdentityRowSize n
          (B.currentCoordinateObservable n t (B.squaredScoreObservable n t)) =
        (fun omega :
            CommonOmega B.repeatedExactCycleData exactCycleIdentityRowSize =>
          liftRowVariable B.repeatedExactCycleData exactCycleIdentityRowSize n
              (B.currentCoordinateObservable n t (B.scoreObservable n t)) omega ^ 2) := by
    funext omega
    rfl
  rw [← hObservable]
  exact hCommon

theorem exactCycleCommonStrictLindeberg_condExp_eq_kernel
    (B : MixedExactCycleScalarTriangularArrayData)
    (epsilon : ℝ) (_hepsilon : 0 < epsilon)
    (n : ℕ) (t : Fin (exactCycleCommonRowLength n)) :
    B.exactCycleCommonMeasure[
        (fun omega =>
          if epsilon < |B.exactCycleCommonScoreIncrement n t omega| then
            B.exactCycleCommonScoreIncrement n t omega ^ 2
          else 0) |
        B.exactCycleCommonFiltration n t.1] =ᵐ[
          B.exactCycleCommonMeasure]
      B.exactCycleCommonStrictLindebergKernel epsilon n t := by
  have hRow := B.strictLindeberg_literal_condExp_eq_kernel
    n t epsilon
  unfold exactCycleCommonMeasure exactCycleCommonScoreIncrement
    exactCycleCommonStrictLindebergKernel exactCycleCommonFiltration
  have hCommon :=
    commonCondExp_lift B.repeatedExactCycleData
      exactCycleIdentityRowSize n t.1
      (B.currentCoordinateObservable n t
        (B.strictLindebergObservable n t epsilon))
      (B.strictOneShotLindebergKernel n t epsilon) hRow
  have hObservable :
      liftRowVariable B.repeatedExactCycleData exactCycleIdentityRowSize n
          (B.currentCoordinateObservable n t
            (B.strictLindebergObservable n t epsilon)) =
        (fun omega :
            CommonOmega B.repeatedExactCycleData exactCycleIdentityRowSize =>
          if epsilon <
              |liftRowVariable B.repeatedExactCycleData exactCycleIdentityRowSize n
                (B.currentCoordinateObservable n t (B.scoreObservable n t)) omega| then
            liftRowVariable B.repeatedExactCycleData exactCycleIdentityRowSize n
                (B.currentCoordinateObservable n t (B.scoreObservable n t)) omega ^ 2
          else 0) := by
    funext omega
    rfl
  rw [← hObservable]
  exact hCommon

/-! ## Predictable sums and convergence -/

/-- The concrete chosen conditional-variance sum is exactly the explicit
pilot-dependent normalized Fisher expression. -/
theorem exactCycleCommonConditionalVariance_sum_eq_fisher
    (B : MixedExactCycleScalarTriangularArrayData)
    (n : ℕ) (omega : (CommonOmega B.repeatedExactCycleData exactCycleIdentityRowSize)) :
    (∑ t : Fin (exactCycleCommonRowLength n),
      B.exactCycleCommonConditionalVariance n t omega) =
        B.explicitNormalizedFisher n (omega n).1 := by
  simpa [exactCycleCommonConditionalVariance, liftRowVariable,
    predictableQuadraticVariation] using
    B.predictableQuadraticVariation_eq_explicitNormalizedFisher n (omega n)

/-- This is the sole model-specific asymptotic premise consumed by the
deterministic-variance reduction. -/
def CommonExactCycleFisherConvergesInProbability
    (B : MixedExactCycleScalarTriangularArrayData)
    (sigmaSq : ℝ) : Prop :=
  HallHeydeScalarConvergesInProbability B.exactCycleCommonMeasure
    (fun n omega => B.explicitNormalizedFisher n (omega n).1)
    sigmaSq

theorem strictOneShotLindebergKernel_eq_zero_of_envelope_lt
    (B : MixedExactCycleScalarTriangularArrayData)
    (r : ℕ) (hr : 0 < r) (pilot : B.PilotSpace r)
    (t : Fin (3 * r)) (epsilon : ℝ)
    (henvelope : B.maximumJumpEnvelope r < epsilon)
    (row : B.RowSpace r) (hpilot : row.1 = pilot) :
    B.strictOneShotLindebergKernel r t epsilon row = 0 := by
  subst pilot
  unfold strictOneShotLindebergKernel
  apply Finset.sum_eq_zero
  intro outcome _houtcome
  have hscore :=
    B.normalizedFinalScoreIncrement_abs_le_maximumJumpEnvelope
      r hr row.1 t outcome
  have hnot : ¬ epsilon <
      |B.normalizedFinalScoreIncrement r row.1 t outcome| :=
    not_lt_of_ge (hscore.trans (le_of_lt henvelope))
  simp [strictLindebergObservable, hnot]

/-- The printed strict-tail predictable Lindeberg sum is eventually exactly
zero, uniformly over the common sample point. -/
theorem exactCycleCommonStrictLindebergSum_eventually_zero
    (B : MixedExactCycleScalarTriangularArrayData)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      ∀ omega : (CommonOmega B.repeatedExactCycleData exactCycleIdentityRowSize),
        (∑ t : Fin (exactCycleCommonRowLength n),
          B.exactCycleCommonStrictLindebergKernel epsilon n t omega) = 0 := by
  have hsmall : ∀ᶠ n : ℕ in atTop,
      B.maximumJumpEnvelope n < epsilon :=
    (tendsto_order.1 B.maximumJumpEnvelope_tendsto_zero).2
      epsilon hepsilon
  filter_upwards [eventually_ge_atTop (1 : ℕ), hsmall]
    with n hn henvelope
  intro omega
  apply Finset.sum_eq_zero
  intro t _ht
  simpa [exactCycleCommonStrictLindebergKernel, liftRowVariable] using
    B.strictOneShotLindebergKernel_eq_zero_of_envelope_lt
      n hn (omega n).1 t epsilon henvelope (omega n) rfl

/-- Conditional Lindeberg convergence required by the abstract statement,
proved from the pilot-independent score envelope. -/
theorem exactCycleCommonStrictLindeberg_converges
    (B : MixedExactCycleScalarTriangularArrayData) :
    ∀ epsilon : ℝ, 0 < epsilon →
      HallHeydeScalarConvergesInProbability B.exactCycleCommonMeasure
        (fun n omega =>
          ∑ t : Fin (exactCycleCommonRowLength n),
            B.exactCycleCommonStrictLindebergKernel epsilon n t omega)
        0 := by
  intro epsilon hepsilon delta hdelta
  have hzero :=
    B.exactCycleCommonStrictLindebergSum_eventually_zero epsilon hepsilon
  have hprobabilityZero :
      (fun n => B.exactCycleCommonMeasure
        {omega |
          delta ≤
            |(∑ t : Fin (exactCycleCommonRowLength n),
                B.exactCycleCommonStrictLindebergKernel
                  epsilon n t omega) - 0|}) =ᶠ[atTop]
        (fun _ : ℕ => (0 : ℝ≥0∞)) := by
    filter_upwards [hzero] with n hn
    have hset :
        {omega : (CommonOmega B.repeatedExactCycleData exactCycleIdentityRowSize) |
          delta ≤
            |∑ t : Fin (exactCycleCommonRowLength n),
                B.exactCycleCommonStrictLindebergKernel
                  epsilon n t omega|} = ∅ := by
      ext omega
      simp [hn omega, not_le_of_gt hdelta]
    have hmeasure := congrArg B.exactCycleCommonMeasure hset
    simpa only [sub_zero, measure_empty] using hmeasure
  exact tendsto_const_nhds.congr' hprobabilityZero.symm

/-! ## Exact field identification and reduction -/

/-- Every field of the abstract Hall--Heyde premise record is discharged by
an exact concrete declaration:

* `condition321` by `hallHeydeCondition321`;
* adaptedness by `liftedScore_measurable_succ`;
* integrability by `integrable_mathlibRowMeasure` and
  `liftRowVariable_integrable`;
* martingale differences by `scoreIncrement_literal_condExp_zero` and
  `commonCondExp_lift`;
* predictable variance by
  `squaredScore_literal_condExp_eq_oneShotFisher`, `commonCondExp_lift`, and
  `predictableQuadraticVariation_eq_explicitNormalizedFisher`;
* printed strict-tail Lindeberg by the finite certificate proved above,
  `commonCondExp_lift`, `normalizedFinalScoreIncrement_abs_le_maximumJumpEnvelope`,
  and `maximumJumpEnvelope_tendsto_zero`;
* variance convergence by the sole supplied premise
  `CommonExactCycleFisherConvergesInProbability`.
-/
theorem exactCycleCommonHallHeydePremises
    (B : MixedExactCycleScalarTriangularArrayData)
    (sigmaSq : ℝ) (hsigmaSq : 0 ≤ sigmaSq)
    (hFisher : B.CommonExactCycleFisherConvergesInProbability sigmaSq) :
    HallHeyde1980Corollary31DeterministicVariancePremises
      B.exactCycleCommonMeasure exactCycleCommonRowLength
      B.exactCycleCommonFiltration B.exactCycleCommonScoreIncrement
      B.exactCycleCommonConditionalVariance
      B.exactCycleCommonStrictLindebergKernel sigmaSq := by
  refine
    { condition321 := ?_
      increment_measurable := ?_
      increment_integrable := ?_
      increment_square_integrable := ?_
      martingaleDifference := ?_
      conditionalVarianceVersion := ?_
      conditionalLindebergVersion := ?_
      sigmaSq_nonnegative := hsigmaSq
      conditionalVariance_converges := ?_
      conditionalLindeberg_converges :=
        B.exactCycleCommonStrictLindeberg_converges }
  · intro n k hk hknext
    unfold exactCycleCommonFiltration
    exact hallHeydeCondition321 B.repeatedExactCycleData
      exactCycleIdentityRowSize n k hk hknext
  · intro n t
    exact B.exactCycleCommonScore_measurable_succ n t
  · intro n t
    exact B.exactCycleCommonScore_integrable n t
  · intro n t
    exact B.exactCycleCommonScore_square_integrable n t
  · intro n t
    exact B.exactCycleCommonScore_condExp_zero n t
  · intro n t
    exact B.exactCycleCommonScoreSquare_condExp_eq_fisher n t
  · intro epsilon hepsilon n t
    exact B.exactCycleCommonStrictLindeberg_condExp_eq_kernel
      epsilon hepsilon n t
  · intro epsilon hepsilon
    have h := hFisher epsilon hepsilon
    simpa only [B.exactCycleCommonConditionalVariance_sum_eq_fisher]
      using h

/-- The concrete mixed scalar score CLT conclusion. -/
def MixedExactCycleCommonScalarScoreCLT
    (B : MixedExactCycleScalarTriangularArrayData)
    (sigmaSq : ℝ) : Prop :=
  TendstoInDistribution
    (hallHeydeDeterministicVarianceRowSum exactCycleCommonRowLength
      B.exactCycleCommonScoreIncrement)
    atTop id (fun _ => B.exactCycleCommonMeasure)
    (gaussianReal 0 sigmaSq.toNNReal)

/-- Item 1: an arbitrary term of the inspectable Hall--Heyde statement,
together with only explicit Fisher convergence, yields the mixed exact-cycle
scalar score CLT. -/
theorem mixedExactCycleCommonScalarScoreCLT_of_statement
    (B : MixedExactCycleScalarTriangularArrayData)
    (hHallHeyde :
      HallHeyde1980Corollary31DeterministicVarianceStatement.{0})
    (sigmaSq : ℝ) (hsigmaSq : 0 ≤ sigmaSq)
    (hFisher : B.CommonExactCycleFisherConvergesInProbability sigmaSq) :
    B.MixedExactCycleCommonScalarScoreCLT sigmaSq := by
  exact hHallHeyde B.exactCycleCommonMeasure
    exactCycleCommonRowLength B.exactCycleCommonFiltration
    B.exactCycleCommonScoreIncrement
    B.exactCycleCommonConditionalVariance
    B.exactCycleCommonStrictLindebergKernel sigmaSq
    (B.exactCycleCommonHallHeydePremises sigmaSq hsigmaSq hFisher)

/-- The paper data already stores nonnegativity of its proposed scalar target
variance, so the usual target-variance specialization needs no extra premise. -/
theorem mixedExactCycleTargetVarianceScoreCLT_of_statement
    (B : MixedExactCycleScalarTriangularArrayData)
    (hHallHeyde :
      HallHeyde1980Corollary31DeterministicVarianceStatement.{0})
    (hFisher : B.CommonExactCycleFisherConvergesInProbability
      B.targetVariance) :
    B.MixedExactCycleCommonScalarScoreCLT B.targetVariance :=
  B.mixedExactCycleCommonScalarScoreCLT_of_statement hHallHeyde
    B.targetVariance B.targetVariance_nonnegative hFisher

/-! ## Separate zero-variance and zero-direction handling -/

/-- Zero deterministic variance is included explicitly; no positivity premise
is hidden in the approval contract. -/
theorem mixedExactCycleZeroVarianceScoreCLT_of_statement
    (B : MixedExactCycleScalarTriangularArrayData)
    (hHallHeyde :
      HallHeyde1980Corollary31DeterministicVarianceStatement.{0})
    (hFisherZero :
      B.CommonExactCycleFisherConvergesInProbability 0) :
    B.MixedExactCycleCommonScalarScoreCLT 0 :=
  B.mixedExactCycleCommonScalarScoreCLT_of_statement
    hHallHeyde 0 le_rfl hFisherZero

/-- A zero local direction makes every normalized score increment exactly
zero, before taking any limit. -/
theorem exactCycleCommonScoreIncrement_eq_zero_of_direction_eq_zero
    (B : MixedExactCycleScalarTriangularArrayData)
    (hDirection : B.direction = (0 : Fin 3 → ℝ))
    (n : ℕ) (t : Fin (exactCycleCommonRowLength n))
    (omega : (CommonOmega B.repeatedExactCycleData exactCycleIdentityRowSize)) :
    B.exactCycleCommonScoreIncrement n t omega = 0 := by
  simp [exactCycleCommonScoreIncrement, liftRowVariable,
    currentCoordinateObservable, scoreObservable,
    normalizedFinalScoreIncrement,
    mixedTwoStageFinalShotDirectionalScore,
    mixedTwoStageAxisDirectionalScore, hDirection,
    QubitOracle.blochDot]

/-- Consequently every terminal row score is exactly zero. -/
theorem exactCycleCommonRowSum_eq_zero_of_direction_eq_zero
    (B : MixedExactCycleScalarTriangularArrayData)
    (hDirection : B.direction = (0 : Fin 3 → ℝ))
    (n : ℕ) (omega : (CommonOmega B.repeatedExactCycleData exactCycleIdentityRowSize)) :
    hallHeydeDeterministicVarianceRowSum exactCycleCommonRowLength
      B.exactCycleCommonScoreIncrement n omega = 0 := by
  unfold hallHeydeDeterministicVarianceRowSum
  apply Finset.sum_eq_zero
  intro t _ht
  exact B.exactCycleCommonScoreIncrement_eq_zero_of_direction_eq_zero
    hDirection n t omega

/-- The explicit normalized Fisher expression is also exactly zero in the
zero direction. -/
theorem explicitNormalizedFisher_eq_zero_of_direction_eq_zero
    (B : MixedExactCycleScalarTriangularArrayData)
    (hDirection : B.direction = (0 : Fin 3 → ℝ))
    (r : ℕ) (pilot : B.PilotSpace r) :
    B.explicitNormalizedFisher r pilot = 0 := by
  simp [explicitNormalizedFisher,
    mixedExactCycleNormalizedDirectionalFisher,
    mixedExactCycleOneShotNormalizedDirectionalFisher,
    hDirection, QubitOracle.blochDot]

/-- Zero direction supplies the zero-Fisher convergence premise without an
asymptotic assumption. -/
theorem commonExactCycleFisherConvergesInProbability_zero_of_direction_eq_zero
    (B : MixedExactCycleScalarTriangularArrayData)
    (hDirection : B.direction = (0 : Fin 3 → ℝ)) :
    B.CommonExactCycleFisherConvergesInProbability 0 := by
  intro epsilon hepsilon
  simpa [CommonExactCycleFisherConvergesInProbability,
    HallHeydeScalarConvergesInProbability,
    B.explicitNormalizedFisher_eq_zero_of_direction_eq_zero
      hDirection,
    not_le_of_gt hepsilon] using
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (nhds 0))

/-- Item 2: exact zero-direction CLT handling. The row sum is already
pointwise zero, and the abstract statement is applied only with variance zero. -/
theorem mixedExactCycleZeroDirectionScoreCLT_of_statement
    (B : MixedExactCycleScalarTriangularArrayData)
    (hHallHeyde :
      HallHeyde1980Corollary31DeterministicVarianceStatement.{0})
    (hDirection : B.direction = (0 : Fin 3 → ℝ)) :
    B.MixedExactCycleCommonScalarScoreCLT 0 :=
  B.mixedExactCycleZeroVarianceScoreCLT_of_statement hHallHeyde
    (B.commonExactCycleFisherConvergesInProbability_zero_of_direction_eq_zero
      hDirection)

/-! ## Source-faithful unconditional wrappers -/

/-- The concrete scalar score CLT with arbitrary deterministic variance,
using exactly the shared Hall--Heyde Corollary 3.1 atom. -/
theorem mixedExactCycleCommonScalarScoreCLT_of_hallHeyde
    (B : MixedExactCycleScalarTriangularArrayData)
    (sigmaSq : ℝ) (hsigmaSq : 0 ≤ sigmaSq)
    (hFisher : B.CommonExactCycleFisherConvergesInProbability sigmaSq) :
    B.MixedExactCycleCommonScalarScoreCLT sigmaSq :=
  B.mixedExactCycleCommonScalarScoreCLT_of_statement
    hallHeyde1980_corollary3_1_deterministicVariance_external
    sigmaSq hsigmaSq hFisher

/-- Target-variance specialization of the concrete scalar score CLT. -/
theorem mixedExactCycleTargetScoreCLT_of_hallHeyde
    (B : MixedExactCycleScalarTriangularArrayData)
    (hFisher : B.CommonExactCycleFisherConvergesInProbability
      B.targetVariance) :
    B.MixedExactCycleCommonScalarScoreCLT B.targetVariance :=
  B.mixedExactCycleTargetVarianceScoreCLT_of_statement
    hallHeyde1980_corollary3_1_deterministicVariance_external hFisher

/-- Zero-variance specialization of the concrete scalar score CLT. -/
theorem mixedExactCycleZeroVarianceScoreCLT_of_hallHeyde
    (B : MixedExactCycleScalarTriangularArrayData)
    (hFisherZero : B.CommonExactCycleFisherConvergesInProbability 0) :
    B.MixedExactCycleCommonScalarScoreCLT 0 :=
  B.mixedExactCycleZeroVarianceScoreCLT_of_statement
    hallHeyde1980_corollary3_1_deterministicVariance_external hFisherZero

/-- Zero-direction specialization; Fisher convergence is proved pointwise. -/
theorem mixedExactCycleZeroDirectionScoreCLT_of_hallHeyde
    (B : MixedExactCycleScalarTriangularArrayData)
    (hDirection : B.direction = (0 : Fin 3 → ℝ)) :
    B.MixedExactCycleCommonScalarScoreCLT 0 :=
  B.mixedExactCycleZeroDirectionScoreCLT_of_statement
    hallHeyde1980_corollary3_1_deterministicVariance_external hDirection

end MixedExactCycleScalarTriangularArrayData

end

end QubitOracle.Paper
