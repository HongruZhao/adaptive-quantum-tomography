import QubitOracle.Paper.TerminalEstimatorDefinitions
import QubitOracle.Paper.CanonicalFloorLabels
import QubitOracle.Paper.MixedProbabilityFloor

/-!
# Safeguard and regular-event proofs

This file formalizes the deterministic and event-algebra layer of
Supplementary Notes 6 and 9.  It deliberately does not assume a concentration
conclusion.  Instead, the probability assembly theorems take finite-sample
bounds for the four primitive component events and derive the bound for their
intersection.

No scientific axiom is introduced here.
-/

namespace QubitOracle.Paper

open Filter Set Topology

noncomputable section

/-! ## A minimal probability envelope

The safeguard proofs use only positivity, monotonicity, and the union bound.
Packaging precisely those properties keeps the event algebra independent of a
particular measure representation while remaining instantiable by ordinary
probability measures.
-/

structure ProbabilityEnvelope (Omega : Type*) where
  probability : Set Omega -> Real
  nonnegative : forall A, 0 <= probability A
  monotone : forall {A B}, A ⊆ B -> probability A <= probability B
  union_le : forall A B, probability (A ∪ B) <= probability A + probability B

/-- The complement of the four-component event is the union of the four bad
component events. -/
theorem terminalGoodEvent_compl_eq_union_compls
    {Omega : Type*} (controller regular score hessian : Set Omega) :
    (terminalGoodEvent controller regular score hessian)ᶜ =
      controllerᶜ ∪ regularᶜ ∪ scoreᶜ ∪ hessianᶜ := by
  ext omega
  simp only [terminalGoodEvent, Set.mem_compl_iff, Set.mem_inter_iff,
    Set.mem_union]
  tauto

/-- Four applications of the union bound control the complement of the
regular event. -/
theorem probability_terminalGoodEvent_compl_le
    {Omega : Type*} (P : ProbabilityEnvelope Omega)
    (controller regular score hessian : Set Omega) :
    P.probability (terminalGoodEvent controller regular score hessian)ᶜ <=
      P.probability controllerᶜ + P.probability regularᶜ +
        P.probability scoreᶜ + P.probability hessianᶜ := by
  rw [terminalGoodEvent_compl_eq_union_compls]
  calc
    P.probability (controllerᶜ ∪ regularᶜ ∪ scoreᶜ ∪ hessianᶜ) <=
        P.probability (controllerᶜ ∪ regularᶜ ∪ scoreᶜ) +
          P.probability hessianᶜ := P.union_le _ _
    _ <= (P.probability (controllerᶜ ∪ regularᶜ) +
          P.probability scoreᶜ) + P.probability hessianᶜ := by
      gcongr
      exact P.union_le _ _
    _ <= ((P.probability controllerᶜ + P.probability regularᶜ) +
          P.probability scoreᶜ) + P.probability hessianᶜ := by
      gcongr
      exact P.union_le _ _
    _ = P.probability controllerᶜ + P.probability regularᶜ +
          P.probability scoreᶜ + P.probability hessianᶜ := by ring

/-- A nonnegative quantity squeezed below a vanishing upper envelope also
vanishes. -/
theorem tendsto_zero_of_nonnegative_of_le
    (p upper : Nat -> Real)
    (hp : ∀ n, 0 <= p n)
    (hle : ∀ᶠ n in atTop, p n <= upper n)
    (hupper : Tendsto upper atTop (nhds 0)) :
    Tendsto p atTop (nhds 0) := by
  exact squeeze_zero' (Filter.Eventually.of_forall hp) hle hupper

/-! ## Retained-index and denominator safety -/

/-- A retained index is after the burn-in cutoff, at most the endpoint, and
is not an exploration round. -/
theorem retainedIndex_is_postBurnIn_nonexploration
    (n : Nat) (exploration : Nat -> Nat) (i : Nat)
    (hi : i ∈ terminalTailSet n exploration) :
    terminalBurnInCutoff n < i ∧ i <= n ∧ exploration i = 0 :=
  (mem_terminalTailSet_iff n exploration i).1 hi

/-- Every retained binary likelihood denominator inherits a common positive
margin from a scalar overlap bound. -/
theorem retained_binary_denominator_lower_bound
    {Omega : Type*} (n : Nat) (exploration : Nat -> Nat)
    (z : Nat -> Omega -> Real) (outcome : Nat -> BinaryOutcome)
    (regular : Set Omega) (s : Real)
    (hz : ∀ omega ∈ regular, ∀ i ∈ terminalTailSet n exploration,
      |z i omega| <= s) :
    ∀ omega ∈ regular, ∀ i ∈ terminalTailSet n exploration,
      1 - s <= 1 + (outcome i).sign * z i omega := by
  intro omega homega i hi
  exact signed_denominator_lower_bound (z i omega) s (hz omega homega i hi) (outcome i)

/-- If the common overlap radius is strictly interior, every retained Born
probability is strictly positive. -/
theorem retained_binary_probability_pos
    {Omega : Type*} (n : Nat) (exploration : Nat -> Nat)
    (z : Nat -> Omega -> Real) (outcome : Nat -> BinaryOutcome)
    (regular : Set Omega) (s : Real) (hs : s < 1)
    (hz : ∀ omega ∈ regular, ∀ i ∈ terminalTailSet n exploration,
      |z i omega| <= s) :
    ∀ omega ∈ regular, ∀ i ∈ terminalTailSet n exploration,
      0 < binaryBornProbability (z i omega) (outcome i) := by
  intro omega homega i hi
  exact binaryBornProbability_pos (z i omega) s (hz omega homega i hi) hs (outcome i)

/-! ## Floor projection -/

/-- Main-text floor projection, parameterized by the Euclidean-ball projection
operator used by the implementation. -/
def floorProjectedController
    {E : Type*} (project : Real -> E -> E)
    (eta : Nat -> Real) (raw : Nat -> E) (n : Nat) : E :=
  project (1 - 2 * eta n) (raw n)

/-- The strict-interior estimate used in Eq. S24, including the complete
three-term comparison displayed in the supplement. -/
theorem floor_inside_chain
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (raw truth : E) (eta : Real)
    (hinterior : ‖truth‖ < 1)
    (hraw : ‖raw - truth‖ < (1 - ‖truth‖) / 4)
    (heta : 2 * eta < (1 - ‖truth‖) / 4) :
    ‖raw‖ < ‖truth‖ + (1 - ‖truth‖) / 4 ∧
      ‖truth‖ + (1 - ‖truth‖) / 4 =
        1 - 3 * (1 - ‖truth‖) / 4 ∧
      1 - 3 * (1 - ‖truth‖) / 4 < 1 - 2 * eta := by
  have htriangle : ‖raw‖ <= ‖raw - truth‖ + ‖truth‖ := by
    calc
      ‖raw‖ = ‖(raw - truth) + truth‖ := by congr 1 <;> abel
      _ <= ‖raw - truth‖ + ‖truth‖ := norm_add_le _ _
  constructor
  · linarith
  constructor
  · ring
  · have hgap : 0 < 1 - ‖truth‖ := by linarith
    linarith

/-- The main-text floor is eventually inactive under the already verified
interior-consistency hypotheses. -/
theorem floorProjectedController_eventually_eq_raw
    {E : Type} [NormedAddCommGroup E] [NormedSpace Real E]
    (project : Real -> E -> E)
    (fixesInterior : forall r z, ‖z‖ < r -> project r z = z)
    (raw : Nat -> E) (truth : E) (eta : Nat -> Real)
    (hraw : Tendsto raw atTop (nhds truth))
    (heta : Tendsto eta atTop (nhds 0))
    (hinterior : ‖truth‖ < 1) :
    ∀ᶠ n in atTop,
      floorProjectedController project eta raw n = raw n := by
  simpa [floorProjectedController] using
    eventually_floor_projection_inactive
      project fixesInterior raw truth eta hraw heta hinterior

/-! ## Exact safeguard definitions -/

/-- The Hessian cutoff `n / log n` used by the terminal safeguard. -/
def paperHessianThreshold (n : Nat) : Real :=
  (n : Real) / Real.log (n : Real)

/-- The shrinking safeguard radius
`min(1/2, (log n / E_n)^(1/4))`. -/
def paperSafeguardRadius (expectedExploration : Nat -> Real) (n : Nat) : Real :=
  min (1 / 2 : Real)
    (Real.rpow (Real.log (n : Real) / expectedExploration n) (1 / 4 : Real))

/-- Event on which the Hessian cutoff rejects the unsafeguarded update. -/
def hessianSafeguardBadEvent
    {Omega : Type*} (curvature : Nat -> Omega -> Real) (n : Nat) : Set Omega :=
  {omega | curvature n omega <= paperHessianThreshold n}

/-- Event on which the Newton correction is larger than the shrinking
safeguard neighborhood. -/
def stepSafeguardBadEvent
    {Omega : Type*} (expectedExploration : Nat -> Real)
    (stepSize : Nat -> Omega -> Real) (n : Nat) : Set Omega :=
  {omega | paperSafeguardRadius expectedExploration n < stepSize n omega}

/-- The safeguard accepts exactly when neither rejection rule fires. -/
def safeguardAcceptEvent
    {Omega : Type*} (expectedExploration : Nat -> Real)
    (curvature stepSize : Nat -> Omega -> Real) (n : Nat) : Set Omega :=
  {omega | paperHessianThreshold n < curvature n omega ∧
    stepSize n omega <= paperSafeguardRadius expectedExploration n}

/-- Safeguarded estimator: use the Newton output on the acceptance event and
otherwise return the prescribed physical fallback. -/
def paperSafeguardedEstimator
    {Omega E : Type*} (accept : Set Omega) (raw fallback : Omega -> E) : Omega -> E :=
  by
    classical
    exact fun omega => if omega ∈ accept then raw omega else fallback omega

@[simp] theorem paperSafeguardedEstimator_eq_raw_of_mem
    {Omega E : Type*} (accept : Set Omega) (raw fallback : Omega -> E)
    {omega : Omega} (homega : omega ∈ accept) :
    paperSafeguardedEstimator accept raw fallback omega = raw omega := by
  simp [paperSafeguardedEstimator, homega]

/-- The complement of the acceptance event is exactly the union of the two
rejection events. -/
theorem safeguardAcceptEvent_compl_eq_bad_union
    {Omega : Type*} (expectedExploration : Nat -> Real)
    (curvature stepSize : Nat -> Omega -> Real) (n : Nat) :
    (safeguardAcceptEvent expectedExploration curvature stepSize n)ᶜ =
      hessianSafeguardBadEvent curvature n ∪
        stepSafeguardBadEvent expectedExploration stepSize n := by
  ext omega
  change
    (¬ (paperHessianThreshold n < curvature n omega ∧
      stepSize n omega <= paperSafeguardRadius expectedExploration n)) ↔
      curvature n omega <= paperHessianThreshold n ∨
        paperSafeguardRadius expectedExploration n < stepSize n omega
  constructor
  · intro h
    by_cases hc : paperHessianThreshold n < curvature n omega
    · right
      exact lt_of_not_ge (fun hs => h ⟨hc, hs⟩)
    · left
      exact le_of_not_gt hc
  · intro h haccept
    rcases h with hcurv | hstep
    · exact (not_lt_of_ge hcurv) haccept.1
    · exact (not_lt_of_ge haccept.2) hstep

/-! ## Deterministic inverse-score control -/

/-- Primitive scalar bounds extracted from a positive Hessian inverse and a
Taylor bound for the score.  This is the non-probabilistic content needed for
Eqs. S73 and S89. -/
structure NewtonPrimitiveBounds
    (normalizer delta constant remainder inverseNorm scoreNorm stepNorm : Real) : Prop where
  normalizer_pos : 0 < normalizer
  delta_nonnegative : 0 <= delta
  constant_nonnegative : 0 <= constant
  remainder_nonnegative : 0 <= remainder
  inverse_nonnegative : 0 <= inverseNorm
  score_nonnegative : 0 <= scoreNorm
  step_le_product : stepNorm <= inverseNorm * scoreNorm
  inverse_le : inverseNorm <= normalizer⁻¹
  score_le : scoreNorm <=
    normalizer * (delta + constant * (remainder + delta ^ 2))

/-- Primitive inverse-Hessian and score bounds imply the Newton-size bound;
no asymptotic conclusion is assumed. -/
theorem newton_size_bound_of_primitive
    {normalizer delta constant remainder inverseNorm scoreNorm stepNorm : Real}
    (h : NewtonPrimitiveBounds normalizer delta constant remainder
      inverseNorm scoreNorm stepNorm) :
    stepNorm <= delta + constant * (remainder + delta ^ 2) := by
  calc
    stepNorm <= inverseNorm * scoreNorm := h.step_le_product
    _ <= normalizer⁻¹ * scoreNorm :=
      mul_le_mul_of_nonneg_right h.inverse_le h.score_nonnegative
    _ <= normalizer⁻¹ *
        (normalizer * (delta + constant * (remainder + delta ^ 2))) :=
      mul_le_mul_of_nonneg_left h.score_le
        (inv_nonneg.mpr (le_of_lt h.normalizer_pos))
    _ = delta + constant * (remainder + delta ^ 2) := by
      field_simp [ne_of_gt h.normalizer_pos]

/-- A regular event on which the deterministic Newton envelope fits within
its safeguard radius cannot contain a step-rejection outcome. -/
theorem stepSafeguardBadEvent_subset_regular_compl
    {Omega : Type*} (expectedExploration : Nat -> Real)
    (stepSize : Nat -> Omega -> Real) (regular : Set Omega) (n : Nat)
    (delta inverseNorm scoreNorm : Omega -> Real) (constant remainder : Real)
    (hprimitive : ∀ omega ∈ regular,
      NewtonPrimitiveBounds (n : Real) (delta omega) constant remainder
        (inverseNorm omega) (scoreNorm omega) (stepSize n omega))
    (henvelope : ∀ omega ∈ regular,
      delta omega + constant * (remainder + (delta omega) ^ 2) <=
        paperSafeguardRadius expectedExploration n) :
    stepSafeguardBadEvent expectedExploration stepSize n ⊆ regularᶜ := by
  intro omega hbad hregular
  have hstep := newton_size_bound_of_primitive (hprimitive omega hregular)
  have hsafe := le_trans hstep (henvelope omega hregular)
  exact (not_lt_of_ge hsafe) hbad

/-- A regular event with curvature above the cutoff cannot contain a
Hessian-rejection outcome. -/
theorem hessianSafeguardBadEvent_subset_regular_compl
    {Omega : Type*} (curvature : Nat -> Omega -> Real)
    (regular : Set Omega) (n : Nat)
    (hcurvature : ∀ omega ∈ regular,
      paperHessianThreshold n < curvature n omega) :
    hessianSafeguardBadEvent curvature n ⊆ regularᶜ := by
  intro omega hbad hregular
  exact (not_lt_of_ge hbad) (hcurvature omega hregular)

/-! ## Concrete component events for the polynomial regular event -/

/-- Controller component of the good event. -/
def controllerFiniteBoundEvent
    {Omega : Type*} (controllerError controllerBound : Nat -> Omega -> Real)
    (n : Nat) : Set Omega :=
  {omega | controllerError n omega <= controllerBound n omega}

/-- Score component of the good event. -/
def scoreHighProbabilityEvent
    {Omega : Type*} (scoreSize scoreBound : Nat -> Omega -> Real)
    (n : Nat) : Set Omega :=
  {omega | scoreSize n omega <= scoreBound n omega}

/-- Hessian component of the good event, uniformly over the local parameter
set after taking the infimum in the scalar `curvature` statistic. -/
def uniformHessianEvent
    {Omega : Type*} (curvature lowerBound : Nat -> Omega -> Real)
    (n : Nat) : Set Omega :=
  {omega | lowerBound n omega <= curvature n omega}

/-- Fully instantiated four-component event of Supplementary Note 9. -/
def paperRegularEvent
    {Omega : Type*}
    (controller regular score hessian : Nat -> Set Omega) (n : Nat) : Set Omega :=
  terminalGoodEvent (controller n) (regular n) (score n) (hessian n)

/-- Exact finite-sample polynomial envelope used in place of informal
`O(n^{-r})` notation. -/
def polynomialTailEnvelope (constant : Real) (order n : Nat) : Real :=
  constant / ((n + 1 : Nat) : Real) ^ order

/-- The four component-tail bounds imply the polynomial bound for their
intersection. -/
theorem regularEvent_probability_bound_of_component_tails
    {Omega : Type*} (P : ProbabilityEnvelope Omega)
    (controller regular score hessian : Nat -> Set Omega)
    (Ccontroller Cregular Cscore Chessian : Real) (order n : Nat)
    (hcontroller : P.probability (controller n)ᶜ <=
      polynomialTailEnvelope Ccontroller order n)
    (hregular : P.probability (regular n)ᶜ <=
      polynomialTailEnvelope Cregular order n)
    (hscore : P.probability (score n)ᶜ <=
      polynomialTailEnvelope Cscore order n)
    (hhessian : P.probability (hessian n)ᶜ <=
      polynomialTailEnvelope Chessian order n) :
    P.probability (paperRegularEvent controller regular score hessian n)ᶜ <=
      polynomialTailEnvelope
        (Ccontroller + Cregular + Cscore + Chessian) order n := by
  calc
    P.probability (paperRegularEvent controller regular score hessian n)ᶜ <=
        P.probability (controller n)ᶜ + P.probability (regular n)ᶜ +
          P.probability (score n)ᶜ + P.probability (hessian n)ᶜ :=
      probability_terminalGoodEvent_compl_le P _ _ _ _
    _ <= polynomialTailEnvelope Ccontroller order n +
          polynomialTailEnvelope Cregular order n +
          polynomialTailEnvelope Cscore order n +
          polynomialTailEnvelope Chessian order n := by linarith
    _ = polynomialTailEnvelope
          (Ccontroller + Cregular + Cscore + Chessian) order n := by
      simp only [polynomialTailEnvelope]
      ring

/-- Membership in the assembled event exposes all four primitive regularity
properties simultaneously. -/
theorem mem_paperRegularEvent_iff
    {Omega : Type*} (controller regular score hessian : Nat -> Set Omega)
    (n : Nat) (omega : Omega) :
    omega ∈ paperRegularEvent controller regular score hessian n ↔
      omega ∈ controller n ∧ omega ∈ regular n ∧
        omega ∈ score n ∧ omega ∈ hessian n := by
  simp [paperRegularEvent, terminalGoodEvent, and_assoc]

/-! ## Elementary curvature transfer -/

/-- A truth-Hessian lower bound and a Lipschitz perturbation bound imply a
uniform local-Hessian lower bound. -/
theorem uniform_curvature_lower_bound
    (normalizer populationGap perturbation truthCurvature localCurvature : Real)
    (hn : 0 <= normalizer)
    (hgap : 0 <= populationGap)
    (htruth : populationGap * normalizer <= truthCurvature)
    (hperturb : truthCurvature - perturbation <= localCurvature)
    (hsmall : perturbation <= populationGap * normalizer / 2) :
    populationGap * normalizer / 2 <= localCurvature := by
  linarith

/-! ## Bad-event moment transfer -/

/-- The only expectation properties needed for the bounded bad-event
argument: monotonicity and evaluation of constant indicators. -/
structure PositiveExpectation (Omega : Type*) where
  expectation : (Omega -> Real) -> Real
  probability : Set Omega -> Real
  monotone : forall {f g : Omega -> Real},
    (forall omega, f omega <= g omega) -> expectation f <= expectation g
  indicator_const : forall (A : Set Omega) (c : Real),
    expectation (A.indicator (fun _ => c)) = c * probability A

/-- Moment contribution restricted to an event. -/
def restrictedMoment
    {Omega E : Type*} [SeminormedAddGroup E] (bad : Set Omega) (W : Omega -> E)
    (moment : Nat) : Omega -> Real :=
  bad.indicator (fun omega => ‖W omega‖ ^ moment)

/-- Bounded physical errors turn a bad-event probability bound into the
finite-sample moment estimate used in Eq. S96. -/
theorem bad_event_moment_le_probability
    {Omega E : Type*} [SeminormedAddGroup E] (Exp : PositiveExpectation Omega)
    (bad : Set Omega) (W : Omega -> E) (moment : Nat)
    (bound : Real) (hbound : ∀ omega, ‖W omega‖ <= bound) :
    Exp.expectation (restrictedMoment bad W moment) <=
      bound ^ moment * Exp.probability bad := by
  calc
    Exp.expectation (restrictedMoment bad W moment) <=
        Exp.expectation (bad.indicator (fun _ => bound ^ moment)) := by
      apply Exp.monotone
      intro omega
      by_cases homega : omega ∈ bad
      · simp only [restrictedMoment, Set.indicator_of_mem homega]
        exact pow_le_pow_left₀ (norm_nonneg (W omega)) (hbound omega) moment
      · simp [restrictedMoment, homega]
    _ = bound ^ moment * Exp.probability bad :=
      Exp.indicator_const bad (bound ^ moment)

namespace Label

/-- Main equation `eq:floor_projection`. -/
theorem eq_floor_projection
    {E : Type*} (project : Real -> E -> E)
    (eta : Nat -> Real) (raw : Nat -> E) (n : Nat) :
    floorProjectedController project eta raw n =
      project (1 - 2 * eta n) (raw n) :=
  rfl

/-- Supplement equation `eq:SI_floor_inside`. -/
theorem eq_SI_floor_inside
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (raw truth : E) (eta : Real)
    (hinterior : ‖truth‖ < 1)
    (hraw : ‖raw - truth‖ < (1 - ‖truth‖) / 4)
    (heta : 2 * eta < (1 - ‖truth‖) / 4) :
    ‖raw‖ < ‖truth‖ + (1 - ‖truth‖) / 4 ∧
      ‖truth‖ + (1 - ‖truth‖) / 4 =
        1 - 3 * (1 - ‖truth‖) / 4 ∧
      1 - 3 * (1 - ‖truth‖) / 4 < 1 - 2 * eta :=
  floor_inside_chain raw truth eta hinterior hraw heta

/-- Supplement equation `eq:SI_general_newton_size`, derived from primitive
inverse-Hessian and Taylor-score bounds. -/
theorem eq_SI_general_newton_size
    {normalizer delta constant inverseNorm scoreNorm stepNorm : Real}
    (h : NewtonPrimitiveBounds normalizer delta constant
      (Real.sqrt normalizer)⁻¹ inverseNorm scoreNorm stepNorm) :
    stepNorm <= delta + constant *
      ((Real.sqrt normalizer)⁻¹ + delta ^ 2) :=
  newton_size_bound_of_primitive h

/-- Supplement equation `eq:SI_newton_size_bound`, with the explicit
`sqrt(log n / n)` remainder. -/
theorem eq_SI_newton_size_bound
    {n : Nat} {delta constant inverseNorm scoreNorm stepNorm : Real}
    (h : NewtonPrimitiveBounds (n : Real) delta constant
      (Real.sqrt (Real.log (n : Real) / (n : Real)))
      inverseNorm scoreNorm stepNorm) :
    stepNorm <= delta + constant *
      (Real.sqrt (Real.log (n : Real) / (n : Real)) + delta ^ 2) :=
  newton_size_bound_of_primitive h

/-- Supplement equation `eq:SI_safeguard_hessian_general`: a primitive
regular-event curvature bound and a vanishing component tail imply that the
Hessian safeguard rejects with probability tending to zero. -/
theorem eq_SI_safeguard_hessian_general
    {Omega : Type*} (P : ProbabilityEnvelope Omega)
    (curvature : Nat -> Omega -> Real) (regular : Nat -> Set Omega)
    (tail : Nat -> Real)
    (hcurvature : ∀ᶠ n in atTop, ∀ omega ∈ regular n,
      paperHessianThreshold n < curvature n omega)
    (htailBound : forall n, P.probability (regular n)ᶜ <= tail n)
    (htail : Tendsto tail atTop (nhds 0)) :
    Tendsto (fun n => P.probability (hessianSafeguardBadEvent curvature n))
      atTop (nhds 0) := by
  apply tendsto_zero_of_nonnegative_of_le
  · intro n
    exact P.nonnegative _
  · filter_upwards [hcurvature] with n hn
    exact le_trans
      (P.monotone (hessianSafeguardBadEvent_subset_regular_compl
        curvature (regular n) n hn))
      (htailBound n)
  · exact htail

/-- Supplement equation `eq:SI_safeguard_step_general`: primitive
inverse/score bounds, a deterministic shrinking-radius comparison, and a
vanishing component tail imply that step rejection vanishes. -/
theorem eq_SI_safeguard_step_general
    {Omega : Type*} (P : ProbabilityEnvelope Omega)
    (expectedExploration : Nat -> Real)
    (stepSize delta inverseNorm scoreNorm : Nat -> Omega -> Real)
    (constant remainder tail : Nat -> Real) (regular : Nat -> Set Omega)
    (hprimitive : ∀ᶠ n in atTop, ∀ omega ∈ regular n,
      NewtonPrimitiveBounds (n : Real) (delta n omega) (constant n)
        (remainder n) (inverseNorm n omega) (scoreNorm n omega)
        (stepSize n omega))
    (henvelope : ∀ᶠ n in atTop, ∀ omega ∈ regular n,
      delta n omega + constant n * (remainder n + (delta n omega) ^ 2) <=
        paperSafeguardRadius expectedExploration n)
    (htailBound : forall n, P.probability (regular n)ᶜ <= tail n)
    (htail : Tendsto tail atTop (nhds 0)) :
    Tendsto (fun n => P.probability
      (stepSafeguardBadEvent expectedExploration stepSize n))
      atTop (nhds 0) := by
  apply tendsto_zero_of_nonnegative_of_le
  · intro n
    exact P.nonnegative _
  · filter_upwards [hprimitive, henvelope] with n hp he
    exact le_trans
      (P.monotone (stepSafeguardBadEvent_subset_regular_compl
        expectedExploration stepSize (regular n) n
        (delta n) (inverseNorm n) (scoreNorm n) (constant n) (remainder n)
        hp he))
      (htailBound n)
  · exact htail

/-- Supplement lemma `lem:SI_safeguard_general`: both rejection
probabilities vanish and therefore safeguard disagreement with the raw
Newton estimator also vanishes. -/
theorem lem_SI_safeguard_general
    {Omega E : Type*} (P : ProbabilityEnvelope Omega)
    (expectedExploration : Nat -> Real)
    (curvature stepSize : Nat -> Omega -> Real)
    (raw fallback : Nat -> Omega -> E)
    (hHessian : Tendsto
      (fun n => P.probability (hessianSafeguardBadEvent curvature n))
      atTop (nhds 0))
    (hStep : Tendsto
      (fun n => P.probability
        (stepSafeguardBadEvent expectedExploration stepSize n))
      atTop (nhds 0)) :
    Tendsto (fun n => P.probability
      {omega | paperSafeguardedEstimator
          (safeguardAcceptEvent expectedExploration curvature stepSize n)
          (raw n) (fallback n) omega ≠ raw n omega})
      atTop (nhds 0) := by
  apply tendsto_zero_of_nonnegative_of_le
  · intro n
    exact P.nonnegative _
  · exact Filter.Eventually.of_forall (fun n =>
      le_trans (P.monotone (by
        intro omega hne
        have hnot : omega ∉ safeguardAcceptEvent
            expectedExploration curvature stepSize n := by
          intro hmem
          exact hne (paperSafeguardedEstimator_eq_raw_of_mem
            _ _ _ hmem)
        have hcompl : omega ∈
            (safeguardAcceptEvent expectedExploration curvature stepSize n)ᶜ :=
          hnot
        rw [safeguardAcceptEvent_compl_eq_bad_union] at hcompl
        exact hcompl))
        (P.union_le _ _))
  · simpa using hHessian.add hStep

/-- Supplement lemma `lem:SI_regular_event`: exact decomposition, simultaneous
component membership, and the finite polynomial complement bound. -/
theorem lem_SI_regular_event
    {Omega : Type*} (P : ProbabilityEnvelope Omega)
    (controller regular score hessian : Nat -> Set Omega)
    (Ccontroller Cregular Cscore Chessian : Real) (order n : Nat)
    (hcontroller : P.probability (controller n)ᶜ <=
      polynomialTailEnvelope Ccontroller order n)
    (hregular : P.probability (regular n)ᶜ <=
      polynomialTailEnvelope Cregular order n)
    (hscore : P.probability (score n)ᶜ <=
      polynomialTailEnvelope Cscore order n)
    (hhessian : P.probability (hessian n)ᶜ <=
      polynomialTailEnvelope Chessian order n) :
    paperRegularEvent controller regular score hessian n =
        terminalGoodEvent (controller n) (regular n) (score n) (hessian n) ∧
      P.probability (paperRegularEvent controller regular score hessian n)ᶜ <=
        polynomialTailEnvelope
          (Ccontroller + Cregular + Cscore + Chessian) order n ∧
      (∀ omega ∈ paperRegularEvent controller regular score hessian n,
        omega ∈ controller n ∧ omega ∈ regular n ∧
          omega ∈ score n ∧ omega ∈ hessian n) := by
  refine ⟨rfl, ?_, ?_⟩
  · exact regularEvent_probability_bound_of_component_tails
      P controller regular score hessian
      Ccontroller Cregular Cscore Chessian order n
      hcontroller hregular hscore hhessian
  · intro omega homega
    exact (mem_paperRegularEvent_iff controller regular score hessian n omega).1 homega

/-- Supplement equation `eq:SI_regular_event_probability`, represented by a
finite bound stronger than the manuscript's `O(n^{-r})` notation. -/
theorem eq_SI_regular_event_probability
    {Omega : Type*} (P : ProbabilityEnvelope Omega)
    (controller regular score hessian : Nat -> Set Omega)
    (Ccontroller Cregular Cscore Chessian : Real) (order n : Nat)
    (hcontroller : P.probability (controller n)ᶜ <=
      polynomialTailEnvelope Ccontroller order n)
    (hregular : P.probability (regular n)ᶜ <=
      polynomialTailEnvelope Cregular order n)
    (hscore : P.probability (score n)ᶜ <=
      polynomialTailEnvelope Cscore order n)
    (hhessian : P.probability (hessian n)ᶜ <=
      polynomialTailEnvelope Chessian order n) :
    P.probability (paperRegularEvent controller regular score hessian n)ᶜ <=
      polynomialTailEnvelope
        (Ccontroller + Cregular + Cscore + Chessian) order n :=
  regularEvent_probability_bound_of_component_tails
    P controller regular score hessian
    Ccontroller Cregular Cscore Chessian order n
    hcontroller hregular hscore hhessian

/-- Supplement equation `eq:SI_controller_finite_bound`, as an exact
membership characterization of the controller component event. -/
theorem eq_SI_controller_finite_bound
    {Omega : Type*} (controllerError controllerBound : Nat -> Omega -> Real)
    (n : Nat) (omega : Omega) :
    omega ∈ controllerFiniteBoundEvent controllerError controllerBound n ↔
      controllerError n omega <= controllerBound n omega :=
  Iff.rfl

/-- Supplement equation `eq:SI_score_high_probability`, as an exact
membership characterization of the score component event. -/
theorem eq_SI_score_high_probability
    {Omega : Type*} (scoreSize scoreBound : Nat -> Omega -> Real)
    (n : Nat) (omega : Omega) :
    omega ∈ scoreHighProbabilityEvent scoreSize scoreBound n ↔
      scoreSize n omega <= scoreBound n omega :=
  Iff.rfl

/-- Supplement equation `eq:SI_uniform_hessian_high_probability`, as the
uniform-curvature component event. -/
theorem eq_SI_uniform_hessian_high_probability
    {Omega : Type*} (curvature lowerBound : Nat -> Omega -> Real)
    (n : Nat) (omega : Omega) :
    omega ∈ uniformHessianEvent curvature lowerBound n ↔
      lowerBound n omega <= curvature n omega :=
  Iff.rfl

/-- Supplement equation `eq:SI_bad_event_moment`: a deterministic physical
error bound and a primitive bad-event probability estimate imply the exact
finite-sample moment bound. -/
theorem eq_SI_bad_event_moment_from_event_bound
    {Omega E : Type*} [SeminormedAddGroup E] (Exp : PositiveExpectation Omega)
    (bad : Set Omega) (W : Omega -> E) (moment : Nat)
    (constant scale tail : Real)
    (hW : ∀ omega, ‖W omega‖ <= constant * scale)
    (hbad : Exp.probability bad <= tail)
    (hpow : 0 <= (constant * scale) ^ moment) :
    Exp.expectation (restrictedMoment bad W moment) <=
      (constant * scale) ^ moment * tail := by
  exact le_trans
    (bad_event_moment_le_probability Exp bad W moment
      (constant * scale) hW)
    (mul_le_mul_of_nonneg_left hbad hpow)

end Label

end

end QubitOracle.Paper
