import QubitOracle.Paper.ProtocolInformationComposition
import QubitOracle.Paper.ConcreteProtocolA1A3
import QubitOracle.Paper.RemainingElementaryLabels
import QubitOracle.Paper.ConcentrationLabelInterfaces
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Controller and information-convergence labels

This module closes the deterministic assembly around the manuscript's
controller-rate, empirical-information, uniform-Gram, and Hessian-variance
labels.  Protocol-specific concentration inputs are exposed as summable bad
events, component limits, or one-step variance bounds.  No final labeled
conclusion is assumed and no scientific axiom is introduced.
-/

noncomputable section

namespace QubitOracle.Paper

open Filter MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

/-! ## Controller rate from summable failure events -/

/-- The deterministic scale in the controller-rate equations. -/
def controllerRateScale (expectedExploration : Nat -> Real) (n : Nat) : Real :=
  Real.sqrt (Real.log (n : Real) / expectedExploration n)

/-- Typed meaning of `O_as(sqrt(log n / E_n))`. -/
def AlmostSureControllerRate
    {Omega E : Type*} [MeasurableSpace Omega] [NormedAddCommGroup E]
    (mu : Measure Omega) (controller : Nat -> Omega -> E) (truth : E)
    (expectedExploration : Nat -> Real) : Prop :=
  ∀ᵐ omega ∂mu, exists C : Real, 0 <= C ∧
    ∀ᶠ n in atTop,
      ‖controller n omega - truth‖ <= C * controllerRateScale expectedExploration n

/-- Primitive concentration certificate.  Its pointwise estimate is required
only off a bad event, and summability is strictly weaker than the final
almost-sure rate. -/
structure ControllerRatePrimitives
    {Omega E : Type*} [MeasurableSpace Omega] [NormedAddCommGroup E]
    (mu : Measure Omega) (controller : Nat -> Omega -> E) (truth : E)
    (expectedExploration : Nat -> Real) where
  badEvent : Nat -> Set Omega
  badEvent_tsum_ne_top : (∑' n, mu (badEvent n)) ≠ ⊤
  constant : Real
  constant_nonnegative : 0 <= constant
  bound_on_good : forall n omega, omega ∉ badEvent n ->
    ‖controller n omega - truth‖ <=
      constant * controllerRateScale expectedExploration n
  rate_tendsto_zero :
    Tendsto (controllerRateScale expectedExploration) atTop (nhds 0)

/-- First Borel--Cantelli converts the summable finite-time failures into the
manuscript's almost-sure controller rate. -/
theorem ControllerRatePrimitives.almostSureRate
    {Omega E : Type*} [MeasurableSpace Omega] [NormedAddCommGroup E]
    {mu : Measure Omega} {controller : Nat -> Omega -> E} {truth : E}
    {expectedExploration : Nat -> Real}
    (h : ControllerRatePrimitives mu controller truth expectedExploration) :
    AlmostSureControllerRate mu controller truth expectedExploration := by
  have havoid : ∀ᵐ omega ∂mu, ∀ᶠ n in atTop, omega ∉ h.badEvent n :=
    MeasureTheory.ae_eventually_notMem h.badEvent_tsum_ne_top
  filter_upwards [havoid] with omega hgood
  refine ⟨h.constant, h.constant_nonnegative, ?_⟩
  filter_upwards [hgood] with n hn
  exact h.bound_on_good n omega hn

/-- The same primitive certificate gives strong controller consistency once
the exploration scale vanishes. -/
theorem ControllerRatePrimitives.consistent_ae
    {Omega E : Type*} [MeasurableSpace Omega] [NormedAddCommGroup E]
    {mu : Measure Omega} {controller : Nat -> Omega -> E} {truth : E}
    {expectedExploration : Nat -> Real}
    (h : ControllerRatePrimitives mu controller truth expectedExploration) :
    ∀ᵐ omega ∂mu,
      Tendsto (fun n => controller n omega) atTop (nhds truth) := by
  filter_upwards [h.almostSureRate] with omega hrate
  obtain ⟨C, hC, hbound⟩ := hrate
  apply (tendsto_iff_norm_sub_tendsto_zero).2
  have hupper : Tendsto
      (fun n => C * controllerRateScale expectedExploration n)
      atTop (nhds 0) := by
    simpa using h.rate_tendsto_zero.const_mul C
  exact squeeze_zero'
    (Eventually.of_forall fun n => norm_nonneg (controller n omega - truth))
    hbound hupper

/-- Root-fourth scaled controller distance. -/
def scaledControllerNormError
    {Omega E : Type*} [NormedAddCommGroup E]
    (controller : Nat -> Omega -> E) (truth : E) (n : Nat) (omega : Omega) : Real :=
  natQuarterPower n * ‖controller n omega - truth‖

/-- The terminal exploration condition upgrades the controller certificate to
the `o_P(n^(-1/4))` scale, first in its stronger almost-sure form. -/
theorem ControllerRatePrimitives.nquarter_tendsto_ae
    {Omega E : Type*} [MeasurableSpace Omega] [NormedAddCommGroup E]
    {mu : Measure Omega} {controller : Nat -> Omega -> E} {truth : E}
    {expectedExploration : Nat -> Real}
    (h : ControllerRatePrimitives mu controller truth expectedExploration)
    (hterminal : TerminalExplorationRate expectedExploration) :
    ∀ᵐ omega ∂mu,
      Tendsto (fun n => scaledControllerNormError controller truth n omega)
        atTop (nhds 0) := by
  filter_upwards [h.almostSureRate] with omega hrate
  obtain ⟨C, hC, hbound⟩ := hrate
  have hscale : Tendsto
      (fun n => natQuarterPower n * controllerRateScale expectedExploration n)
      atTop (nhds 0) := by
    simpa [controllerRateScale] using
      nquarter_rate_tendsto_zero expectedExploration hterminal
  have hupper : Tendsto
      (fun n => C *
        (natQuarterPower n * controllerRateScale expectedExploration n))
      atTop (nhds 0) := by
    simpa using hscale.const_mul C
  apply squeeze_zero'
  · exact Eventually.of_forall fun n =>
      mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  · filter_upwards [hbound] with n hn
    calc
      scaledControllerNormError controller truth n omega <=
          natQuarterPower n *
            (C * controllerRateScale expectedExploration n) :=
        mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg _)
      _ = C *
          (natQuarterPower n * controllerRateScale expectedExploration n) := by
        ring
  · exact hupper

/-- Measurability converts the almost-sure root-fourth result to convergence
in probability, the exact stochastic meaning used in the controller theorem. -/
theorem ControllerRatePrimitives.nquarter_tendstoInMeasure
    {Omega E : Type*} [MeasurableSpace Omega] [NormedAddCommGroup E]
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {controller : Nat -> Omega -> E} {truth : E}
    {expectedExploration : Nat -> Real}
    (h : ControllerRatePrimitives mu controller truth expectedExploration)
    (hterminal : TerminalExplorationRate expectedExploration)
    (hmeasurable : forall n, AEStronglyMeasurable
      (scaledControllerNormError controller truth n) mu) :
    TendstoInMeasure mu
      (scaledControllerNormError controller truth) atTop (fun _ => 0) :=
  tendstoInMeasure_of_tendsto_ae hmeasurable
    (h.nquarter_tendsto_ae hterminal)

/-! ## Information composition -/

/-- Primitive exploitation, exploration, and innovation limits.  The final
realized-information limit is deliberately not a field. -/
structure ProtocolInformationComponents
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [NormedSpace Real E]
    (mu : Measure Omega) (target : E) where
  epsilon : Nat -> Real
  realized : Omega -> Nat -> E
  predictable : Omega -> Nat -> E
  exploitation : Omega -> Nat -> E
  exploration : Omega -> Nat -> E
  round_decomposition : forall omega i,
    predictable omega i =
      predictableMixtureInformation epsilon
        (exploitation omega) (exploration omega) i
  exploitation_limit : ∀ᵐ omega ∂mu,
    Tendsto
      (fun N => normalizedProtocolInformation
        (exploitationInformation epsilon (exploitation omega)) N)
      atTop (nhds target)
  exploration_limit : ∀ᵐ omega ∂mu,
    Tendsto
      (fun N => normalizedProtocolInformation
        (explorationInformation epsilon (exploration omega)) N)
      atTop (nhds 0)
  innovation_limit : ∀ᵐ omega ∂mu,
    Tendsto
      (fun N => normalizedProtocolInformation
        (informationInnovation (realized omega) (predictable omega)) N)
      atTop (nhds 0)

/-- Deterministic information decomposition, lifted almost surely. -/
theorem ProtocolInformationComponents.realized_tendsto_ae
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [NormedSpace Real E]
    {mu : Measure Omega} {target : E}
    (h : ProtocolInformationComponents mu target) :
    ∀ᵐ omega ∂mu,
      Tendsto
        (fun N => normalizedProtocolInformation (h.realized omega) N)
        atTop (nhds target) :=
  ae_normalizedProtocolInformation_tendsto_of_components
    mu h.realized h.predictable h.epsilon h.exploitation h.exploration target
    h.round_decomposition h.exploitation_limit h.exploration_limit
    h.innovation_limit

/-- Full-sequence information convergence implies convergence along any
completed-batch sequence tending to infinity. -/
theorem ProtocolInformationComponents.completedBatch_tendsto_ae
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [NormedSpace Real E]
    {mu : Measure Omega} {target : E}
    (h : ProtocolInformationComponents mu target)
    (completed : Nat -> Nat) (hcompleted : Tendsto completed atTop atTop) :
    ∀ᵐ omega ∂mu,
      Tendsto
        (fun K => normalizedProtocolInformation
          (h.realized omega) (completed K))
        atTop (nhds target) := by
  filter_upwards [h.realized_tendsto_ae] with omega hfull
  exact hfull.comp hcompleted

/-! ## Uniform Gram lower bounds -/

/-- Loewner lower bound expressed without relying on a matrix-order instance. -/
def MatrixQuadraticDominates
    {D : Type*} [Fintype D]
    (A : Matrix D D Real) (scale : Real) : Prop :=
  forall x : D -> Real,
    scale * dotProduct x x <= realMatrixQuadratic A x

/-- Quadratic-form nonnegativity. -/
def MatrixQuadraticNonnegative
    {D : Type*} [Fintype D] (A : Matrix D D Real) : Prop :=
  forall x : D -> Real, 0 <= realMatrixQuadratic A x

/-- Primitive window certificate behind the paper's uniform Gram event.
The exploration lower bound and nonnegative remainder are separate inputs;
the lower bound for the full Gram matrix is not a field. -/
structure UniformGramWindowPrimitives
    (Omega D : Type*) [Fintype D] where
  gram : Nat -> Omega -> Matrix D D Real
  explorationPart : Nat -> Omega -> Matrix D D Real
  remainderPart : Nat -> Omega -> Matrix D D Real
  start : Nat -> Nat
  expectedExploration : Nat -> Real
  c2 : Real
  c2_nonnegative : 0 <= c2
  badEvent : Nat -> Set Omega
  quadratic_decomposition : forall n omega, omega ∉ badEvent n ->
    forall j, start n <= j -> j <= n -> forall x,
      realMatrixQuadratic (gram j omega) x =
        realMatrixQuadratic (explorationPart j omega) x +
          realMatrixQuadratic (remainderPart j omega) x
  exploration_lower : forall n omega, omega ∉ badEvent n ->
    forall j, start n <= j -> j <= n ->
      MatrixQuadraticDominates (explorationPart j omega)
        (c2 * expectedExploration j)
  remainder_nonnegative : forall n omega, omega ∉ badEvent n ->
    forall j, start n <= j -> j <= n ->
      MatrixQuadraticNonnegative (remainderPart j omega)

/-- Finite deterministic assembly of the uniform Gram bound on one good
window. -/
theorem UniformGramWindowPrimitives.dominates_on_good
    {Omega D : Type*} [Fintype D]
    (h : UniformGramWindowPrimitives Omega D)
    (n : Nat) (omega : Omega) (hgood : omega ∉ h.badEvent n) :
    forall j, h.start n <= j -> j <= n ->
      MatrixQuadraticDominates (h.gram j omega)
        (h.c2 * h.expectedExploration j) := by
  intro j hj0 hj1 x
  have hdecomp := h.quadratic_decomposition n omega hgood j hj0 hj1 x
  have hexplore := h.exploration_lower n omega hgood j hj0 hj1 x
  have hremain := h.remainder_nonnegative n omega hgood j hj0 hj1 x
  rw [hdecomp]
  linarith

/-! ## Hessian variance parameter -/

/-- A uniform one-step conditional-square bound controls the complete
predictable quadratic variation by the triangle inequality. -/
theorem predictableQuadraticVariation_norm_le_of_increment_bound
    {Omega : Type*} [MeasurableSpace Omega] {d : Nat} {mu : Measure Omega}
    (data : SourceFaithfulMatrixFreedman.MatrixMartingaleData Omega d mu)
    (C_H : Real) (n : Nat) (omega : Omega)
    (hbound : forall k, k < n ->
      ‖SourceFaithfulMatrixFreedman.conditionalIncrementSquare data k omega‖ <= C_H) :
    ‖SourceFaithfulMatrixFreedman.predictableQuadraticVariation data n omega‖ <=
      C_H * (n : Real) := by
  unfold SourceFaithfulMatrixFreedman.predictableQuadraticVariation
  calc
    ‖∑ k ∈ Finset.range n,
        SourceFaithfulMatrixFreedman.conditionalIncrementSquare data k omega‖ <=
        ∑ k ∈ Finset.range n,
          ‖SourceFaithfulMatrixFreedman.conditionalIncrementSquare data k omega‖ :=
      norm_sum_le _ _
    _ <= ∑ _k ∈ Finset.range n, C_H := by
      apply Finset.sum_le_sum
      intro k hk
      exact hbound k (Finset.mem_range.mp hk)
    _ = C_H * (n : Real) := by simp [mul_comm]

namespace Label

/-! ## Canonical manuscript labels -/

/-- Main equation `eq:controller_rate_main`. -/
theorem eq_controller_rate_main
    {Omega E : Type*} [MeasurableSpace Omega] [NormedAddCommGroup E]
    (mu : Measure Omega) (controller : Nat -> Omega -> E) (truth : E)
    (expectedExploration : Nat -> Real)
    (h : ControllerRatePrimitives mu controller truth expectedExploration) :
    AlmostSureControllerRate mu controller truth expectedExploration :=
  h.almostSureRate

/-- Supplement equation `eq:SI_RLS_rate`. -/
theorem eq_SI_RLS_rate
    {Omega E : Type*} [MeasurableSpace Omega] [NormedAddCommGroup E]
    (mu : Measure Omega) (controller : Nat -> Omega -> E) (truth : E)
    (expectedExploration : Nat -> Real)
    (h : ControllerRatePrimitives mu controller truth expectedExploration) :
    AlmostSureControllerRate mu controller truth expectedExploration :=
  h.almostSureRate

/-- Supplement theorem `thm:SI_RLS`: almost-sure rate, strong consistency,
and the terminal root-fourth convergence in probability. -/
theorem thm_SI_RLS
    {Omega E : Type*} [MeasurableSpace Omega] [NormedAddCommGroup E]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (controller : Nat -> Omega -> E) (truth : E)
    (expectedExploration : Nat -> Real)
    (h : ControllerRatePrimitives mu controller truth expectedExploration)
    (hterminal : TerminalExplorationRate expectedExploration)
    (hmeasurable : forall n, AEStronglyMeasurable
      (scaledControllerNormError controller truth n) mu) :
    AlmostSureControllerRate mu controller truth expectedExploration ∧
      (∀ᵐ omega ∂mu,
        Tendsto (fun n => controller n omega) atTop (nhds truth)) ∧
      TendstoInMeasure mu
        (scaledControllerNormError controller truth) atTop (fun _ => 0) := by
  exact ⟨h.almostSureRate, h.consistent_ae,
    h.nquarter_tendstoInMeasure hterminal hmeasurable⟩

/-- Main mixed branch `eq:mixed_info_convergence`. -/
theorem eq_mixed_info_convergence
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (controller : Nat -> Omega -> (Fin 3 -> Real))
    (thetaStar : Fin 3 -> Real) (expectedExploration : Nat -> Real)
    (hcontroller : ControllerRatePrimitives
      mu controller thetaStar expectedExploration)
    (mixedTarget : OracleMatrix)
    (hinfo : ProtocolInformationComponents mu mixedTarget)
    (completed : Nat -> Nat) (hcompleted : Tendsto completed atTop atTop) :
    (∀ᵐ omega ∂mu,
      Tendsto (fun n => controller n omega) atTop (nhds thetaStar)) ∧
    (∀ᵐ omega ∂mu,
      Tendsto
        (fun K => normalizedProtocolInformation
          (hinfo.realized omega) (completed K))
        atTop (nhds mixedTarget)) :=
  ⟨hcontroller.consistent_ae,
    hinfo.completedBatch_tendsto_ae completed hcompleted⟩

/-- Main rank-one branch `eq:r1_info_convergence`. -/
theorem eq_r1_info_convergence
    {n : Nat} {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (controller : Nat -> Omega ->
      Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (truthProjector : Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (expectedExploration : Nat -> Real)
    (hcontroller : ControllerRatePrimitives
      mu controller truthProjector expectedExploration)
    (hinfo : ProtocolInformationComponents mu
      ((1 / 2 : Real) •
        (1 : Matrix (TangentIndex n) (TangentIndex n) Real)))
    (completed : Nat -> Nat) (hcompleted : Tendsto completed atTop atTop) :
    (∀ᵐ omega ∂mu,
      Tendsto (fun k => controller k omega) atTop (nhds truthProjector)) ∧
    (∀ᵐ omega ∂mu,
      Tendsto
        (fun K => normalizedProtocolInformation
          (hinfo.realized omega) (completed K))
        atTop (nhds ((1 / 2 : Real) •
          (1 : Matrix (TangentIndex n) (TangentIndex n) Real)))) :=
  ⟨hcontroller.consistent_ae,
    hinfo.completedBatch_tendsto_ae completed hcompleted⟩

/-- Main theorem `thm:information_convergence`, assembling its two branches
without requiring convergence of the empirical design distribution. -/
theorem thm_information_convergence
    {n : Nat} {OmegaMix OmegaR1 : Type*}
    [MeasurableSpace OmegaMix] [MeasurableSpace OmegaR1]
    (muMix : Measure OmegaMix) (muR1 : Measure OmegaR1)
    (mixedController : Nat -> OmegaMix -> (Fin 3 -> Real))
    (thetaStar : Fin 3 -> Real) (mixedExploration : Nat -> Real)
    (hmixedController : ControllerRatePrimitives
      muMix mixedController thetaStar mixedExploration)
    (mixedTarget : OracleMatrix)
    (hmixedInfo : ProtocolInformationComponents muMix mixedTarget)
    (rankOneController : Nat -> OmegaR1 ->
      Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (truthProjector : Matrix (Fin (n + 1)) (Fin (n + 1)) Complex)
    (rankOneExploration : Nat -> Real)
    (hrankOneController : ControllerRatePrimitives
      muR1 rankOneController truthProjector rankOneExploration)
    (hrankOneInfo : ProtocolInformationComponents muR1
      ((1 / 2 : Real) •
        (1 : Matrix (TangentIndex n) (TangentIndex n) Real)))
    (completed : Nat -> Nat) (hcompleted : Tendsto completed atTop atTop) :
    ((∀ᵐ omega ∂muMix,
        Tendsto (fun k => mixedController k omega) atTop (nhds thetaStar)) ∧
      (∀ᵐ omega ∂muMix,
        Tendsto
          (fun K => normalizedProtocolInformation
            (hmixedInfo.realized omega) (completed K))
          atTop (nhds mixedTarget))) ∧
    ((∀ᵐ omega ∂muR1,
        Tendsto (fun k => rankOneController k omega)
          atTop (nhds truthProjector)) ∧
      (∀ᵐ omega ∂muR1,
        Tendsto
          (fun K => normalizedProtocolInformation
            (hrankOneInfo.realized omega) (completed K))
          atTop (nhds ((1 / 2 : Real) •
            (1 : Matrix (TangentIndex n) (TangentIndex n) Real))))) := by
  constructor
  · exact eq_mixed_info_convergence muMix mixedController thetaStar
      mixedExploration hmixedController mixedTarget hmixedInfo completed hcompleted
  · exact eq_r1_info_convergence muR1 rankOneController truthProjector
      rankOneExploration hrankOneController hrankOneInfo completed hcompleted

/-- Supplement theorem `thm:SI_information`. -/
theorem thm_SI_information
    {n : Nat} {OmegaMix OmegaR1 : Type*}
    [MeasurableSpace OmegaMix] [MeasurableSpace OmegaR1]
    (muMix : Measure OmegaMix) (muR1 : Measure OmegaR1)
    (mixedTarget : OracleMatrix)
    (hmixed : ProtocolInformationComponents muMix mixedTarget)
    (hrankOne : ProtocolInformationComponents muR1
      ((1 / 2 : Real) •
        (1 : Matrix (TangentIndex n) (TangentIndex n) Real))) :
    (∀ᵐ omega ∂muMix,
      Tendsto
        (fun N => normalizedProtocolInformation (hmixed.realized omega) N)
        atTop (nhds mixedTarget)) ∧
    (∀ᵐ omega ∂muR1,
      Tendsto
        (fun N => normalizedProtocolInformation (hrankOne.realized omega) N)
        atTop (nhds ((1 / 2 : Real) •
          (1 : Matrix (TangentIndex n) (TangentIndex n) Real)))) :=
  ⟨hmixed.realized_tendsto_ae, hrankOne.realized_tendsto_ae⟩

/-- Supplement equation `eq:SI_protocol_information_verified`: componentwise
protocol limits imply conditional information convergence in probability. -/
theorem eq_SI_protocol_information_verified
    {D : Type*} [Fintype D]
    {problem : MartingaleCLTProblem D} {M : Matrix D D Real}
    (h : ScalarInformationCompositionPrimitives problem M) :
    problem.ConditionalCovarianceConverges M :=
  h.toConditionalCovariance

/-- Supplement equation `eq:SI_protocol_LAN_information`: the two protocol
component certificates identify the mixed and rank-one LAN information. -/
theorem eq_SI_protocol_LAN_information
    {n : Nat}
    {mixedProblem : MartingaleCLTProblem (Fin 3)}
    {rankOneProblem : MartingaleCLTProblem (TangentIndex n)}
    (mixedTarget : OracleMatrix)
    (hmixed : ScalarInformationCompositionPrimitives mixedProblem mixedTarget)
    (hrankOne : ScalarInformationCompositionPrimitives rankOneProblem
      ((1 / 2 : Real) •
        (1 : Matrix (TangentIndex n) (TangentIndex n) Real))) :
    mixedProblem.ConditionalCovarianceConverges mixedTarget ∧
      rankOneProblem.ConditionalCovarianceConverges
        ((1 / 2 : Real) •
          (1 : Matrix (TangentIndex n) (TangentIndex n) Real)) :=
  ⟨hmixed.toConditionalCovariance, hrankOne.toConditionalCovariance⟩

/-- Supplement equation `eq:SI_uniform_gram`. -/
theorem eq_SI_uniform_gram
    {Omega D : Type*} [Fintype D]
    (h : UniformGramWindowPrimitives Omega D)
    (n : Nat) (omega : Omega) (hgood : omega ∉ h.badEvent n) :
    forall j, h.start n <= j -> j <= n ->
      MatrixQuadraticDominates (h.gram j omega)
        (h.c2 * h.expectedExploration j) :=
  h.dominates_on_good n omega hgood

/-- Supplement equation `eq:SI_Gram_as`.  Summability of the window failures
is converted to an eventual almost-sure Gram lower bound. -/
theorem eq_SI_Gram_as
    {Omega D : Type*} [MeasurableSpace Omega] [Fintype D]
    (mu : Measure Omega) (h : UniformGramWindowPrimitives Omega D)
    (hbad : (∑' n, mu (h.badEvent n)) ≠ ⊤)
    (hstart : ∀ᶠ n in atTop, h.start n <= n) :
    ∀ᵐ omega ∂mu, ∀ᶠ n in atTop,
      MatrixQuadraticDominates (h.gram n omega)
        (h.c2 * h.expectedExploration n) := by
  have havoid : ∀ᵐ omega ∂mu,
      ∀ᶠ n in atTop, omega ∉ h.badEvent n :=
    MeasureTheory.ae_eventually_notMem hbad
  filter_upwards [havoid] with omega hgood
  filter_upwards [hgood, hstart] with n hn hsn
  exact h.dominates_on_good n omega hn n hsn le_rfl

/-- Supplement equation `eq:SI_Hessian_variance_parameter`. -/
theorem eq_SI_Hessian_variance_parameter
    {Omega : Type*} [MeasurableSpace Omega] {d : Nat} {mu : Measure Omega}
    (data : SourceFaithfulMatrixFreedman.MatrixMartingaleData Omega d mu)
    (C_H : Real) (n : Nat) (omega : Omega)
    (hbound : forall k, k < n ->
      ‖SourceFaithfulMatrixFreedman.conditionalIncrementSquare data k omega‖ <= C_H) :
    ‖SourceFaithfulMatrixFreedman.predictableQuadraticVariation data n omega‖ <=
      C_H * (n : Real) :=
  predictableQuadraticVariation_norm_le_of_increment_bound
    data C_H n omega hbound

end Label

end QubitOracle.Paper
