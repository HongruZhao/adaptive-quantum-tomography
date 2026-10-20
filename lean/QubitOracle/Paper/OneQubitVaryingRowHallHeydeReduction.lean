import QubitOracle.Paper.OneQubitHallHeydeCor31ExactQubitReduction

/-!
# Hall--Heyde reduction for varying exact-cycle qubit rows

This module retains the exact finite Born laws and the common product-space
construction while allowing row `n` to contain `3 * rowSize n` final
observations. It introduces no axiom. The final wrapper invokes only the
source-faithful Hall--Heyde Corollary 3.1 atom.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace QubitOracle.Paper
namespace MixedExactCycleScalarTriangularArrayData

noncomputable section

attribute [local instance] rowMeasurableSpace rowMeasurableSingletonClass
  historyKeyMeasurableSpace

abbrev varyingExactCycleRowLength (rowSize : ℕ → ℕ) (n : ℕ) : ℕ :=
  3 * rowSize n

abbrev varyingExactCycleFiltration
    (A : ℕ → MixedExactCycleScalarTriangularArrayData)
    (rowSize : ℕ → ℕ) (n : ℕ) :=
  augmentedRowFiltration A rowSize n

abbrev varyingExactCycleScoreIncrement
    (A : ℕ → MixedExactCycleScalarTriangularArrayData)
    (rowSize : ℕ → ℕ) (n : ℕ)
    (t : Fin (varyingExactCycleRowLength rowSize n)) :
    CommonOmega A rowSize → ℝ :=
  liftedScore A rowSize n t

abbrev varyingExactCycleConditionalVariance
    (A : ℕ → MixedExactCycleScalarTriangularArrayData)
    (rowSize : ℕ → ℕ) (n : ℕ)
    (t : Fin (varyingExactCycleRowLength rowSize n)) :
    CommonOmega A rowSize → ℝ :=
  liftedOneShotFisher A rowSize n t

abbrev varyingExactCycleStrictLindebergKernel
    (A : ℕ → MixedExactCycleScalarTriangularArrayData)
    (rowSize : ℕ → ℕ) (epsilon : ℝ) (n : ℕ)
    (t : Fin (varyingExactCycleRowLength rowSize n)) :
    CommonOmega A rowSize → ℝ :=
  liftRowVariable A rowSize n
    ((A n).strictOneShotLindebergKernel (rowSize n) t epsilon)

/-- Model-specific Fisher convergence on the exact common product space. -/
def VaryingCommonFisherConvergesInProbability
    (A : ℕ → MixedExactCycleScalarTriangularArrayData)
    (rowSize : ℕ → ℕ) (sigmaSq : ℝ) : Prop :=
  HallHeydeScalarConvergesInProbability (commonMeasure A rowSize)
    (fun n omega =>
      (A n).explicitNormalizedFisher (rowSize n) (omega n).1)
    sigmaSq

/-- The deterministic score envelope vanishes along the chosen row sizes. -/
def VaryingMaximumJumpEnvelopeTendsToZero
    (A : ℕ → MixedExactCycleScalarTriangularArrayData)
    (rowSize : ℕ → ℕ) : Prop :=
  Tendsto (fun n => (A n).maximumJumpEnvelope (rowSize n))
    atTop (nhds 0)

theorem varyingExactCycleScore_integrable
    (A : ℕ → MixedExactCycleScalarTriangularArrayData)
    (rowSize : ℕ → ℕ) (n : ℕ)
    (t : Fin (varyingExactCycleRowLength rowSize n)) :
    Integrable (varyingExactCycleScoreIncrement A rowSize n t)
      (commonMeasure A rowSize) := by
  exact liftRowVariable_integrable A rowSize n
    ((A n).currentCoordinateObservable (rowSize n) t
      ((A n).scoreObservable (rowSize n) t))
    ((A n).integrable_mathlibRowMeasure (rowSize n) _)

theorem varyingExactCycleScore_square_integrable
    (A : ℕ → MixedExactCycleScalarTriangularArrayData)
    (rowSize : ℕ → ℕ) (n : ℕ)
    (t : Fin (varyingExactCycleRowLength rowSize n)) :
    Integrable
      (fun omega => varyingExactCycleScoreIncrement A rowSize n t omega ^ 2)
      (commonMeasure A rowSize) := by
  have hLift := liftRowVariable_integrable A rowSize n
    (fun row : CommonRow A rowSize n =>
      (A n).currentCoordinateObservable (rowSize n) t
        ((A n).scoreObservable (rowSize n) t) row ^ 2)
    ((A n).integrable_mathlibRowMeasure (rowSize n) _)
  exact hLift.congr (Filter.Eventually.of_forall fun _omega => rfl)

theorem varyingExactCycleScoreSquare_condExp_eq_fisher
    (A : ℕ → MixedExactCycleScalarTriangularArrayData)
    (rowSize : ℕ → ℕ) (hrow : ∀ n, 0 < rowSize n)
    (n : ℕ) (t : Fin (varyingExactCycleRowLength rowSize n)) :
    (commonMeasure A rowSize)[
        (fun omega => varyingExactCycleScoreIncrement A rowSize n t omega ^ 2) |
        varyingExactCycleFiltration A rowSize n t.1] =ᵐ[
          commonMeasure A rowSize]
      varyingExactCycleConditionalVariance A rowSize n t := by
  have hCommon :=
    liftedSquaredScore_condExp_eq_oneShotFisher_closed A rowSize n (hrow n) t
  have hObservable :
      liftedSquaredScore A rowSize n t =
        (fun omega => liftedScore A rowSize n t omega ^ 2) := by
    funext _omega
    rfl
  rw [← hObservable]
  exact hCommon

theorem varyingExactCycleStrictLindeberg_condExp_eq_kernel
    (A : ℕ → MixedExactCycleScalarTriangularArrayData)
    (rowSize : ℕ → ℕ) (epsilon : ℝ)
    (n : ℕ) (t : Fin (varyingExactCycleRowLength rowSize n)) :
    (commonMeasure A rowSize)[
        (fun omega =>
          if epsilon < |varyingExactCycleScoreIncrement A rowSize n t omega| then
            varyingExactCycleScoreIncrement A rowSize n t omega ^ 2
          else 0) |
        varyingExactCycleFiltration A rowSize n t.1] =ᵐ[
          commonMeasure A rowSize]
      varyingExactCycleStrictLindebergKernel A rowSize epsilon n t := by
  have hCommon := commonCondExp_lift A rowSize n t.1
    ((A n).currentCoordinateObservable (rowSize n) t
      ((A n).strictLindebergObservable (rowSize n) t epsilon))
    ((A n).strictOneShotLindebergKernel (rowSize n) t epsilon)
    ((A n).strictLindeberg_literal_condExp_eq_kernel
      (rowSize n) t epsilon)
  have hObservable :
      liftRowVariable A rowSize n
          ((A n).currentCoordinateObservable (rowSize n) t
            ((A n).strictLindebergObservable (rowSize n) t epsilon)) =
        (fun omega =>
          if epsilon < |liftedScore A rowSize n t omega| then
            liftedScore A rowSize n t omega ^ 2
          else 0) := by
    funext _omega
    rfl
  rw [← hObservable]
  exact hCommon

theorem varyingExactCycleConditionalVariance_sum_eq_fisher
    (A : ℕ → MixedExactCycleScalarTriangularArrayData)
    (rowSize : ℕ → ℕ) (n : ℕ) (omega : CommonOmega A rowSize) :
    (∑ t : Fin (varyingExactCycleRowLength rowSize n),
      varyingExactCycleConditionalVariance A rowSize n t omega) =
        (A n).explicitNormalizedFisher (rowSize n) (omega n).1 := by
  simpa [varyingExactCycleConditionalVariance, liftedOneShotFisher,
    liftRowVariable, predictableQuadraticVariation] using
    (A n).predictableQuadraticVariation_eq_explicitNormalizedFisher
      (rowSize n) (omega n)

theorem varyingExactCycleStrictLindebergSum_eventually_zero
    (A : ℕ → MixedExactCycleScalarTriangularArrayData)
    (rowSize : ℕ → ℕ) (hrow : ∀ n, 0 < rowSize n)
    (hEnvelope : VaryingMaximumJumpEnvelopeTendsToZero A rowSize)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      ∀ omega : CommonOmega A rowSize,
        (∑ t : Fin (varyingExactCycleRowLength rowSize n),
          varyingExactCycleStrictLindebergKernel A rowSize epsilon n t omega) = 0 := by
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (A n).maximumJumpEnvelope (rowSize n) < epsilon :=
    (tendsto_order.1 hEnvelope).2 epsilon hepsilon
  filter_upwards [hsmall] with n henvelope
  intro omega
  apply Finset.sum_eq_zero
  intro t _ht
  simpa [varyingExactCycleStrictLindebergKernel, liftRowVariable] using
    (A n).strictOneShotLindebergKernel_eq_zero_of_envelope_lt
      (rowSize n) (hrow n) (omega n).1 t epsilon henvelope (omega n) rfl

theorem varyingExactCycleStrictLindeberg_converges
    (A : ℕ → MixedExactCycleScalarTriangularArrayData)
    (rowSize : ℕ → ℕ) (hrow : ∀ n, 0 < rowSize n)
    (hEnvelope : VaryingMaximumJumpEnvelopeTendsToZero A rowSize) :
    ∀ epsilon : ℝ, 0 < epsilon →
      HallHeydeScalarConvergesInProbability (commonMeasure A rowSize)
        (fun n omega =>
          ∑ t : Fin (varyingExactCycleRowLength rowSize n),
            varyingExactCycleStrictLindebergKernel A rowSize epsilon n t omega)
        0 := by
  intro epsilon hepsilon delta hdelta
  have hzero := varyingExactCycleStrictLindebergSum_eventually_zero
    A rowSize hrow hEnvelope epsilon hepsilon
  have hprobabilityZero :
      (fun n => commonMeasure A rowSize
        {omega |
          delta ≤
            |(∑ t : Fin (varyingExactCycleRowLength rowSize n),
                varyingExactCycleStrictLindebergKernel
                  A rowSize epsilon n t omega) - 0|}) =ᶠ[atTop]
        (fun _ : ℕ => (0 : ℝ≥0∞)) := by
    filter_upwards [hzero] with n hn
    have hset :
        {omega : CommonOmega A rowSize |
          delta ≤
            |∑ t : Fin (varyingExactCycleRowLength rowSize n),
                varyingExactCycleStrictLindebergKernel
                  A rowSize epsilon n t omega|} = ∅ := by
      ext omega
      simp [hn omega, not_le_of_gt hdelta]
    have hmeasure := congrArg (commonMeasure A rowSize) hset
    simpa only [sub_zero, measure_empty] using hmeasure
  exact tendsto_const_nhds.congr' hprobabilityZero.symm

theorem varyingExactCycleHallHeydePremises
    (A : ℕ → MixedExactCycleScalarTriangularArrayData)
    (rowSize : ℕ → ℕ) (hrow : ∀ n, 0 < rowSize n)
    (sigmaSq : ℝ) (hsigmaSq : 0 ≤ sigmaSq)
    (hFisher : VaryingCommonFisherConvergesInProbability A rowSize sigmaSq)
    (hEnvelope : VaryingMaximumJumpEnvelopeTendsToZero A rowSize) :
    HallHeyde1980Corollary31DeterministicVariancePremises
      (commonMeasure A rowSize) (varyingExactCycleRowLength rowSize)
      (varyingExactCycleFiltration A rowSize)
      (varyingExactCycleScoreIncrement A rowSize)
      (varyingExactCycleConditionalVariance A rowSize)
      (varyingExactCycleStrictLindebergKernel A rowSize) sigmaSq := by
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
        varyingExactCycleStrictLindeberg_converges
          A rowSize hrow hEnvelope }
  · intro n k hk hknext
    exact hallHeydeCondition321 A rowSize n k hk hknext
  · intro n t
    exact liftedScore_measurable_succ A rowSize n t
  · intro n t
    exact varyingExactCycleScore_integrable A rowSize n t
  · intro n t
    exact varyingExactCycleScore_square_integrable A rowSize n t
  · intro n t
    exact liftedScore_condExp_zero_closed A rowSize n t
  · intro n t
    exact varyingExactCycleScoreSquare_condExp_eq_fisher A rowSize hrow n t
  · intro epsilon _hepsilon n t
    exact varyingExactCycleStrictLindeberg_condExp_eq_kernel
      A rowSize epsilon n t
  · intro epsilon hepsilon
    have h := hFisher epsilon hepsilon
    simpa only [varyingExactCycleConditionalVariance_sum_eq_fisher]
      using h

def VaryingExactCycleScalarScoreCLT
    (A : ℕ → MixedExactCycleScalarTriangularArrayData)
    (rowSize : ℕ → ℕ) (sigmaSq : ℝ) : Prop :=
  TendstoInDistribution
    (hallHeydeDeterministicVarianceRowSum
      (varyingExactCycleRowLength rowSize)
      (varyingExactCycleScoreIncrement A rowSize))
    atTop id (fun _ => commonMeasure A rowSize)
    (gaussianReal 0 sigmaSq.toNNReal)

theorem varyingExactCycleScalarScoreCLT_of_statement
    (A : ℕ → MixedExactCycleScalarTriangularArrayData)
    (rowSize : ℕ → ℕ) (hrow : ∀ n, 0 < rowSize n)
    (hHallHeyde : HallHeyde1980Corollary31DeterministicVarianceStatement.{0})
    (sigmaSq : ℝ) (hsigmaSq : 0 ≤ sigmaSq)
    (hFisher : VaryingCommonFisherConvergesInProbability A rowSize sigmaSq)
    (hEnvelope : VaryingMaximumJumpEnvelopeTendsToZero A rowSize) :
    VaryingExactCycleScalarScoreCLT A rowSize sigmaSq := by
  exact hHallHeyde (commonMeasure A rowSize)
    (varyingExactCycleRowLength rowSize)
    (varyingExactCycleFiltration A rowSize)
    (varyingExactCycleScoreIncrement A rowSize)
    (varyingExactCycleConditionalVariance A rowSize)
    (varyingExactCycleStrictLindebergKernel A rowSize) sigmaSq
    (varyingExactCycleHallHeydePremises
      A rowSize hrow sigmaSq hsigmaSq hFisher hEnvelope)

/-- Varying-row score CLT with exactly one external scientific dependency:
Hall and Heyde (1980), Corollary 3.1. -/
theorem varyingExactCycleScalarScoreCLT_of_hallHeyde
    (A : ℕ → MixedExactCycleScalarTriangularArrayData)
    (rowSize : ℕ → ℕ) (hrow : ∀ n, 0 < rowSize n)
    (sigmaSq : ℝ) (hsigmaSq : 0 ≤ sigmaSq)
    (hFisher : VaryingCommonFisherConvergesInProbability A rowSize sigmaSq)
    (hEnvelope : VaryingMaximumJumpEnvelopeTendsToZero A rowSize) :
    VaryingExactCycleScalarScoreCLT A rowSize sigmaSq :=
  varyingExactCycleScalarScoreCLT_of_statement A rowSize hrow
    hallHeyde1980_corollary3_1_deterministicVariance_external
    sigmaSq hsigmaSq hFisher hEnvelope

end
end MixedExactCycleScalarTriangularArrayData
end QubitOracle.Paper
