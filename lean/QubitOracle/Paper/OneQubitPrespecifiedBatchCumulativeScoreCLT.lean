import QubitOracle.Paper.OneQubitPrespecifiedBatchSafeguardedEstimator
import QubitOracle.Paper.OneQubitMixedExactCycleTaylorRemainder
import QubitOracle.Paper.SourceFaithfulHallHeydeCor31DeterministicVariance
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Sigma.Order

/-!
# Cumulative final-score Hall--Heyde reduction for prespecified batches

At horizon `K`, the final-shot index is the dependent finite sum of all final
shots in batches `k < K`.  A lexicographic key orders this type, and
`Fintype.orderIsoFinOfCardEq` enumerates it by a single `Fin` row.  Every
increment uses the frame selected by the pilot in its own observed batch.

The deterministic part is closed here: exact enumeration, exact terminal-sum
identity, a uniform `mixedProjectedScoreEnvelope / sqrt N_K` jump bound, and
eventual vanishing of every Lindeberg truncand.  The remaining certificate is
deliberately narrow and contains the genuinely unproved nested-filtration
conditional-expectation identities.  Conditional on that certificate and the
concrete cumulative Fisher convergence proposition, the only external theorem
used is Hall--Heyde (1980), Corollary 3.1.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open PureMultilevelSequentialBatchAdaptive

noncomputable section

attribute [local instance]
  pauliPilotBornPathMeasurableSpace
  mixedTwoStageFiniteRowMeasurableSpace
  mixedTwoStageFiniteRowMeasurableSingletonClass

/-- All final shots completed before horizon `K`, retaining their batch. -/
abbrev PrespecifiedBatchCumulativeFinalShotIndex (K : Nat) : Type :=
  Lex (Sigma fun k : Fin K => Fin (3 * exactConcreteBatchFinalBlocks k))

/-- Number of final observations in the first `K` batches. -/
def prespecifiedBatchCumulativeFinalRowLength (K : Nat) : Nat :=
  Fintype.card (PrespecifiedBatchCumulativeFinalShotIndex K)

/-- A batch-major enumeration retains the `toEquiv` interface used by the
finite summation lemmas, without hiding the cumulative-offset formula behind
a sorting implementation. -/
structure PrespecifiedBatchCumulativeFinalShotEnumeration (K : Nat) where
  toEquiv : Fin (prespecifiedBatchCumulativeFinalRowLength K) ≃
    PrespecifiedBatchCumulativeFinalShotIndex K

instance (K : Nat) : CoeFun
    (PrespecifiedBatchCumulativeFinalShotEnumeration K)
    (fun _ => Fin (prespecifiedBatchCumulativeFinalRowLength K) →
      PrespecifiedBatchCumulativeFinalShotIndex K) :=
  ⟨fun enumeration => enumeration.toEquiv⟩

/-- Explicit increasing enumeration by cumulative batch offset. -/
noncomputable def prespecifiedBatchCumulativeFinalShotOrderIso (K : Nat) :
    PrespecifiedBatchCumulativeFinalShotEnumeration K where
  toEquiv := by
    let hcard : prespecifiedBatchCumulativeFinalRowLength K =
        ∑ k : Fin K, 3 * exactConcreteBatchFinalBlocks k := by
      simp [prespecifiedBatchCumulativeFinalRowLength]
    exact (finCongr hcard).trans (finSigmaFinEquiv.symm.trans toLex)

/-- The row cardinality is the sum of the exact batch final sizes. -/
theorem prespecifiedBatchCumulativeFinalRowLength_eq_sum (K : Nat) :
    prespecifiedBatchCumulativeFinalRowLength K =
      ∑ k : Fin K, 3 * exactConcreteBatchFinalBlocks k := by
  simp [prespecifiedBatchCumulativeFinalRowLength]

/-- Root scaling from one exact-cycle row to the cumulative total-observation
scale. -/
def prespecifiedBatchCumulativeShotScale (K : Nat) (k : Fin K) : Real :=
  Real.sqrt (3 * exactConcreteBatchFinalBlocks k : Nat) /
    prespecifiedBatchSampleScale K

/-- One cumulative final-score increment.  It is the row-normalized score
multiplied by `sqrt(3 r_k) / sqrt(N_K)`, hence the raw score divided by
`sqrt(N_K)`. -/
def prespecifiedBatchCumulativeShotIncrement
    (K : Nat) (theta h b : RLSVector 3)
    (shot : PrespecifiedBatchCumulativeFinalShotIndex K)
    (omega : ExactConcretePredeterminedBatchPath) : Real :=
  prespecifiedBatchCumulativeShotScale K shot.1 *
    mixedExactCycleNormalizedDirectionalScore theta h
      (exactConcreteBatchSelectedFrame shot.1 b)
      (omega shot.1).1 shot.2 (omega shot.1).2

/-- The same increments in the single `Fin` enumeration required by the
Hall--Heyde triangular-array interface. -/
def prespecifiedBatchCumulativeEnumeratedIncrement
    (theta h b : RLSVector 3)
    (K : Nat) (t : Fin (prespecifiedBatchCumulativeFinalRowLength K))
    (omega : ExactConcretePredeterminedBatchPath) : Real :=
  prespecifiedBatchCumulativeShotIncrement K theta h b
    (prespecifiedBatchCumulativeFinalShotOrderIso K t) omega

/-- Enumeration preserves the exact sum over the dependent shot index. -/
theorem prespecifiedBatchCumulativeRowSum_eq_sigma
    (K : Nat) (theta h b : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPath) :
    hallHeydeDeterministicVarianceRowSum
        prespecifiedBatchCumulativeFinalRowLength
        (prespecifiedBatchCumulativeEnumeratedIncrement theta h b) K omega =
      ∑ shot : PrespecifiedBatchCumulativeFinalShotIndex K,
        prespecifiedBatchCumulativeShotIncrement K theta h b shot omega := by
  unfold hallHeydeDeterministicVarianceRowSum
    prespecifiedBatchCumulativeEnumeratedIncrement
  exact Fintype.sum_equiv
    (prespecifiedBatchCumulativeFinalShotOrderIso K).toEquiv
    (fun t => prespecifiedBatchCumulativeShotIncrement K theta h b
      (prespecifiedBatchCumulativeFinalShotOrderIso K t) omega)
    (fun shot => prespecifiedBatchCumulativeShotIncrement K theta h b shot omega)
    (fun _ => rfl)

/-- Exact batch-by-batch terminal-score identity after flattening. -/
theorem prespecifiedBatchCumulativeRowSum_eq_batchSums
    (K : Nat) (theta h b : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPath) :
    hallHeydeDeterministicVarianceRowSum
        prespecifiedBatchCumulativeFinalRowLength
        (prespecifiedBatchCumulativeEnumeratedIncrement theta h b) K omega =
      ∑ k : Fin K,
        prespecifiedBatchCumulativeShotScale K k *
          ∑ t : Fin (3 * exactConcreteBatchFinalBlocks k),
            mixedExactCycleNormalizedDirectionalScore theta h
              (exactConcreteBatchSelectedFrame k b)
              (omega k).1 t (omega k).2 := by
  rw [prespecifiedBatchCumulativeRowSum_eq_sigma]
  rw [show
      (∑ shot : PrespecifiedBatchCumulativeFinalShotIndex K,
        prespecifiedBatchCumulativeShotIncrement K theta h b shot omega) =
      ∑ shot : Sigma fun k : Fin K =>
          Fin (3 * exactConcreteBatchFinalBlocks k),
        prespecifiedBatchCumulativeShotIncrement K theta h b
          (toLex shot) omega by
    exact Fintype.sum_equiv ofLex
      (fun shot : PrespecifiedBatchCumulativeFinalShotIndex K =>
        prespecifiedBatchCumulativeShotIncrement K theta h b shot omega)
      (fun shot : Sigma fun k : Fin K =>
          Fin (3 * exactConcreteBatchFinalBlocks k) =>
        prespecifiedBatchCumulativeShotIncrement K theta h b
          (toLex shot) omega)
      (fun _ => rfl)]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [Finset.mul_sum]
  rfl

/-! ## Uniform jump and bounded-jump Lindeberg reduction -/

/-- Deterministic cumulative jump envelope. -/
def prespecifiedBatchCumulativeJumpEnvelope
    (K : Nat) (theta h : RLSVector 3) : Real :=
  mixedProjectedScoreEnvelope theta h / prespecifiedBatchSampleScale K

theorem prespecifiedBatchCumulativeShotIncrement_abs_le
    (K : Nat) (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (shot : PrespecifiedBatchCumulativeFinalShotIndex K)
    (omega : ExactConcretePredeterminedBatchPath) :
    |prespecifiedBatchCumulativeShotIncrement K theta h b shot omega| <=
      prespecifiedBatchCumulativeJumpEnvelope K theta h := by
  let r := exactConcreteBatchFinalBlocks shot.1
  have hr : 0 < r := exactConcreteBatchFinalBlocks_pos shot.1
  have hsqrt : 0 < Real.sqrt (3 * r : Nat) := by
    apply Real.sqrt_pos.2
    exact_mod_cast Nat.mul_pos (by norm_num : 0 < 3) hr
  have hscale : 0 <= prespecifiedBatchCumulativeShotScale K shot.1 := by
    unfold prespecifiedBatchCumulativeShotScale
    exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hnormalized :=
    mixedExactCycleNormalizedDirectionalScore_abs_le_envelope
      theta h (exactConcreteBatchSelectedFrame shot.1 b)
      (omega shot.1).1 (omega shot.1).2 shot.2 hInterior hr
  rw [prespecifiedBatchCumulativeShotIncrement, abs_mul,
    abs_of_nonneg hscale]
  calc
    prespecifiedBatchCumulativeShotScale K shot.1 *
        |mixedExactCycleNormalizedDirectionalScore theta h
          (exactConcreteBatchSelectedFrame shot.1 b)
          (omega shot.1).1 shot.2 (omega shot.1).2| <=
      prespecifiedBatchCumulativeShotScale K shot.1 *
        (mixedProjectedScoreEnvelope theta h / Real.sqrt (3 * r : Nat)) :=
      mul_le_mul_of_nonneg_left hnormalized hscale
    _ = prespecifiedBatchCumulativeJumpEnvelope K theta h := by
      unfold prespecifiedBatchCumulativeShotScale
        prespecifiedBatchCumulativeJumpEnvelope r
      have hratio (s q e : Real) (hs : s ≠ 0) :
          (s / q) * (e / s) = e / q := by
        have hcancel : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
        simp only [div_eq_mul_inv]
        calc
          s * q⁻¹ * (e * s⁻¹) =
              (s * s⁻¹) * e * q⁻¹ := by ring
          _ = e * q⁻¹ := by rw [hcancel]; ring
      simpa [Nat.mul_comm] using
        hratio
          (Real.sqrt (exactConcreteBatchFinalBlocks shot.1 * 3 : Nat))
          (prespecifiedBatchSampleScale K)
          (mixedProjectedScoreEnvelope theta h)
          (by rw [Nat.mul_comm]; exact ne_of_gt hsqrt)

theorem prespecifiedBatchTotalObservations_eq_cumulativeCount (K : Nat) :
    prespecifiedBatchTotalObservations K =
      cumulativeCount exactConcreteBatchSize K := by
  simp [prespecifiedBatchTotalObservations, cumulativeCount]

theorem prespecifiedBatchSampleScale_tendsto_atTop :
    Tendsto prespecifiedBatchSampleScale atTop atTop := by
  have htotal : Tendsto
      (fun K => (prespecifiedBatchTotalObservations K : Real)) atTop atTop := by
    simpa [prespecifiedBatchTotalObservations_eq_cumulativeCount] using
      exactConcreteBatch_totalSamples_tendsto_atTop
  exact Real.tendsto_sqrt_atTop.comp htotal

theorem prespecifiedBatchCumulativeJumpEnvelope_tendsto_zero
    (theta h : RLSVector 3) :
    Tendsto (fun K => prespecifiedBatchCumulativeJumpEnvelope K theta h)
      atTop (nhds 0) := by
  have hinv : Tendsto (fun K => (prespecifiedBatchSampleScale K)⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp prespecifiedBatchSampleScale_tendsto_atTop
  simpa [prespecifiedBatchCumulativeJumpEnvelope, div_eq_mul_inv] using
    tendsto_const_nhds.mul hinv

/-- Strong bounded-jump Lindeberg reduction: eventually every individual
truncated-square integrand is identically zero, on every sample path. -/
theorem prespecifiedBatchCumulativeLindebergTruncand_eventually_zero
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    Filter.Eventually (fun K =>
      forall t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
      forall omega : ExactConcretePredeterminedBatchPath,
        (if epsilon <
            |prespecifiedBatchCumulativeEnumeratedIncrement theta h b K t omega|
          then prespecifiedBatchCumulativeEnumeratedIncrement theta h b K t omega ^ 2
          else 0) = 0) atTop := by
  have heventually : Filter.Eventually
      (fun K => prespecifiedBatchCumulativeJumpEnvelope K theta h < epsilon)
      atTop :=
    (prespecifiedBatchCumulativeJumpEnvelope_tendsto_zero theta h).eventually
      (gt_mem_nhds hepsilon)
  filter_upwards [heventually] with K hK
  intro t omega
  have hbound := prespecifiedBatchCumulativeShotIncrement_abs_le
    K theta h b hInterior
      (prespecifiedBatchCumulativeFinalShotOrderIso K t) omega
  have hbound' :
      |prespecifiedBatchCumulativeEnumeratedIncrement theta h b K t omega| <=
        prespecifiedBatchCumulativeJumpEnvelope K theta h := by
    simpa [prespecifiedBatchCumulativeEnumeratedIncrement] using hbound
  have hnot : ¬(epsilon <
      |prespecifiedBatchCumulativeEnumeratedIncrement theta h b K t omega|) :=
    not_lt_of_ge (le_of_lt (hbound'.trans_lt hK))
  simp [hnot]

/-! ## Exact Hall--Heyde boundary -/

/-- Concrete predictable conditional variance of one cumulative increment. -/
def prespecifiedBatchCumulativeConditionalVariance
    (theta h b : RLSVector 3)
    (K : Nat) (t : Fin (prespecifiedBatchCumulativeFinalRowLength K))
    (omega : ExactConcretePredeterminedBatchPath) : Real :=
  let shot := prespecifiedBatchCumulativeFinalShotOrderIso K t
  let axis := mixedTwoStageFinalAxis
    (exactConcreteBatchSelectedFrame shot.1 b) (omega shot.1).1 shot.2
  (prespecifiedBatchSampleScale K)⁻¹ ^ 2 *
    (QubitOracle.blochDot h axis ^ 2 /
      (1 - QubitOracle.blochDot theta axis ^ 2))

/-- The sole protocol-specific limit needed after finite martingale identities:
the cumulative predictable Fisher quadratic converges in probability. -/
def PrespecifiedBatchCumulativeFisherConvergesInProbability
    (theta h b : RLSVector 3)
    (hphysical : PauliPilotPhysicalBloch theta) (sigmaSq : Real) : Prop :=
  HallHeydeScalarConvergesInProbability
    (exactConcretePredeterminedBatchPathMeasure theta b hphysical)
    (fun K omega =>
      ∑ t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
        prespecifiedBatchCumulativeConditionalVariance theta h b K t omega)
    sigmaSq

/-- Narrow remaining nested-filtration certificate.  Its fields are exactly
the finite common-space measurability, integrability, and conditional-
expectation identities not supplied by the existing one-pilot common-space
API.  Lindeberg convergence is retained explicitly until those conditional
expectations are transported through the multi-batch filtration. -/
structure PrespecifiedBatchCumulativeMartingaleCertificate
    (theta h b : RLSVector 3)
    (hphysical : PauliPilotPhysicalBloch theta) where
  filtration : Nat -> Filtration Nat
    (inferInstance : MeasurableSpace ExactConcretePredeterminedBatchPath)
  conditionalLindeberg :
    Real -> (K : Nat) ->
      Fin (prespecifiedBatchCumulativeFinalRowLength K) ->
      ExactConcretePredeterminedBatchPath -> Real
  condition321 :
    forall n k : Nat,
      k <= prespecifiedBatchCumulativeFinalRowLength n ->
      k <= prespecifiedBatchCumulativeFinalRowLength (n + 1) ->
        filtration n k <= filtration (n + 1) k
  increment_measurable : forall K
      (t : Fin (prespecifiedBatchCumulativeFinalRowLength K)),
    Measurable[filtration K (t.1 + 1)]
      (prespecifiedBatchCumulativeEnumeratedIncrement theta h b K t)
  increment_integrable : forall K
      (t : Fin (prespecifiedBatchCumulativeFinalRowLength K)),
    Integrable (prespecifiedBatchCumulativeEnumeratedIncrement theta h b K t)
      (exactConcretePredeterminedBatchPathMeasure theta b hphysical)
  increment_square_integrable : forall K
      (t : Fin (prespecifiedBatchCumulativeFinalRowLength K)),
    Integrable (fun omega =>
      prespecifiedBatchCumulativeEnumeratedIncrement theta h b K t omega ^ 2)
      (exactConcretePredeterminedBatchPathMeasure theta b hphysical)
  martingaleDifference : forall K
      (t : Fin (prespecifiedBatchCumulativeFinalRowLength K)),
    (exactConcretePredeterminedBatchPathMeasure theta b hphysical)[
      prespecifiedBatchCumulativeEnumeratedIncrement theta h b K t |
        filtration K t.1] =ᵐ[
          exactConcretePredeterminedBatchPathMeasure theta b hphysical]
      (fun _ => (0 : Real))
  conditionalVarianceVersion : forall K
      (t : Fin (prespecifiedBatchCumulativeFinalRowLength K)),
    (exactConcretePredeterminedBatchPathMeasure theta b hphysical)[
      (fun omega =>
        prespecifiedBatchCumulativeEnumeratedIncrement theta h b K t omega ^ 2) |
        filtration K t.1] =ᵐ[
          exactConcretePredeterminedBatchPathMeasure theta b hphysical]
      prespecifiedBatchCumulativeConditionalVariance theta h b K t
  conditionalLindebergVersion : forall epsilon : Real, 0 < epsilon ->
    forall K (t : Fin (prespecifiedBatchCumulativeFinalRowLength K)),
    (exactConcretePredeterminedBatchPathMeasure theta b hphysical)[
      (fun omega =>
        if epsilon <
            |prespecifiedBatchCumulativeEnumeratedIncrement theta h b K t omega|
          then prespecifiedBatchCumulativeEnumeratedIncrement theta h b K t omega ^ 2
          else 0) | filtration K t.1] =ᵐ[
            exactConcretePredeterminedBatchPathMeasure theta b hphysical]
      conditionalLindeberg epsilon K t
  conditionalLindeberg_converges : forall epsilon : Real, 0 < epsilon ->
    HallHeydeScalarConvergesInProbability
      (exactConcretePredeterminedBatchPathMeasure theta b hphysical)
      (fun K omega =>
        ∑ t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
          conditionalLindeberg epsilon K t omega)
      0

/-- Assemble the source-faithful Hall--Heyde premise record from the narrow
finite-filtration certificate and the concrete Fisher convergence statement. -/
def prespecifiedBatchCumulativeHallHeydePremises
    (theta h b : RLSVector 3)
    (hphysical : PauliPilotPhysicalBloch theta)
    (sigmaSq : Real) (hsigmaSq : 0 <= sigmaSq)
    (certificate : PrespecifiedBatchCumulativeMartingaleCertificate
      theta h b hphysical)
    (hFisher : PrespecifiedBatchCumulativeFisherConvergesInProbability
      theta h b hphysical sigmaSq) :
    HallHeyde1980Corollary31DeterministicVariancePremises
      (exactConcretePredeterminedBatchPathMeasure theta b hphysical)
      prespecifiedBatchCumulativeFinalRowLength certificate.filtration
      (prespecifiedBatchCumulativeEnumeratedIncrement theta h b)
      (prespecifiedBatchCumulativeConditionalVariance theta h b)
      certificate.conditionalLindeberg sigmaSq where
  condition321 := certificate.condition321
  increment_measurable := certificate.increment_measurable
  increment_integrable := certificate.increment_integrable
  increment_square_integrable := certificate.increment_square_integrable
  martingaleDifference := certificate.martingaleDifference
  conditionalVarianceVersion := certificate.conditionalVarianceVersion
  conditionalLindebergVersion := certificate.conditionalLindebergVersion
  sigmaSq_nonnegative := hsigmaSq
  conditionalVariance_converges := hFisher
  conditionalLindeberg_converges := certificate.conditionalLindeberg_converges

/-- Distributional conclusion with its constant probability-family instance
packaged internally. -/
def PrespecifiedBatchCumulativeFinalScoreCLT
    (theta h b : RLSVector 3)
    (hphysical : PauliPilotPhysicalBloch theta)
    (sigmaSq : Real) : Prop := by
  letI : IsProbabilityMeasure
      (exactConcretePredeterminedBatchPathMeasure theta b hphysical) :=
    exactConcretePredeterminedBatchPathMeasure_isProbability
      theta b hphysical
  letI : ∀ _ : Nat, IsProbabilityMeasure
      (exactConcretePredeterminedBatchPathMeasure theta b hphysical) :=
    fun _ => inferInstance
  exact TendstoInDistribution
    (hallHeydeDeterministicVarianceRowSum
      prespecifiedBatchCumulativeFinalRowLength
      (prespecifiedBatchCumulativeEnumeratedIncrement theta h b))
    atTop id
    (fun _ => exactConcretePredeterminedBatchPathMeasure theta b hphysical)
    (gaussianReal 0 sigmaSq.toNNReal)

/-- Scalar cumulative final-score CLT from the already isolated Hall--Heyde
literature atom.  No protocol-specific limit is asserted without a proof
value. -/
theorem prespecifiedBatchCumulativeFinalScore_CLT_of_hallHeyde
    (theta h b : RLSVector 3)
    (hphysical : PauliPilotPhysicalBloch theta)
    (sigmaSq : Real) (hsigmaSq : 0 <= sigmaSq)
    (certificate : PrespecifiedBatchCumulativeMartingaleCertificate
      theta h b hphysical)
    (hFisher : PrespecifiedBatchCumulativeFisherConvergesInProbability
      theta h b hphysical sigmaSq) :
    PrespecifiedBatchCumulativeFinalScoreCLT theta h b hphysical sigmaSq := by
  unfold PrespecifiedBatchCumulativeFinalScoreCLT
  letI : IsProbabilityMeasure
      (exactConcretePredeterminedBatchPathMeasure theta b hphysical) :=
    exactConcretePredeterminedBatchPathMeasure_isProbability theta b hphysical
  exact hallHeyde1980_corollary3_1_deterministicVariance_external
    (exactConcretePredeterminedBatchPathMeasure theta b hphysical)
    prespecifiedBatchCumulativeFinalRowLength certificate.filtration
    (prespecifiedBatchCumulativeEnumeratedIncrement theta h b)
    (prespecifiedBatchCumulativeConditionalVariance theta h b)
    certificate.conditionalLindeberg sigmaSq
    (prespecifiedBatchCumulativeHallHeydePremises theta h b hphysical
      sigmaSq hsigmaSq certificate hFisher)

end

end QubitOracle.Paper
