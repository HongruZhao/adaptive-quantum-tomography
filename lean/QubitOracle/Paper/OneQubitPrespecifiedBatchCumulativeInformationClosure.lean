import QubitOracle.Paper.OneQubitPrespecifiedBatchCumulativeScoreCLT
import Mathlib.Probability.BorelCantelli

/-!
# Cumulative information closure for the prespecified-batch qubit protocol

This module closes the protocol-specific predictable-Fisher premise used by
the cumulative Hall--Heyde row.  The proof is entirely internal:

* the exact Hoeffding pilot tails are summable at the shrinking threshold
  `1 / (k + 1)`;
* first Borel--Cantelli gives almost-sure coordinatewise convergence of the
  literal controller on the common infinite Born product law;
* the exact cycle identity and the polynomial weighted Toeplitz theorem give
  the cumulative final-shot Fisher limit pathwise;
* almost-sure convergence is transported to convergence in measure, hence to
  the deviation-event formulation used by `HallHeydeScalarConvergesInProbability`.

The file also identifies the selected truth-frame information with the Bures
information target and proves a concrete boundedness certificate for the
actual complete-Pauli pilot information.  No protocol premise is introduced.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory Matrix
open scoped BigOperators ENNReal Topology Matrix
open OneQubitPredeterminedBatchHeadline
open PureMultilevelSequentialBatchAdaptive

noncomputable section

set_option maxRecDepth 2000

attribute [local instance]
  pauliPilotBornPathMeasurableSpace
  mixedTwoStageFiniteRowMeasurableSpace
  mixedTwoStageFiniteRowMeasurableSingletonClass

/-- Per-exploitation-observation directional Fisher information of the exact
equal-cycle frame selected in batch `k`.  This is the scalar layer of the
Bures information module, repeated here because that module and the
cumulative-score module currently load conflicting legacy declarations of
the truth-frame matrix. -/
def exactCumulativeBatchFrameDirectionalInformation
    (theta h b : Fin 3 -> Real) (k : Nat)
    (pilot : PauliPilotPath (exactConcreteBatchPilotBlocks k)) : Real :=
  mixedPolynomialFrameDirectionalInformation theta h
    (mixedPilotSelectedLocalFrame b (pauliPilotEstimate pilot))

/-! ## Summable exact pilot tails and almost-sure controller convergence -/

/-- Shrinking coordinate threshold used for the first Borel--Cantelli step. -/
def exactConcretePilotShrinkingThreshold (k : Nat) : Real :=
  (k + 1 : Real)⁻¹

theorem exactConcretePilotShrinkingThreshold_pos (k : Nat) :
    0 < exactConcretePilotShrinkingThreshold k := by
  unfold exactConcretePilotShrinkingThreshold
  positivity

theorem exactConcretePilotShrinkingThreshold_tendsto_zero :
    Tendsto exactConcretePilotShrinkingThreshold atTop (nhds 0) := by
  unfold exactConcretePilotShrinkingThreshold
  simpa only [Nat.cast_add, Nat.cast_one, one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun k : Nat => 1 / ((k : Real) + 1)) atTop (nhds 0))

/-- The cubic pilot schedule and threshold `1/(k+1)` leave a linear
Hoeffding exponent. -/
theorem exactConcreteBatchPilot_exponent_lower (k : Nat) :
    (27 : Real) * (k + 1) <=
      (exactConcreteBatchPilotBlocks k : Real) *
        exactConcretePilotShrinkingThreshold k ^ 2 := by
  have hk0 : 0 <= (k : Real) := by positivity
  have hk1 : 0 < (k : Real) + 1 := by positivity
  unfold exactConcretePilotShrinkingThreshold exactConcreteBatchPilotBlocks
  push_cast
  rw [inv_pow, le_mul_inv_iff₀ (sq_pos_of_pos hk1)]
  nlinarith [sq_nonneg (k : Real),
    mul_nonneg hk0 (sq_nonneg (k : Real))]

/-- A geometric ENNReal envelope dominating the shrinking-threshold pilot
failure probability. -/
def exactConcretePilotGeometricEnvelope (k : Nat) : ENNReal :=
  ENNReal.ofReal (2 * Real.exp (-(27 / 2 : Real) * (k + 1)))

theorem exactConcretePilotHoeffdingEnvelope_le_geometric (k : Nat) :
    pauliPilotCoordinateHoeffdingEnvelope
        (exactConcreteBatchPilotIndex k)
        (exactConcretePilotShrinkingThreshold k) <=
      exactConcretePilotGeometricEnvelope k := by
  unfold pauliPilotCoordinateHoeffdingEnvelope
  rw [Nat.succ_eq_add_one]
  rw [exactConcreteBatchPilotIndex_succ]
  unfold exactConcretePilotGeometricEnvelope
  rw [ENNReal.ofReal_mul (by norm_num : (0 : Real) <= 2)]
  norm_num
  gcongr
  have h := exactConcreteBatchPilot_exponent_lower k
  nlinarith

theorem exactConcretePilotGeometricEnvelope_tsum_ne_top :
    (∑' k : Nat, exactConcretePilotGeometricEnvelope k) ≠ ∞ := by
  have hreal : Summable
      (fun k : Nat => 2 * Real.exp (-(27 / 2 : Real) * (k + 1))) := by
    exact (Real.summable_exp_nat_mul_of_ge
      (c := -(27 / 2 : Real)) (by norm_num) (fun k => by norm_num)).mul_left 2
  exact hreal.tsum_ofReal_ne_top

/-- For each Bloch coordinate, the exact shrinking-threshold bad events are
summable under the common infinite Born law. -/
theorem exactConcretePredeterminedBatchController_badEvent_tsum_ne_top
    (theta b : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (j : Fin 3) :
    (∑' k : Nat,
      exactConcretePredeterminedBatchPathMeasure theta b hphysical
        {omega |
          exactConcretePilotShrinkingThreshold k <=
            |exactConcretePredeterminedBatchPathController k omega j -
              theta j|}) ≠ ∞ := by
  apply ne_top_of_le_ne_top exactConcretePilotGeometricEnvelope_tsum_ne_top
  apply ENNReal.tsum_le_tsum
  intro k
  exact (exactConcretePredeterminedBatchPathController_coordinate_tail
    theta b hphysical k j (exactConcretePilotShrinkingThreshold k)
      (exactConcretePilotShrinkingThreshold_pos k)).trans
        (exactConcretePilotHoeffdingEnvelope_le_geometric k)

/-- First Borel--Cantelli upgrades the exact coordinate concentration to
almost-sure coordinatewise controller convergence. -/
theorem exactConcretePredeterminedBatchPathController_tendsto_ae
    (theta b : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta) :
    ∀ᵐ omega ∂exactConcretePredeterminedBatchPathMeasure theta b hphysical,
      ∀ j : Fin 3,
        Tendsto
          (fun k => exactConcretePredeterminedBatchPathController k omega j)
          atTop (nhds (theta j)) := by
  have hcoord : ∀ j : Fin 3,
      ∀ᵐ omega ∂exactConcretePredeterminedBatchPathMeasure theta b hphysical,
        Tendsto
          (fun k => exactConcretePredeterminedBatchPathController k omega j)
          atTop (nhds (theta j)) := by
    intro j
    have hBC := ae_eventually_notMem
      (exactConcretePredeterminedBatchController_badEvent_tsum_ne_top
        theta b hphysical j)
    filter_upwards [hBC] with omega homega
    apply (tendsto_iff_norm_sub_tendsto_zero).2
    simpa [Real.norm_eq_abs] using
      (squeeze_zero'
        (Eventually.of_forall fun k => abs_nonneg
          (exactConcretePredeterminedBatchPathController k omega j - theta j))
        (homega.mono fun k hk => by
          change ¬ exactConcretePilotShrinkingThreshold k <=
            |exactConcretePredeterminedBatchPathController k omega j - theta j| at hk
          exact le_of_not_ge hk)
        exactConcretePilotShrinkingThreshold_tendsto_zero)
  filter_upwards [hcoord 0, hcoord 1, hcoord 2] with omega h0 h1 h2
  intro j
  fin_cases j <;> assumption

/-! ## Uniform concrete exploration and exploitation bounds -/

/-- Interior squared-norm gap used in all finite information bounds. -/
def exactConcreteMixedInformationGap (theta : RLSVector 3) : Real :=
  1 - QubitOracle.blochNormSq theta

theorem exactConcreteMixedInformationGap_pos
    (theta : RLSVector 3) (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta) :
    0 < exactConcreteMixedInformationGap theta := by
  unfold exactConcreteMixedInformationGap
  linarith [hTruth.2]

private theorem directionalFisherTerm_nonnegative_and_le
    (theta h axis : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (haxis : QubitOracle.blochNormSq axis = 1) :
    0 <= QubitOracle.blochDot h axis ^ 2 /
        (1 - QubitOracle.blochDot theta axis ^ 2) ∧
      QubitOracle.blochDot h axis ^ 2 /
          (1 - QubitOracle.blochDot theta axis ^ 2) <=
        QubitOracle.blochNormSq h /
          exactConcreteMixedInformationGap theta := by
  let gamma := exactConcreteMixedInformationGap theta
  have hgamma : 0 < gamma := exactConcreteMixedInformationGap_pos theta hTruth
  have htheta : QubitOracle.blochNormSq theta <= 1 - gamma := by
    simp [gamma, exactConcreteMixedInformationGap]
  have hden := mixedAxis_denominator_ge_of_normSq_le
    theta axis gamma htheta haxis
  have hdenpos : 0 < 1 - QubitOracle.blochDot theta axis ^ 2 :=
    hgamma.trans_le hden
  have hnum := blochDot_sq_le_normSq_mul_normSq h axis
  rw [haxis, mul_one] at hnum
  have hnorm : 0 <= QubitOracle.blochNormSq h := by
    unfold QubitOracle.blochNormSq
    positivity
  have hC : 0 <= QubitOracle.blochNormSq h / gamma :=
    div_nonneg hnorm hgamma.le
  constructor
  · exact div_nonneg (sq_nonneg _) hdenpos.le
  · rw [div_le_iff₀ hdenpos]
    calc
      QubitOracle.blochDot h axis ^ 2 <= QubitOracle.blochNormSq h := hnum
      _ = (QubitOracle.blochNormSq h / gamma) * gamma := by
        field_simp [hgamma.ne']
      _ <= (QubitOracle.blochNormSq h / gamma) *
          (1 - QubitOracle.blochDot theta axis ^ 2) :=
        mul_le_mul_of_nonneg_left hden hC

/-- Every selected equal-cycle directional information is nonnegative and
uniformly bounded at the fixed interior truth. -/
theorem exactCumulativeBatchFrameDirectionalInformation_nonnegative_and_le
    (theta h b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (k : Nat) (pilot : PauliPilotPath (exactConcreteBatchPilotBlocks k)) :
    0 <= exactCumulativeBatchFrameDirectionalInformation theta h b k pilot ∧
      exactCumulativeBatchFrameDirectionalInformation theta h b k pilot <=
        QubitOracle.blochNormSq h /
          exactConcreteMixedInformationGap theta := by
  let C := QubitOracle.blochNormSq h / exactConcreteMixedInformationGap theta
  have hterm : ∀ j : Fin 3,
      0 <= mixedTwoStageFrameColumnDirectionalFisherTerm theta h
          (exactConcreteBatchSelectedFrame k b) pilot j ∧
      mixedTwoStageFrameColumnDirectionalFisherTerm theta h
          (exactConcreteBatchSelectedFrame k b) pilot j <= C := by
    intro j
    exact directionalFisherTerm_nonnegative_and_le theta h _ hTruth
      (exactConcreteBatchSelectedFrame_unit k b pilot j)
  constructor
  · unfold exactCumulativeBatchFrameDirectionalInformation
      mixedPolynomialFrameDirectionalInformation
    exact mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun j _ => (hterm j).1)
  · unfold exactCumulativeBatchFrameDirectionalInformation
      mixedPolynomialFrameDirectionalInformation
    calc
      (1 / 3 : Real) * ∑ j : Fin 3,
          mixedTwoStageFrameColumnDirectionalFisherTerm theta h
            (exactConcreteBatchSelectedFrame k b) pilot j <=
        (1 / 3 : Real) * ∑ _j : Fin 3, C :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun j _ => (hterm j).2) (by norm_num)
      _ = C := by simp [Fin.sum_univ_succ]

/-- Actual directional information per observation of a complete cyclic-Pauli
pilot block. -/
def exactConcretePauliPilotDirectionalInformation
    (theta h : RLSVector 3) : Real :=
  (1 / 3 : Real) * ∑ a : Fin 3,
    QubitOracle.blochDot h (prespecifiedBatchPauliAxis a) ^ 2 /
      (1 - QubitOracle.blochDot theta (prespecifiedBatchPauliAxis a) ^ 2)

private theorem prespecifiedBatchPauliAxis_unit (a : Fin 3) :
    QubitOracle.blochNormSq (prespecifiedBatchPauliAxis a) = 1 := by
  fin_cases a <;>
    norm_num [prespecifiedBatchPauliAxis, QubitOracle.blochNormSq,
      Fin.sum_univ_succ]

/-- Literal complete-Pauli pilot information has the same finite interior
bound as a selected exploitation frame. -/
theorem exactConcretePauliPilotDirectionalInformation_nonnegative_and_le
    (theta h : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta) :
    0 <= exactConcretePauliPilotDirectionalInformation theta h ∧
      exactConcretePauliPilotDirectionalInformation theta h <=
        QubitOracle.blochNormSq h /
          exactConcreteMixedInformationGap theta := by
  have hterm : ∀ a : Fin 3,
      0 <= QubitOracle.blochDot h (prespecifiedBatchPauliAxis a) ^ 2 /
          (1 - QubitOracle.blochDot theta
            (prespecifiedBatchPauliAxis a) ^ 2) ∧
      QubitOracle.blochDot h (prespecifiedBatchPauliAxis a) ^ 2 /
          (1 - QubitOracle.blochDot theta
            (prespecifiedBatchPauliAxis a) ^ 2) <=
        QubitOracle.blochNormSq h /
          exactConcreteMixedInformationGap theta := by
    intro a
    exact directionalFisherTerm_nonnegative_and_le theta h _ hTruth
      (prespecifiedBatchPauliAxis_unit a)
  constructor
  · unfold exactConcretePauliPilotDirectionalInformation
    exact mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun a _ => (hterm a).1)
  · unfold exactConcretePauliPilotDirectionalInformation
    calc
      (1 / 3 : Real) * ∑ a : Fin 3,
          QubitOracle.blochDot h (prespecifiedBatchPauliAxis a) ^ 2 /
            (1 - QubitOracle.blochDot theta
              (prespecifiedBatchPauliAxis a) ^ 2) <=
        (1 / 3 : Real) * ∑ _a : Fin 3,
          QubitOracle.blochNormSq h /
            exactConcreteMixedInformationGap theta :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun a _ => (hterm a).2) (by norm_num)
      _ = QubitOracle.blochNormSq h /
          exactConcreteMixedInformationGap theta := by
        simp [Fin.sum_univ_succ]

/-- The bounded exploration-versus-exploitation premise is discharged for
the literal Pauli pilot rows in every local direction. -/
theorem exactConcretePauliPilotDirectionalInformation_sub_frame_norm_le
    (theta h b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (k : Nat) (pilot : PauliPilotPath (exactConcreteBatchPilotBlocks k)) :
    ‖exactConcretePauliPilotDirectionalInformation theta h -
      exactCumulativeBatchFrameDirectionalInformation theta h b k pilot‖ <=
      2 * (QubitOracle.blochNormSq h /
        exactConcreteMixedInformationGap theta) := by
  have hp :=
    exactConcretePauliPilotDirectionalInformation_nonnegative_and_le
      theta h hTruth
  have hf :=
    exactCumulativeBatchFrameDirectionalInformation_nonnegative_and_le
      theta h b hTruth k pilot
  rw [Real.norm_eq_abs]
  calc
    |exactConcretePauliPilotDirectionalInformation theta h -
        exactCumulativeBatchFrameDirectionalInformation theta h b k pilot| <=
      |exactConcretePauliPilotDirectionalInformation theta h| +
        |exactCumulativeBatchFrameDirectionalInformation theta h b k pilot| :=
      abs_sub _ _
    _ = exactConcretePauliPilotDirectionalInformation theta h +
        exactCumulativeBatchFrameDirectionalInformation theta h b k pilot := by
      rw [abs_of_nonneg hp.1, abs_of_nonneg hf.1]
    _ <= 2 * (QubitOracle.blochNormSq h /
        exactConcreteMixedInformationGap theta) := by linarith

/-! ## Exact cumulative final-shot Fisher identity -/

/-- The cumulative final-shot conditional variance is exactly the completed-
batch predictable average with zero pilot contribution. -/
theorem prespecifiedBatchCumulativeConditionalVariance_sum_eq_batched
    (theta h b : RLSVector 3) (K : Nat)
    (omega : ExactConcretePredeterminedBatchPath) :
    (∑ t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
      prespecifiedBatchCumulativeConditionalVariance theta h b K t omega) =
      batchedPredictableScalarAverage exactConcreteBatchSize
        exactConcreteBatchExplorationSize
        (fun k => exactCumulativeBatchFrameDirectionalInformation
          theta h b k (omega k).1)
        (fun _ => 0) K := by
  classical
  by_cases hK : K = 0
  · subst K
    have hrow : prespecifiedBatchCumulativeFinalRowLength 0 = 0 := by
      simpa using prespecifiedBatchCumulativeFinalRowLength_eq_sum 0
    letI : IsEmpty (Fin (prespecifiedBatchCumulativeFinalRowLength 0)) :=
      Fintype.card_eq_zero_iff.mp (by simpa using hrow)
    simp [batchedPredictableScalarAverage]
  · have hKpos : 0 < K := Nat.pos_of_ne_zero hK
    have hNpos : 0 < prespecifiedBatchTotalObservations K := by
      rw [prespecifiedBatchTotalObservations_eq_cumulativeCount,
        exactConcreteBatchSize_cumulative]
      positivity
    have hscale : (prespecifiedBatchSampleScale K)⁻¹ ^ 2 =
        (prespecifiedBatchTotalObservations K : Real)⁻¹ := by
      unfold prespecifiedBatchSampleScale
      rw [inv_pow, Real.sq_sqrt (by positivity :
        0 <= (prespecifiedBatchTotalObservations K : Real))]
    have hbatch (k : Nat) :
        (∑ t : Fin (3 * exactConcreteBatchFinalBlocks k),
          mixedTwoStageFinalDirectionalFisherTerm theta h
            (exactConcreteBatchSelectedFrame k b) (omega k).1 t) =
        (3 * exactConcreteBatchFinalBlocks k : Nat) *
          exactCumulativeBatchFrameDirectionalInformation
            theta h b k (omega k).1 := by
      rw [mixedTwoStageExactCycleInformation_sum]
      unfold mixedTwoStageFrameColumnDirectionalFisherTerm
      have hframe :
          (exactConcreteBatchSelectedFrame k b).frame (omega k).1 =
            mixedPilotSelectedLocalFrame b (pauliPilotEstimate (omega k).1) := rfl
      rw [hframe]
      unfold exactCumulativeBatchFrameDirectionalInformation
        mixedPolynomialFrameDirectionalInformation
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      simp only [div_eq_mul_inv]
      ring
    have hsub (k : Nat) :
        exactConcreteBatchSize k - exactConcreteBatchExplorationSize k =
          3 * exactConcreteBatchFinalBlocks k := by
      rw [exactConcreteBatchSize_decompose]
      omega
    rw [show (∑ t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
        prespecifiedBatchCumulativeConditionalVariance theta h b K t omega) =
        (prespecifiedBatchTotalObservations K : Real)⁻¹ *
          ∑ k : Fin K,
            (3 * exactConcreteBatchFinalBlocks k : Nat) *
              exactCumulativeBatchFrameDirectionalInformation
                theta h b k (omega k).1 by
      calc
        (∑ t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
            prespecifiedBatchCumulativeConditionalVariance theta h b K t omega) =
          ∑ shot : PrespecifiedBatchCumulativeFinalShotIndex K,
            (prespecifiedBatchSampleScale K)⁻¹ ^ 2 *
              mixedTwoStageFinalDirectionalFisherTerm theta h
                (exactConcreteBatchSelectedFrame shot.1 b)
                (omega shot.1).1 shot.2 := by
            exact Fintype.sum_equiv
              (prespecifiedBatchCumulativeFinalShotOrderIso K).toEquiv
              (fun t => prespecifiedBatchCumulativeConditionalVariance
                theta h b K t omega)
              (fun shot => (prespecifiedBatchSampleScale K)⁻¹ ^ 2 *
                mixedTwoStageFinalDirectionalFisherTerm theta h
                  (exactConcreteBatchSelectedFrame shot.1 b)
                  (omega shot.1).1 shot.2)
              (fun t => rfl)
        _ = ∑ shot : Sigma fun k : Fin K =>
              Fin (3 * exactConcreteBatchFinalBlocks k),
            (prespecifiedBatchSampleScale K)⁻¹ ^ 2 *
              mixedTwoStageFinalDirectionalFisherTerm theta h
                (exactConcreteBatchSelectedFrame (toLex shot).1 b)
                (omega (toLex shot).1).1 (toLex shot).2 := by
              exact Fintype.sum_equiv ofLex
                (fun shot : PrespecifiedBatchCumulativeFinalShotIndex K =>
                  (prespecifiedBatchSampleScale K)⁻¹ ^ 2 *
                    mixedTwoStageFinalDirectionalFisherTerm theta h
                      (exactConcreteBatchSelectedFrame shot.1 b)
                      (omega shot.1).1 shot.2)
                (fun shot : Sigma fun k : Fin K =>
                    Fin (3 * exactConcreteBatchFinalBlocks k) =>
                  (prespecifiedBatchSampleScale K)⁻¹ ^ 2 *
                    mixedTwoStageFinalDirectionalFisherTerm theta h
                      (exactConcreteBatchSelectedFrame (toLex shot).1 b)
                      (omega (toLex shot).1).1 (toLex shot).2)
                (fun _ => rfl)
        _ = ∑ k : Fin K, ∑ t : Fin (3 * exactConcreteBatchFinalBlocks k),
            (prespecifiedBatchSampleScale K)⁻¹ ^ 2 *
              mixedTwoStageFinalDirectionalFisherTerm theta h
                (exactConcreteBatchSelectedFrame k b) (omega k).1 t := by
              rw [Fintype.sum_sigma]
              apply Finset.sum_congr rfl
              intro k _hk
              apply Finset.sum_congr rfl
              intro t _ht
              rfl
        _ = (prespecifiedBatchSampleScale K)⁻¹ ^ 2 *
            ∑ k : Fin K, ∑ t : Fin (3 * exactConcreteBatchFinalBlocks k),
              mixedTwoStageFinalDirectionalFisherTerm theta h
                (exactConcreteBatchSelectedFrame k b) (omega k).1 t := by
              simp_rw [Finset.mul_sum]
        _ = (prespecifiedBatchTotalObservations K : Real)⁻¹ *
            ∑ k : Fin K,
              (3 * exactConcreteBatchFinalBlocks k : Nat) *
                exactCumulativeBatchFrameDirectionalInformation
                  theta h b k (omega k).1 := by
              rw [hscale]
              congr 1
              apply Finset.sum_congr rfl
              intro k _
              exact hbatch k]
    unfold batchedPredictableScalarAverage
    rw [prespecifiedBatchTotalObservations_eq_cumulativeCount]
    simp only [cumulativeCount]
    push_cast
    congr 1
    rw [Fin.sum_univ_eq_sum_range (fun k =>
      (3 : Real) * (exactConcreteBatchFinalBlocks k : Real) *
        exactCumulativeBatchFrameDirectionalInformation
          theta h b k (omega k).1)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [batchAllocation_identity _ _ _ _
      (exactConcreteBatchExplorationSize_le k), hsub]
    simp

/-! ## Almost-sure and in-probability cumulative closure -/

theorem prespecifiedBatchCumulativeConditionalVariance_tendsto_ae
    (theta h b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    ∀ᵐ omega ∂exactConcretePredeterminedBatchPathMeasure theta b
        (mixedNonzeroInterior_pauliPilotPhysical theta hTruth),
      Tendsto
        (fun K => ∑ t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
          prespecifiedBatchCumulativeConditionalVariance theta h b K t omega)
        atTop
        (nhds (mixedPolynomialTruthFrameDirectionalInformation theta h b)) := by
  let hphysical := mixedNonzeroInterior_pauliPilotPhysical theta hTruth
  filter_upwards
    [exactConcretePredeterminedBatchPathController_tendsto_ae
      theta b hphysical] with omega hcontroller
  rw [show (fun K => ∑ t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
      prespecifiedBatchCumulativeConditionalVariance theta h b K t omega) =
      batchedPredictableScalarAverage exactConcreteBatchSize
        exactConcreteBatchExplorationSize
        (fun k => exactCumulativeBatchFrameDirectionalInformation
          theta h b k (omega k).1) (fun _ => 0) by
    funext K
    exact prespecifiedBatchCumulativeConditionalVariance_sum_eq_batched
      theta h b K omega]
  apply batchedPredictableScalarAverage_tendsto
    exactConcreteBatchSize exactConcreteBatchExplorationSize
    (fun k => exactCumulativeBatchFrameDirectionalInformation
      theta h b k (omega k).1) (fun _ => 0)
    (mixedPolynomialTruthFrameDirectionalInformation theta h b)
    (QubitOracle.blochNormSq h / exactConcreteMixedInformationGap theta)
  · simpa [cumulativeCount] using exactConcreteBatch_totalSamples_tendsto_atTop
  · exact mixedPolynomialFrameDirectionalInformation_tendsto_of_coordinatewise
      b theta h
      (fun k => exactConcretePredeterminedBatchPathController k omega)
      hcontroller hTruth hSeed
  · exact div_nonneg (by
      unfold QubitOracle.blochNormSq
      positivity) (exactConcreteMixedInformationGap_pos theta hTruth).le
  · intro k
    have hbnd := exactCumulativeBatchFrameDirectionalInformation_nonnegative_and_le
      theta h b hTruth k (omega k).1
    rw [Real.norm_eq_abs, zero_sub, abs_neg, abs_of_nonneg hbnd.1]
    exact hbnd.2
  · simpa [cumulativeCount] using
      exactConcreteBatch_explorationFraction_tendsto_zero

private theorem prespecifiedBatchCumulativeConditionalVariance_aestronglyMeasurable
    (theta h b : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (K : Nat) :
    AEStronglyMeasurable
      (fun omega => ∑ t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
        prespecifiedBatchCumulativeConditionalVariance theta h b K t omega)
      (exactConcretePredeterminedBatchPathMeasure theta b hphysical) := by
  apply Measurable.aestronglyMeasurable
  rw [show (fun omega => ∑ t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
      prespecifiedBatchCumulativeConditionalVariance theta h b K t omega) =
      fun omega => batchedPredictableScalarAverage exactConcreteBatchSize
        exactConcreteBatchExplorationSize
        (fun k => exactCumulativeBatchFrameDirectionalInformation
          theta h b k (omega k).1) (fun _ => 0) K by
    funext omega
    exact prespecifiedBatchCumulativeConditionalVariance_sum_eq_batched
      theta h b K omega]
  unfold batchedPredictableScalarAverage
  apply Measurable.mul measurable_const
  apply Finset.measurable_sum
  intro k hk
  have hkmeas : Measurable (fun omega : ExactConcretePredeterminedBatchPath =>
      exactCumulativeBatchFrameDirectionalInformation
        theta h b k (omega k).1) :=
    (measurable_of_finite
      (fun row : ExactConcretePredeterminedBatchRow k =>
        exactCumulativeBatchFrameDirectionalInformation theta h b k row.1)).comp
      (measurable_pi_apply k)
  fun_prop

/-- The exact cumulative final-shot predictable Fisher quadratic converges in
measure on the common infinite product Born law. -/
theorem prespecifiedBatchCumulativeConditionalVariance_tendstoInMeasure
    (theta h b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    TendstoInMeasure
      (exactConcretePredeterminedBatchPathMeasure theta b
        (mixedNonzeroInterior_pauliPilotPhysical theta hTruth))
      (fun K omega => ∑ t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
        prespecifiedBatchCumulativeConditionalVariance theta h b K t omega)
      atTop
      (fun _ => mixedPolynomialTruthFrameDirectionalInformation theta h b) := by
  let hphysical := mixedNonzeroInterior_pauliPilotPhysical theta hTruth
  letI : IsProbabilityMeasure
      (exactConcretePredeterminedBatchPathMeasure theta b hphysical) :=
    exactConcretePredeterminedBatchPathMeasure_isProbability theta b hphysical
  apply tendstoInMeasure_of_tendsto_ae
  · intro K
    exact prespecifiedBatchCumulativeConditionalVariance_aestronglyMeasurable
      theta h b hphysical K
  · exact prespecifiedBatchCumulativeConditionalVariance_tendsto_ae
      theta h b hTruth hSeed

/-- Requested concrete closure of the Hall--Heyde predictable-Fisher premise. -/
theorem prespecifiedBatchCumulativeFisherConvergesInProbability_closed
    (theta h b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    PrespecifiedBatchCumulativeFisherConvergesInProbability theta h b
      (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)
      (mixedPolynomialTruthFrameDirectionalInformation theta h b) := by
  unfold PrespecifiedBatchCumulativeFisherConvergesInProbability
    HallHeydeScalarConvergesInProbability
  have hmeasure := prespecifiedBatchCumulativeConditionalVariance_tendstoInMeasure
    theta h b hTruth hSeed
  rw [tendstoInMeasure_iff_dist] at hmeasure
  intro epsilon hepsilon
  simpa [Real.dist_eq] using hmeasure epsilon hepsilon

/-! ## Exact Bures normalization -/

/-- The local truth frame, ordered tangent--tangent--radial, supplies the
geometric structure expected by the Bures stage theorem. -/
noncomputable def mixedPolynomialTruthRadialTangentFrame
    (theta b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    MixedRadialTangentFrame theta where
  radial := mixedTwoStageFrameAxis (localContinuousQubitFrame b theta) 2
  tangentFirst := mixedTwoStageFrameAxis (localContinuousQubitFrame b theta) 0
  tangentSecond := mixedTwoStageFrameAxis (localContinuousQubitFrame b theta) 1
  radial_unit := by
    exact localContinuousQubitFrame_axis_unit ⟨hTruth.1, hSeed⟩ 2
  tangentFirst_unit := by
    exact localContinuousQubitFrame_axis_unit ⟨hTruth.1, hSeed⟩ 0
  tangentSecond_unit := by
    exact localContinuousQubitFrame_axis_unit ⟨hTruth.1, hSeed⟩ 1
  tangentFirst_orthogonal := by
    change QubitOracle.blochDot theta (localFrameFirstTangent b theta) = 0
    have horth := localFrameFirstTangent_dot_radial
      (show LocalContinuousFrameDomain b theta from ⟨hTruth.1, hSeed⟩)
    simp [localNormalizedBlochDirection,
      QubitOracle.blochDot, Fin.sum_univ_succ] at horth ⊢
    have hsqrt : Real.sqrt (QubitOracle.blochNormSq theta) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hTruth.1)
    field_simp [hsqrt] at horth ⊢
    simpa [mul_comm] using horth
  tangentSecond_orthogonal := by
    change QubitOracle.blochDot theta (localFrameSecondTangent b theta) = 0
    have horth := localFrameSecondTangent_dot_radial b theta
    simp [localNormalizedBlochDirection,
      QubitOracle.blochDot, Fin.sum_univ_succ] at horth ⊢
    have hsqrt : Real.sqrt (QubitOracle.blochNormSq theta) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hTruth.1)
    field_simp [hsqrt] at horth ⊢
    simpa [mul_comm] using horth
  radial_dot_sq := by
    change QubitOracle.blochDot theta
      (localNormalizedBlochDirection theta) ^ 2 = QubitOracle.blochNormSq theta
    simp [localNormalizedBlochDirection, QubitOracle.blochDot,
      QubitOracle.blochNormSq, Fin.sum_univ_succ]
    have hsqrt : Real.sqrt (theta 0 ^ 2 + (theta 1 ^ 2 + theta 2 ^ 2)) ≠ 0 := by
      simpa [QubitOracle.blochNormSq, Fin.sum_univ_succ] using
        ne_of_gt (Real.sqrt_pos.2 hTruth.1)
    field_simp [hsqrt]
    nlinarith [Real.sq_sqrt (show 0 <=
      theta 0 ^ 2 + (theta 1 ^ 2 + theta 2 ^ 2) by positivity)]
  resolution := by
    have hmatrix := localContinuousQubitFrame_mul_transpose_self
      (show LocalContinuousFrameDomain b theta from ⟨hTruth.1, hSeed⟩)
    ext i j
    simpa [mixedTwoStageFrameAxis, qubitFrameAxis, QubitOracle.blochOuter,
      Matrix.mul_apply, Fin.sum_univ_succ, add_assoc] using
        congrFun (congrFun hmatrix i) j
  radial_outer_of_nonzero := by
    intro hnonzero
    change QubitOracle.blochOuter (localNormalizedBlochDirection theta) =
      mixedRadialProjector theta
    ext i j
    simp [localNormalizedBlochDirection, mixedRadialProjector,
      QubitOracle.blochOuter]
    have hsqrt : Real.sqrt (QubitOracle.blochNormSq theta) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hTruth.1)
    field_simp [hsqrt, hnonzero]
    rw [Real.sq_sqrt hTruth.1.le]
    ring

/-- The selected truth-frame matrix is exactly the center-safe Bures
information target.  Thus the loss covariance is the inverse of both equal
matrices; the information inverse is not itself the information target. -/
theorem mixedPolynomialTruthFrameInformationMatrix_eq_mixedBuresTarget
    (theta b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    mixedPolynomialTruthFrameInformationMatrix theta b =
      mixedBuresTarget theta := by
  let frame := mixedPolynomialTruthRadialTangentFrame theta b hTruth hSeed
  calc
    mixedPolynomialTruthFrameInformationMatrix theta b =
        mixedStageInformation theta
          (radialTangentMass (1 / 3 : Real) (1 / 3 : Real))
          (radialTangentAxes frame.tangentFirst frame.tangentSecond
            frame.radial) := by
      ext i j
      simp [mixedPolynomialTruthFrameInformationMatrix,
        mixedStageInformation, radialTangentMass, radialTangentAxes,
        QubitOracle.mixedAxisFisher, QubitOracle.blochOuter, frame,
        mixedPolynomialTruthRadialTangentFrame, Fin.sum_univ_succ,
        Matrix.smul_apply, smul_eq_mul, div_eq_mul_inv]
      ring
    _ = mixedBuresTarget theta :=
      mixedStageInformation_bures_exact theta hTruth.2 frame

/-- Exact covariance normalization corresponding to the Bures information
identity. -/
theorem mixedPolynomialTruthFrameInformationMatrix_inv_eq_mixedBuresTarget_inv
    (theta b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    (mixedPolynomialTruthFrameInformationMatrix theta b)⁻¹ =
      (mixedBuresTarget theta)⁻¹ := by
  rw [mixedPolynomialTruthFrameInformationMatrix_eq_mixedBuresTarget
    theta b hTruth hSeed]

#print axioms exactConcretePredeterminedBatchPathController_tendsto_ae
#print axioms exactConcretePauliPilotDirectionalInformation_sub_frame_norm_le
#print axioms prespecifiedBatchCumulativeConditionalVariance_tendstoInMeasure
#print axioms prespecifiedBatchCumulativeFisherConvergesInProbability_closed
#print axioms mixedPolynomialTruthFrameInformationMatrix_eq_mixedBuresTarget
#print axioms mixedPolynomialTruthFrameInformationMatrix_inv_eq_mixedBuresTarget_inv

end

end QubitOracle.Paper
