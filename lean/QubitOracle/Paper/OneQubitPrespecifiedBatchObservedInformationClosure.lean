import QubitOracle.Paper.OneQubitPrespecifiedBatchLikelihoodExpansion
import QubitOracle.Paper.OneQubitPrespecifiedBatchCumulativeInformationClosure
import QubitOracle.Paper.OneQubitPrespecifiedBatchMartingaleCertificateClosure
import QubitOracle.Paper.SourceFaithfulMartingaleMoments

/-!
# Finite-prefix observed-information closure

This module proves the final observed-information law directly on each finite
prefix.  It deliberately avoids the global natural-number decoder: complete
batch rows are the independent coordinates of the finite product measure.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology
open PureMultilevelSequentialBatchAdaptive
open OneQubitPredeterminedBatchHeadline
open PrespecifiedBatchMartingaleClosure

noncomputable section

set_option maxRecDepth 4000

attribute [local instance]
  pauliPilotBornPathMeasurableSpace
  mixedTwoStageFiniteRowMeasurableSpace
  mixedTwoStageFiniteRowMeasurableSingletonClass

/-- Convert the finite-product row index to the corresponding `Fin K`. -/
def prespecifiedBatchRangeFin {K : Nat} (k : Finset.range K) : Fin K :=
  ⟨k.1, Finset.mem_range.mp k.2⟩

/-- Canonical equivalence between the finite-product row index and `Fin K`. -/
def prespecifiedBatchRangeFinEquiv (K : Nat) : Finset.range K ≃ Fin K where
  toFun := prespecifiedBatchRangeFin
  invFun := fun k => ⟨k.1, Finset.mem_range.2 k.2⟩
  left_inv := by intro k; cases k; rfl
  right_inv := by intro k; cases k; rfl

/-- Number of final observations in batch `k`. -/
abbrev prespecifiedBatchFinalSize (k : Nat) : Nat :=
  3 * exactConcreteBatchFinalBlocks k

/-- The centered final observed information contributed by one complete row,
at the cumulative `N_K` normalization. -/
def prespecifiedBatchRowCenteredFinalObservedInformation
    (theta h b : RLSVector 3)
    (K : Nat) (k : Finset.range K)
    (row : ExactConcretePredeterminedBatchRow k.1) : Real :=
  prespecifiedBatchCumulativeShotScale K (prespecifiedBatchRangeFin k) ^ 2 *
    ∑ t : Fin (prespecifiedBatchFinalSize k.1),
      mixedExactCycleCenteredObservedSquare theta h
        (exactConcreteBatchSelectedFrame k.1 b) row.1 t row.2

/-- The final (non-pilot) part of the observed directional information on a
finite prefix. -/
def prespecifiedBatchCumulativeFinalObservedDirectionalInformation
    (theta h b : RLSVector 3) (K : Nat)
    (x : PrespecifiedBatchFinitePrefix K) : Real :=
  ∑ k : Finset.range K,
    ∑ t : Fin (prespecifiedBatchFinalSize k.1),
      prespecifiedBatchFinalNormalizedScore theta h b K k (x k) t ^ 2

/-- The finite-prefix predictable conditional-variance sum for the final
shots. -/
def prespecifiedBatchCumulativeFinalPredictableVariancePrefix
    (theta h b : RLSVector 3) (K : Nat)
    (x : PrespecifiedBatchFinitePrefix K) : Real :=
  ∑ k : Finset.range K,
    prespecifiedBatchCumulativeShotScale K (prespecifiedBatchRangeFin k) ^ 2 *
      mixedExactCycleNormalizedDirectionalFisher theta h
        (r := exactConcreteBatchFinalBlocks k.1)
        (exactConcreteBatchSelectedFrame k.1 b) (x k).1

/-- Sum of the independent centered row functions. -/
def prespecifiedBatchCumulativeCenteredFinalObservedInformation
    (theta h b : RLSVector 3) (K : Nat)
    (x : PrespecifiedBatchFinitePrefix K) : Real :=
  ∑ k : Finset.range K,
    prespecifiedBatchRowCenteredFinalObservedInformation theta h b K k (x k)

/-- A finite prefix can be extended by arbitrary default rows after `K`.
All cumulative quantities below inspect only the first `K` rows. -/
def prespecifiedBatchExtendPrefix {K : Nat}
    (x : PrespecifiedBatchFinitePrefix K) :
    ExactConcretePredeterminedBatchPath :=
  fun n => if hn : n < K then x ⟨n, Finset.mem_range.2 hn⟩ else default

@[simp]
theorem prespecifiedBatchExtendPrefix_apply
    {K : Nat} (x : PrespecifiedBatchFinitePrefix K) (k : Finset.range K) :
    prespecifiedBatchExtendPrefix x k.1 = x k := by
  simp [prespecifiedBatchExtendPrefix, Finset.mem_range.mp k.2]

/-- The likelihood score used on a finite prefix is exactly the cumulative
shot scale times the row-normalized exact-cycle score. -/
theorem prespecifiedBatchFinalNormalizedScore_eq_scaled_finitePrefix
    (theta h b : RLSVector 3) (K : Nat) (k : Finset.range K)
    (row : ExactConcretePredeterminedBatchRow k.1)
    (t : Fin (prespecifiedBatchFinalSize k.1)) :
    prespecifiedBatchFinalNormalizedScore theta h b K k row t =
      prespecifiedBatchCumulativeShotScale K (prespecifiedBatchRangeFin k) *
        mixedExactCycleNormalizedDirectionalScore theta h
          (exactConcreteBatchSelectedFrame k.1 b) row.1 t row.2 := by
  have hdot (axis : Fin 3 -> Real) :
      QubitOracle.blochDot
          (fun j =>
            Real.sqrt (3 * exactConcreteBatchFinalBlocks k.1 : Nat) /
              Real.sqrt (prespecifiedBatchTotalObservations K : Real) * h j)
          axis =
        (Real.sqrt (3 * exactConcreteBatchFinalBlocks k.1 : Nat) /
          Real.sqrt (prespecifiedBatchTotalObservations K : Real)) *
          QubitOracle.blochDot h axis := by
    unfold QubitOracle.blochDot
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold prespecifiedBatchFinalNormalizedScore
    prespecifiedBatchFinalDirection
    prespecifiedBatchCumulativeShotScale
    prespecifiedBatchSampleScale
    exactConcreteBatchExploitationSize
    mixedExactCycleNormalizedDirectionalScore
    mixedTwoStageFinalPathDirectionalScore
    mixedTwoStageFinalShotDirectionalScore
    mixedTwoStageAxisDirectionalScore
    prespecifiedBatchRangeFin
  rw [hdot]
  ring

/-! ## Exact finite-row centering -/

/-- One normalized squared-score innovation has row-law mean zero. -/
theorem prespecifiedBatchCenteredFinalShot_integral_zero
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (k : Nat) (t : Fin (prespecifiedBatchFinalSize k)) :
    (∫ row,
      mixedExactCycleCenteredObservedSquare theta h
        (exactConcreteBatchSelectedFrame k b) row.1 t row.2
      ∂exactConcretePredeterminedBatchRowMeasure theta b k) = 0 := by
  let A := exactBatchArrayData theta h b hInterior k
  let r := exactBatchRowSize k
  have hr : 0 < r := exactBatchRowSize_pos k
  have hcond := A.squaredScore_literal_condExp_eq_oneShotFisher r hr t
  have heq :
      (∫ row, A.currentCoordinateObservable r t
          (A.squaredScoreObservable r t) row ∂A.mathlibRowMeasure r) =
        ∫ row, A.oneShotFisherKernel r t row ∂A.mathlibRowMeasure r := by
    calc
      _ = ∫ row,
          (A.mathlibRowMeasure r)[
            A.currentCoordinateObservable r t (A.squaredScoreObservable r t) |
              A.rowFiltrationSigma r t.1] row
          ∂A.mathlibRowMeasure r := (integral_condExp le_top).symm
      _ = _ := integral_congr_ae hcond
  rw [← exactBatchCommonRowMeasure_eq theta h b hInterior k]
  change
    (∫ row,
      (A.currentCoordinateObservable r t (A.squaredScoreObservable r t) row -
        A.oneShotFisherKernel r t row) ∂A.mathlibRowMeasure r) = 0
  rw [integral_sub
    (A.integrable_mathlibRowMeasure r _)
    (A.integrable_mathlibRowMeasure r _), heq, sub_self]

/-- The complete centered row has exact mean zero. -/
theorem prespecifiedBatchRowCenteredFinalObservedInformation_integral_zero
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K : Nat) (k : Finset.range K) :
    (∫ row,
      prespecifiedBatchRowCenteredFinalObservedInformation theta h b K k row
      ∂exactConcretePredeterminedBatchRowMeasure theta b k.1) = 0 := by
  letI : IsProbabilityMeasure
      (exactConcretePredeterminedBatchRowMeasure theta b k.1) :=
    exactConcretePredeterminedBatchRowMeasure_isProbability theta b
      (le_of_lt hInterior) k.1
  rw [show prespecifiedBatchRowCenteredFinalObservedInformation theta h b K k =
      fun row =>
        prespecifiedBatchCumulativeShotScale K (prespecifiedBatchRangeFin k) ^ 2 *
          ∑ t : Fin (prespecifiedBatchFinalSize k.1),
            mixedExactCycleCenteredObservedSquare theta h
              (exactConcreteBatchSelectedFrame k.1 b) row.1 t row.2 by rfl]
  rw [integral_const_mul, integral_finsetSum]
  · simp [prespecifiedBatchCenteredFinalShot_integral_zero theta h b hInterior]
  · intro t _
    exact Integrable.of_finite

/-! ## Deterministic row and variance bounds -/

/-- Uniform deterministic absolute-value envelope for one row. -/
def prespecifiedBatchRowCenteredFinalEnvelope
    (theta h : RLSVector 3) (K : Nat) (k : Finset.range K) : Real :=
  2 * mixedProjectedScoreEnvelope theta h ^ 2 *
    ((prespecifiedBatchFinalSize k.1 : Nat) : Real) /
      (prespecifiedBatchTotalObservations K : Real)

theorem prespecifiedBatchRowCenteredFinalEnvelope_nonneg
    (theta h : RLSVector 3) (K : Nat) (k : Finset.range K) :
    0 <= prespecifiedBatchRowCenteredFinalEnvelope theta h K k := by
  unfold prespecifiedBatchRowCenteredFinalEnvelope
  positivity

theorem prespecifiedBatchRowCenteredFinalObservedInformation_abs_le
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K : Nat) (k : Finset.range K)
    (row : ExactConcretePredeterminedBatchRow k.1) :
    |prespecifiedBatchRowCenteredFinalObservedInformation theta h b K k row| <=
      prespecifiedBatchRowCenteredFinalEnvelope theta h K k := by
  let m := prespecifiedBatchFinalSize k.1
  have hr : 0 < exactConcreteBatchFinalBlocks k.1 :=
    exactConcreteBatchFinalBlocks_pos k.1
  have hm : 0 < m := Nat.mul_pos (by norm_num) hr
  have hK : 0 < K := lt_of_le_of_lt (Nat.zero_le k.1)
    (Finset.mem_range.mp k.2)
  have hN : 0 < prespecifiedBatchTotalObservations K :=
    prespecifiedBatchTotalObservations_pos K hK
  have hmSq : Real.sqrt (m : Real) ^ 2 = (m : Real) :=
    Real.sq_sqrt (by positivity)
  have hNSq : Real.sqrt (prespecifiedBatchTotalObservations K : Real) ^ 2 =
      (prespecifiedBatchTotalObservations K : Real) :=
    Real.sq_sqrt (by positivity)
  have hsum :
      |∑ t : Fin m,
        mixedExactCycleCenteredObservedSquare theta h
          (exactConcreteBatchSelectedFrame k.1 b) row.1 t row.2| <=
        (m : Real) *
          (2 * (mixedProjectedScoreEnvelope theta h / Real.sqrt (m : Real)) ^ 2) := by
    calc
      |∑ t : Fin m,
          mixedExactCycleCenteredObservedSquare theta h
            (exactConcreteBatchSelectedFrame k.1 b) row.1 t row.2| <=
        ∑ t : Fin m,
          |mixedExactCycleCenteredObservedSquare theta h
            (exactConcreteBatchSelectedFrame k.1 b) row.1 t row.2| :=
          Finset.abs_sum_le_sum_abs _ _
      _ <= ∑ _t : Fin m,
          2 * (mixedProjectedScoreEnvelope theta h / Real.sqrt (m : Real)) ^ 2 := by
        exact Finset.sum_le_sum fun t _ =>
          mixedExactCycleCenteredObservedSquare_abs_le theta h
            (exactConcreteBatchSelectedFrame k.1 b) row.1 t row.2 hInterior hr
      _ = _ := by simp
  unfold prespecifiedBatchRowCenteredFinalObservedInformation
    prespecifiedBatchRowCenteredFinalEnvelope
    prespecifiedBatchCumulativeShotScale prespecifiedBatchSampleScale
  rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  change
    (Real.sqrt (m : Real) / Real.sqrt
      (prespecifiedBatchTotalObservations K : Real)) ^ 2 *
        |∑ t : Fin m,
          mixedExactCycleCenteredObservedSquare theta h
            (exactConcreteBatchSelectedFrame k.1 b) row.1 t row.2| <= _
  rw [div_pow]
  calc
    Real.sqrt (m : Real) ^ 2 /
          Real.sqrt (prespecifiedBatchTotalObservations K : Real) ^ 2 *
        |∑ t : Fin m,
          mixedExactCycleCenteredObservedSquare theta h
            (exactConcreteBatchSelectedFrame k.1 b) row.1 t row.2| <=
      (Real.sqrt (m : Real) ^ 2 /
          Real.sqrt (prespecifiedBatchTotalObservations K : Real) ^ 2) *
        ((m : Real) *
          (2 * (mixedProjectedScoreEnvelope theta h / Real.sqrt (m : Real)) ^ 2)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 2 * mixedProjectedScoreEnvelope theta h ^ 2 * (m : Real) /
        (prespecifiedBatchTotalObservations K : Real) := by
      rw [hmSq, hNSq]
      field_simp [show (m : Real) ≠ 0 by exact_mod_cast Nat.ne_of_gt hm,
        show (prespecifiedBatchTotalObservations K : Real) ≠ 0 by
          exact_mod_cast Nat.ne_of_gt hN]
      nlinarith [hmSq]

theorem prespecifiedBatchRowCenteredFinalObservedInformation_memLp
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K : Nat) (k : Finset.range K) :
    MemLp (prespecifiedBatchRowCenteredFinalObservedInformation theta h b K k)
      2 (exactConcretePredeterminedBatchRowMeasure theta b k.1) := by
  letI : IsProbabilityMeasure
      (exactConcretePredeterminedBatchRowMeasure theta b k.1) :=
    exactConcretePredeterminedBatchRowMeasure_isProbability theta b
      (le_of_lt hInterior) k.1
  refine MemLp.of_bound
    (measurable_of_finite
      (prespecifiedBatchRowCenteredFinalObservedInformation theta h b K k)).aestronglyMeasurable
    (prespecifiedBatchRowCenteredFinalEnvelope theta h K k) ?_
  exact Filter.Eventually.of_forall fun row => by
    rw [Real.norm_eq_abs]
    exact prespecifiedBatchRowCenteredFinalObservedInformation_abs_le
      theta h b hInterior K k row

theorem prespecifiedBatchRowCenteredFinalObservedInformation_variance_le
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K : Nat) (k : Finset.range K) :
    variance
      (prespecifiedBatchRowCenteredFinalObservedInformation theta h b K k)
      (exactConcretePredeterminedBatchRowMeasure theta b k.1) <=
        prespecifiedBatchRowCenteredFinalEnvelope theta h K k ^ 2 := by
  letI : IsProbabilityMeasure
      (exactConcretePredeterminedBatchRowMeasure theta b k.1) :=
    exactConcretePredeterminedBatchRowMeasure_isProbability theta b
      (le_of_lt hInterior) k.1
  let B := prespecifiedBatchRowCenteredFinalEnvelope theta h K k
  have hIcc : ∀ᵐ row
      ∂exactConcretePredeterminedBatchRowMeasure theta b k.1,
      prespecifiedBatchRowCenteredFinalObservedInformation theta h b K k row ∈
        Set.Icc (-B) B := by
    exact Filter.Eventually.of_forall fun row => by
      have habs := prespecifiedBatchRowCenteredFinalObservedInformation_abs_le
        theta h b hInterior K k row
      have habs' :
          |prespecifiedBatchRowCenteredFinalObservedInformation theta h b K k row| <= B := by
        simpa [B] using habs
      exact (abs_le.mp habs')
  have hv := variance_le_sq_of_bounded hIcc
    (measurable_of_finite
      (prespecifiedBatchRowCenteredFinalObservedInformation theta h b K k)).aemeasurable
  simpa [B] using hv

/-! ## Exact finite-prefix algebra -/

theorem prespecifiedBatchCumulativeObservedInformation_eq_pilot_add_final
    (theta h b : RLSVector 3) (K : Nat)
    (x : PrespecifiedBatchFinitePrefix K) :
    prespecifiedBatchCumulativeObservedDirectionalInformation theta h b K x =
      prespecifiedBatchCumulativePilotObservedInformation theta h K x +
        prespecifiedBatchCumulativeFinalObservedDirectionalInformation
          theta h b K x := by
  unfold prespecifiedBatchCumulativeObservedDirectionalInformation
    prespecifiedBatchCumulativePilotObservedInformation
    prespecifiedBatchCumulativeFinalObservedDirectionalInformation
    prespecifiedBatchFinalSize
  rw [Finset.sum_add_distrib]

theorem prespecifiedBatchCumulativeCenteredFinalObservedInformation_eq
    (theta h b : RLSVector 3) (K : Nat)
    (x : PrespecifiedBatchFinitePrefix K) :
    prespecifiedBatchCumulativeCenteredFinalObservedInformation theta h b K x =
      prespecifiedBatchCumulativeFinalObservedDirectionalInformation theta h b K x -
        prespecifiedBatchCumulativeFinalPredictableVariancePrefix theta h b K x := by
  unfold prespecifiedBatchCumulativeCenteredFinalObservedInformation
    prespecifiedBatchRowCenteredFinalObservedInformation
    prespecifiedBatchCumulativeFinalObservedDirectionalInformation
    prespecifiedBatchCumulativeFinalPredictableVariancePrefix
    mixedExactCycleCenteredObservedSquare
    mixedExactCycleNormalizedDirectionalFisher
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hscale (t : Fin (prespecifiedBatchFinalSize k.1)) :
      prespecifiedBatchFinalNormalizedScore theta h b K k (x k) t =
        prespecifiedBatchCumulativeShotScale K (prespecifiedBatchRangeFin k) *
          mixedExactCycleNormalizedDirectionalScore theta h
            (exactConcreteBatchSelectedFrame k.1 b) (x k).1 t (x k).2 := by
    exact prespecifiedBatchFinalNormalizedScore_eq_scaled_finitePrefix
      theta h b K k (x k) t
  simp_rw [hscale]
  have hfish :
      (∑ t : Fin (prespecifiedBatchFinalSize k.1),
        prespecifiedBatchCumulativeShotScale K (prespecifiedBatchRangeFin k) ^ 2 *
          mixedExactCycleOneShotNormalizedDirectionalFisher theta h
            (exactConcreteBatchSelectedFrame k.1 b) (x k).1 t) =
        prespecifiedBatchCumulativeShotScale K (prespecifiedBatchRangeFin k) ^ 2 *
          ∑ t : Fin (prespecifiedBatchFinalSize k.1),
            mixedExactCycleOneShotNormalizedDirectionalFisher theta h
              (exactConcreteBatchSelectedFrame k.1 b) (x k).1 t := by
    rw [Finset.mul_sum]
  rw [hfish]
  ring

/-- A complete exact cycle has normalized Fisher information equal to the
selected-frame per-observation Fisher value. -/
theorem mixedExactCycleNormalizedDirectionalFisher_eq_exactCumulativeBatchFrame
    (theta h b : RLSVector 3) (k : Nat)
    (pilot : PauliPilotPath (exactConcreteBatchPilotBlocks k)) :
    mixedExactCycleNormalizedDirectionalFisher theta h
        (r := exactConcreteBatchFinalBlocks k)
        (exactConcreteBatchSelectedFrame k b) pilot =
      exactCumulativeBatchFrameDirectionalInformation theta h b k pilot := by
  let r := exactConcreteBatchFinalBlocks k
  have hr : 0 < r := exactConcreteBatchFinalBlocks_pos k
  have hm : (3 * r : Real) ≠ 0 := by positivity
  have hraw :
      (∑ t : Fin (3 * r),
        mixedTwoStageFinalDirectionalFisherTerm theta h
          (exactConcreteBatchSelectedFrame k b) pilot t) =
        (3 * r : Real) *
          exactCumulativeBatchFrameDirectionalInformation theta h b k pilot := by
    rw [mixedTwoStageExactCycleInformation_sum]
    unfold mixedTwoStageFrameColumnDirectionalFisherTerm
    have hframe :
        (exactConcreteBatchSelectedFrame k b).frame pilot =
          mixedPilotSelectedLocalFrame b (pauliPilotEstimate pilot) := rfl
    rw [hframe]
    unfold exactCumulativeBatchFrameDirectionalInformation
      mixedPolynomialFrameDirectionalInformation
    ring
  unfold mixedExactCycleNormalizedDirectionalFisher
  have hone (t : Fin (3 * r)) :
      mixedExactCycleOneShotNormalizedDirectionalFisher theta h
          (exactConcreteBatchSelectedFrame k b) pilot t =
        mixedTwoStageFinalDirectionalFisherTerm theta h
          (exactConcreteBatchSelectedFrame k b) pilot t / (3 * r : Real) := by
    unfold mixedExactCycleOneShotNormalizedDirectionalFisher
      mixedTwoStageFinalDirectionalFisherTerm
    norm_num [Nat.cast_mul]
  simp_rw [hone]
  rw [← Finset.sum_div]
  rw [hraw]
  field_simp [hm]

/-- Prefix predictable variance is the cumulative conditional-variance sum,
pulled back along the arbitrary finite-prefix extension. -/
theorem prespecifiedBatchCumulativeFinalPredictableVariancePrefix_eq_conditionalVariance
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K : Nat) (x : PrespecifiedBatchFinitePrefix K) :
    prespecifiedBatchCumulativeFinalPredictableVariancePrefix theta h b K x =
      ∑ t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
        prespecifiedBatchCumulativeConditionalVariance theta h b K t
          (prespecifiedBatchExtendPrefix x) := by
  classical
  rw [prespecifiedBatchCumulativeConditionalVariance_sum_eq_batched]
  unfold prespecifiedBatchCumulativeFinalPredictableVariancePrefix
    batchedPredictableScalarAverage
  simp_rw [prespecifiedBatchCumulativeShotScale, prespecifiedBatchSampleScale,
    prespecifiedBatchTotalObservations_eq_cumulativeCount]
  simp only [cumulativeCount]
  let F : Finset.range K -> Real := fun k =>
    (Real.sqrt (3 * exactConcreteBatchFinalBlocks
        (prespecifiedBatchRangeFin k) : Nat) /
      Real.sqrt (∑ i ∈ Finset.range K, exactConcreteBatchSize i : Nat)) ^ 2 *
      mixedExactCycleNormalizedDirectionalFisher theta h
        (r := exactConcreteBatchFinalBlocks k.1)
        (exactConcreteBatchSelectedFrame k.1 b) (x k).1
  let G : Nat -> Real := fun k =>
    (Real.sqrt (3 * exactConcreteBatchFinalBlocks k : Nat) /
      Real.sqrt (∑ i ∈ Finset.range K, exactConcreteBatchSize i : Nat)) ^ 2 *
      mixedExactCycleNormalizedDirectionalFisher theta h
        (r := exactConcreteBatchFinalBlocks k)
        (exactConcreteBatchSelectedFrame k b)
        (prespecifiedBatchExtendPrefix x k).1
  change (∑ k : Finset.range K, F k) = _
  rw [show (∑ k : Finset.range K, F k) =
      ∑ k ∈ Finset.range K, G k by
    calc
      (∑ k : Finset.range K, F k) =
          ∑ k : Finset.range K, G k.1 := by
        apply Finset.sum_congr rfl
        intro k _
        simp [F, G, prespecifiedBatchRangeFin,
          prespecifiedBatchExtendPrefix, Finset.mem_range.mp k.2]
      _ = ∑ k ∈ Finset.range K, G k := by
        change ∑ k ∈ (Finset.univ : Finset (Finset.range K)), G k.1 = _
        rw [show (Finset.univ : Finset (Finset.range K)) =
            (Finset.range K).attach by
          exact Finset.univ_eq_attach (Finset.range K)]
        exact Finset.sum_attach _ _]
  rw [Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  have hsub : exactConcreteBatchSize k - exactConcreteBatchExplorationSize k =
      prespecifiedBatchFinalSize k := by
    rw [exactConcreteBatchSize_decompose]
    simp [prespecifiedBatchFinalSize]
  have hm : 0 < prespecifiedBatchFinalSize k := by
    exact Nat.mul_pos (by norm_num) (exactConcreteBatchFinalBlocks_pos k)
  have hN : 0 < cumulativeCount exactConcreteBatchSize K := by
    rw [exactConcreteBatchSize_cumulative]
    have hK : 0 < K := lt_of_le_of_lt (Nat.zero_le k) (Finset.mem_range.mp hk)
    positivity
  have hmSq : Real.sqrt (prespecifiedBatchFinalSize k : Real) ^ 2 =
      (prespecifiedBatchFinalSize k : Real) := Real.sq_sqrt (by positivity)
  have hNSq : Real.sqrt (cumulativeCount exactConcreteBatchSize K : Real) ^ 2 =
      (cumulativeCount exactConcreteBatchSize K : Real) := Real.sq_sqrt (by positivity)
  rw [batchAllocation_identity _ _ _ _ (exactConcreteBatchExplorationSize_le k),
    hsub]
  let ksub : Finset.range K := ⟨k, hk⟩
  have hext : prespecifiedBatchExtendPrefix x k = x ksub := by
    exact prespecifiedBatchExtendPrefix_apply x ksub
  have hG : G k =
      (Real.sqrt (prespecifiedBatchFinalSize k : Real) /
        Real.sqrt (cumulativeCount exactConcreteBatchSize K : Real)) ^ 2 *
        exactCumulativeBatchFrameDirectionalInformation theta h b k (x ksub).1 := by
    unfold G
    rw [hext]
    rw [mixedExactCycleNormalizedDirectionalFisher_eq_exactCumulativeBatchFrame]
    rfl
  rw [hG]
  have hcount :
      (∑ i ∈ Finset.range K, (exactConcreteBatchSize i : Real)) =
        (cumulativeCount exactConcreteBatchSize K : Real) := by
    unfold cumulativeCount
    push_cast
    rfl
  rw [div_pow, hmSq, hNSq, hext, hcount]
  field_simp [show (prespecifiedBatchFinalSize k : Real) ≠ 0 by
    exact_mod_cast Nat.ne_of_gt hm,
    show (cumulativeCount exactConcreteBatchSize K : Real) ≠ 0 by
      exact_mod_cast Nat.ne_of_gt hN]
  ring

theorem prespecifiedBatchCumulativeCenteredFinalObservedInformation_exact_endpoint
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K : Nat) (x : PrespecifiedBatchFinitePrefix K) :
    prespecifiedBatchCumulativeCenteredFinalObservedInformation theta h b K x =
      (prespecifiedBatchCumulativeObservedDirectionalInformation theta h b K x -
        prespecifiedBatchCumulativePilotObservedInformation theta h K x) -
      ∑ t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
        prespecifiedBatchCumulativeConditionalVariance theta h b K t
          (prespecifiedBatchExtendPrefix x) := by
  rw [prespecifiedBatchCumulativeCenteredFinalObservedInformation_eq,
    prespecifiedBatchCumulativeFinalPredictableVariancePrefix_eq_conditionalVariance
      theta h b hInterior]
  rw [prespecifiedBatchCumulativeObservedInformation_eq_pilot_add_final]
  ring

/-! ## Independent-row variance and `O(1/K)` closure -/

/-- Sum of the sharp squared row envelopes. -/
def prespecifiedBatchFinalObservedInformationVarianceEnvelope
    (theta h : RLSVector 3) (K : Nat) : Real :=
  ∑ k : Finset.range K,
    prespecifiedBatchRowCenteredFinalEnvelope theta h K k ^ 2

theorem prespecifiedBatchCumulativeCenteredFinalObservedInformation_memLp
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K : Nat) :
    MemLp (prespecifiedBatchCumulativeCenteredFinalObservedInformation
      theta h b K) 2 (prespecifiedBatchPrefixMeasure theta b K) := by
  let rowMeasure : (k : Finset.range K) ->
      Measure (ExactConcretePredeterminedBatchRow k.1) :=
    fun k => exactConcretePredeterminedBatchRowMeasure theta b k.1
  let Xrow : (k : Finset.range K) ->
      ExactConcretePredeterminedBatchRow k.1 -> Real :=
    fun k => prespecifiedBatchRowCenteredFinalObservedInformation theta h b K k
  letI : forall k : Finset.range K, IsProbabilityMeasure (rowMeasure k) :=
    fun k => exactConcretePredeterminedBatchRowMeasure_isProbability theta b
      (le_of_lt hInterior) k.1
  have hmem : forall k, MemLp (Xrow k) 2 (rowMeasure k) :=
    fun k => prespecifiedBatchRowCenteredFinalObservedInformation_memLp
      theta h b hInterior K k
  have hcomp : forall k, MemLp
      (fun x : PrespecifiedBatchFinitePrefix K => Xrow k (x k)) 2
      (Measure.pi rowMeasure) :=
    fun k => (hmem k).comp_measurePreserving (measurePreserving_eval rowMeasure k)
  have hsum := memLp_finsetSum (p := (2 : ENNReal))
    (μ := Measure.pi rowMeasure) (Finset.univ : Finset (Finset.range K))
    (fun k _ => hcomp k)
  simpa [prespecifiedBatchPrefixMeasure,
    prespecifiedBatchCumulativeCenteredFinalObservedInformation,
    rowMeasure, Xrow] using hsum

theorem prespecifiedBatchCumulativeCenteredFinalObservedInformation_integral_zero
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K : Nat) :
    (∫ x, prespecifiedBatchCumulativeCenteredFinalObservedInformation
      theta h b K x ∂prespecifiedBatchPrefixMeasure theta b K) = 0 := by
  let rowMeasure : (k : Finset.range K) ->
      Measure (ExactConcretePredeterminedBatchRow k.1) :=
    fun k => exactConcretePredeterminedBatchRowMeasure theta b k.1
  let Xrow : (k : Finset.range K) ->
      ExactConcretePredeterminedBatchRow k.1 -> Real :=
    fun k => prespecifiedBatchRowCenteredFinalObservedInformation theta h b K k
  letI : forall k : Finset.range K, IsProbabilityMeasure (rowMeasure k) :=
    fun k => exactConcretePredeterminedBatchRowMeasure_isProbability theta b
      (le_of_lt hInterior) k.1
  have hmem : forall k, MemLp (Xrow k) 2 (rowMeasure k) :=
    fun k => prespecifiedBatchRowCenteredFinalObservedInformation_memLp
      theta h b hInterior K k
  have hcomp : forall k, Integrable
      (fun x : PrespecifiedBatchFinitePrefix K => Xrow k (x k))
      (Measure.pi rowMeasure) := fun k =>
    ((hmem k).comp_measurePreserving
      (measurePreserving_eval rowMeasure k)).integrable (by norm_num)
  change (∫ x, ∑ k : Finset.range K, Xrow k (x k)
      ∂Measure.pi rowMeasure) = 0
  calc
    (∫ x, ∑ k : Finset.range K, Xrow k (x k)
        ∂Measure.pi rowMeasure) =
        ∑ k : Finset.range K,
          ∫ x, Xrow k (x k) ∂Measure.pi rowMeasure := by
      have hsum := integral_finsetSum
        (μ := Measure.pi rowMeasure)
        (Finset.univ : Finset (Finset.range K))
        (fun k _ => hcomp k)
      simpa using hsum
    _ = ∑ k : Finset.range K,
        ∫ row, Xrow k row ∂rowMeasure k := by
      apply Finset.sum_congr rfl
      intro k _
      exact integral_comp_eval (hmem k).aestronglyMeasurable
    _ = 0 := by
      simp [Xrow, rowMeasure,
        prespecifiedBatchRowCenteredFinalObservedInformation_integral_zero
          theta h b hInterior]

theorem prespecifiedBatchCumulativeCenteredFinalObservedInformation_variance_le
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K : Nat) :
    variance (prespecifiedBatchCumulativeCenteredFinalObservedInformation
      theta h b K) (prespecifiedBatchPrefixMeasure theta b K) <=
      prespecifiedBatchFinalObservedInformationVarianceEnvelope theta h K := by
  let rowMeasure : (k : Finset.range K) ->
      Measure (ExactConcretePredeterminedBatchRow k.1) :=
    fun k => exactConcretePredeterminedBatchRowMeasure theta b k.1
  let Xrow : (k : Finset.range K) ->
      ExactConcretePredeterminedBatchRow k.1 -> Real :=
    fun k => prespecifiedBatchRowCenteredFinalObservedInformation theta h b K k
  letI : forall k : Finset.range K, IsProbabilityMeasure (rowMeasure k) :=
    fun k => exactConcretePredeterminedBatchRowMeasure_isProbability theta b
      (le_of_lt hInterior) k.1
  have hmem : forall k, MemLp (Xrow k) 2 (rowMeasure k) :=
    fun k => prespecifiedBatchRowCenteredFinalObservedInformation_memLp
      theta h b hInterior K k
  have hv : variance (fun x : PrespecifiedBatchFinitePrefix K =>
      ∑ k : Finset.range K, Xrow k (x k)) (Measure.pi rowMeasure) =
      ∑ k : Finset.range K, variance (Xrow k) (rowMeasure k) := by
    rw [show (fun x : PrespecifiedBatchFinitePrefix K =>
        ∑ k : Finset.range K, Xrow k (x k)) =
        ∑ k : Finset.range K,
          (fun x : PrespecifiedBatchFinitePrefix K => Xrow k (x k)) by
      funext x
      simp]
    exact variance_sum_pi (μ := rowMeasure) hmem
  rw [show prespecifiedBatchPrefixMeasure theta b K = Measure.pi rowMeasure by rfl]
  rw [show prespecifiedBatchCumulativeCenteredFinalObservedInformation
      theta h b K = fun x => ∑ k : Finset.range K, Xrow k (x k) by rfl,
    hv]
  unfold prespecifiedBatchFinalObservedInformationVarianceEnvelope
  exact Finset.sum_le_sum fun k _ =>
    prespecifiedBatchRowCenteredFinalObservedInformation_variance_le
      theta h b hInterior K k

/-- The deterministic squared final-batch fractions are bounded by the
largest complete-batch fraction. -/
theorem prespecifiedBatchFinalSizeSquareFractionSum_le_largestBatchFraction
    (K : Nat) (hK : 0 < K) :
    (∑ k : Finset.range K,
      ((prespecifiedBatchFinalSize k.1 : Nat) : Real) ^ 2 /
        (prespecifiedBatchTotalObservations K : Real) ^ 2) <=
      (largestBatchBefore exactConcreteBatchSize K : Real) /
        (prespecifiedBatchTotalObservations K : Real) := by
  let L := largestBatchBefore exactConcreteBatchSize K
  let N := prespecifiedBatchTotalObservations K
  have hN : 0 < N := prespecifiedBatchTotalObservations_pos K hK
  have hsumFinal :
      (∑ k : Finset.range K, prespecifiedBatchFinalSize k.1) <= N := by
    have hterm : forall k : Finset.range K,
        prespecifiedBatchFinalSize k.1 <= exactConcreteBatchSize k.1 := by
      intro k
      rw [exactConcreteBatchSize_decompose]
      simp [prespecifiedBatchFinalSize]
    have hs := Finset.sum_le_sum fun k (_ : k ∈ (Finset.univ : Finset (Finset.range K))) =>
      hterm k
    have htotal : (∑ k : Finset.range K, exactConcreteBatchSize k.1) = N := by
      unfold N prespecifiedBatchTotalObservations cumulativeCount
      rw [show (Finset.univ : Finset (Finset.range K)) =
          (Finset.range K).attach by exact Finset.univ_eq_attach (Finset.range K)]
      exact Finset.sum_attach _ _
    exact hs.trans_eq htotal
  have htermSq : forall k : Finset.range K,
      ((prespecifiedBatchFinalSize k.1 : Nat) : Real) ^ 2 <=
        (L : Real) * (prespecifiedBatchFinalSize k.1 : Real) := by
    intro k
    have hmBatch : prespecifiedBatchFinalSize k.1 <= exactConcreteBatchSize k.1 := by
      rw [exactConcreteBatchSize_decompose]
      simp [prespecifiedBatchFinalSize]
    have hBatchL : exactConcreteBatchSize k.1 <= L := by
      unfold L largestBatchBefore
      exact Finset.le_sup (Finset.mem_range.mpr (Finset.mem_range.mp k.2))
    have hmL : (prespecifiedBatchFinalSize k.1 : Real) <= (L : Real) := by
      exact_mod_cast hmBatch.trans hBatchL
    calc
      ((prespecifiedBatchFinalSize k.1 : Nat) : Real) ^ 2 =
          (prespecifiedBatchFinalSize k.1 : Real) *
            (prespecifiedBatchFinalSize k.1 : Real) := by ring
      _ <= (L : Real) * (prespecifiedBatchFinalSize k.1 : Real) :=
        mul_le_mul_of_nonneg_right hmL (by positivity)
  have hsumSq :
      (∑ k : Finset.range K,
        ((prespecifiedBatchFinalSize k.1 : Nat) : Real) ^ 2) <=
        (L : Real) * (N : Real) := by
    calc
      _ <= ∑ k : Finset.range K,
          (L : Real) * (prespecifiedBatchFinalSize k.1 : Real) :=
        Finset.sum_le_sum fun k _ => htermSq k
      _ = (L : Real) *
          ∑ k : Finset.range K, (prespecifiedBatchFinalSize k.1 : Real) := by
        rw [Finset.mul_sum]
      _ <= (L : Real) * (N : Real) := by
        gcongr
        exact_mod_cast hsumFinal
  unfold L N at *
  rw [← Finset.sum_div]
  rw [div_le_div_iff₀ (by positivity : (0 : Real) <
      (prespecifiedBatchTotalObservations K : Real) ^ 2)
    (by positivity : (0 : Real) < prespecifiedBatchTotalObservations K)]
  calc
    (∑ k : Finset.range K,
        ((prespecifiedBatchFinalSize k.1 : Nat) : Real) ^ 2) *
        (prespecifiedBatchTotalObservations K : Real) <=
      ((largestBatchBefore exactConcreteBatchSize K : Real) *
        (prespecifiedBatchTotalObservations K : Real)) *
        (prespecifiedBatchTotalObservations K : Real) := by gcongr
    _ = (largestBatchBefore exactConcreteBatchSize K : Real) *
        (prespecifiedBatchTotalObservations K : Real) ^ 2 := by ring

theorem prespecifiedBatchFinalSizeSquareFractionSum_tendsto_zero :
    Tendsto (fun K : Nat =>
      ∑ k : Finset.range K,
        ((prespecifiedBatchFinalSize k.1 : Nat) : Real) ^ 2 /
          (prespecifiedBatchTotalObservations K : Real) ^ 2)
      atTop (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards with K
    positivity
  · filter_upwards [eventually_gt_atTop (0 : Nat)] with K hK
    exact prespecifiedBatchFinalSizeSquareFractionSum_le_largestBatchFraction K hK
  · simpa [prespecifiedBatchTotalObservations] using
      exactConcreteBatch_largestBatchFraction_tendsto_zero

theorem prespecifiedBatchFinalObservedInformationVarianceEnvelope_tendsto_zero
    (theta h : RLSVector 3) :
    Tendsto (prespecifiedBatchFinalObservedInformationVarianceEnvelope theta h)
      atTop (nhds 0) := by
  have hs := prespecifiedBatchFinalSizeSquareFractionSum_tendsto_zero
  have hc0 := (tendsto_const_nhds : Tendsto
    (fun _ : Nat => 4 * mixedProjectedScoreEnvelope theta h ^ 4)
    atTop (nhds (4 * mixedProjectedScoreEnvelope theta h ^ 4))).mul hs
  have hc : Tendsto (fun K : Nat =>
      4 * mixedProjectedScoreEnvelope theta h ^ 4 *
        ∑ k : Finset.range K,
          ((prespecifiedBatchFinalSize k.1 : Nat) : Real) ^ 2 /
            (prespecifiedBatchTotalObservations K : Real) ^ 2)
      atTop (nhds 0) := by
    simpa using hc0
  convert hc using 1
  funext K
  unfold prespecifiedBatchFinalObservedInformationVarianceEnvelope
    prespecifiedBatchRowCenteredFinalEnvelope
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Chebyshev bound for the exact finite-prefix final observed-information
innovation. -/
theorem prespecifiedBatchCumulativeCenteredFinalObservedInformation_tail_bound
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (K : Nat) :
    prespecifiedBatchPrefixMeasure theta b K
      {x : PrespecifiedBatchFinitePrefix K |
        epsilon <=
          |prespecifiedBatchCumulativeCenteredFinalObservedInformation
            theta h b K x|} <=
      ENNReal.ofReal
        (prespecifiedBatchFinalObservedInformationVarianceEnvelope theta h K /
          epsilon ^ 2) := by
  letI : IsProbabilityMeasure (prespecifiedBatchPrefixMeasure theta b K) :=
    prespecifiedBatchPrefixMeasure_isProbability theta b (le_of_lt hInterior) K
  have hmem := prespecifiedBatchCumulativeCenteredFinalObservedInformation_memLp
    theta h b hInterior K
  have hmean :=
    prespecifiedBatchCumulativeCenteredFinalObservedInformation_integral_zero
      theta h b hInterior K
  have hcheb := meas_ge_le_variance_div_sq hmem hepsilon
  have hcheb' :
      prespecifiedBatchPrefixMeasure theta b K
        {x : PrespecifiedBatchFinitePrefix K |
          epsilon <=
            |prespecifiedBatchCumulativeCenteredFinalObservedInformation
              theta h b K x|} <=
        ENNReal.ofReal
          (variance (prespecifiedBatchCumulativeCenteredFinalObservedInformation
            theta h b K) (prespecifiedBatchPrefixMeasure theta b K) /
              epsilon ^ 2) := by
    simpa only [hmean, sub_zero] using hcheb
  exact hcheb'.trans (ENNReal.ofReal_le_ofReal
    (div_le_div_of_nonneg_right
      (prespecifiedBatchCumulativeCenteredFinalObservedInformation_variance_le
        theta h b hInterior K) (sq_nonneg epsilon)))

/-- Exact deviation-event convergence required by the finite-prefix LAN
remainder: final observed information minus predictable final Fisher tends to
zero in probability. -/
theorem prespecifiedBatchCumulativeFinalObservedInformation_sub_predictable_convergesInProbability
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1) :
    forall epsilon : Real, 0 < epsilon ->
      Tendsto
        (fun K : Nat =>
          prespecifiedBatchPrefixMeasure theta b K
            {x : PrespecifiedBatchFinitePrefix K |
              epsilon <=
                |prespecifiedBatchCumulativeFinalObservedDirectionalInformation
                    theta h b K x -
                  prespecifiedBatchCumulativeFinalPredictableVariancePrefix
                    theta h b K x|})
        atTop (nhds 0) := by
  intro epsilon hepsilon
  have hreal : Tendsto
      (fun K => prespecifiedBatchFinalObservedInformationVarianceEnvelope theta h K /
        epsilon ^ 2) atTop (nhds 0) :=
    by simpa using
      (prespecifiedBatchFinalObservedInformationVarianceEnvelope_tendsto_zero
        theta h).div_const (epsilon ^ 2)
  have hENN : Tendsto
      (fun K => ENNReal.ofReal
        (prespecifiedBatchFinalObservedInformationVarianceEnvelope theta h K /
          epsilon ^ 2)) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hreal
  apply Tendsto.squeeze' tendsto_const_nhds hENN
  · exact Filter.Eventually.of_forall fun _ => bot_le
  · filter_upwards with K
    simpa only [prespecifiedBatchCumulativeCenteredFinalObservedInformation_eq]
      using prespecifiedBatchCumulativeCenteredFinalObservedInformation_tail_bound
        theta h b hInterior epsilon hepsilon K

/-- The same convergence stated at the exact LAN endpoint: full observed
information minus negligible pilot information minus pulled-back predictable
conditional variance. -/
theorem prespecifiedBatchObservedInformationLANDeviationEvent_tendsto_zero
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1) :
    forall epsilon : Real, 0 < epsilon ->
      Tendsto
        (fun K : Nat =>
          prespecifiedBatchPrefixMeasure theta b K
            {x : PrespecifiedBatchFinitePrefix K |
              epsilon <=
                |(prespecifiedBatchCumulativeObservedDirectionalInformation
                    theta h b K x -
                  prespecifiedBatchCumulativePilotObservedInformation theta h K x) -
                  ∑ t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
                    prespecifiedBatchCumulativeConditionalVariance theta h b K t
                      (prespecifiedBatchExtendPrefix x)|})
        atTop (nhds 0) := by
  intro epsilon hepsilon
  have hconv :=
    prespecifiedBatchCumulativeFinalObservedInformation_sub_predictable_convergesInProbability
      theta h b hInterior epsilon hepsilon
  convert hconv using 1
  funext K
  congr 1
  ext x
  change
    epsilon <=
        |(prespecifiedBatchCumulativeObservedDirectionalInformation theta h b K x -
            prespecifiedBatchCumulativePilotObservedInformation theta h K x) -
          ∑ t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
            prespecifiedBatchCumulativeConditionalVariance theta h b K t
              (prespecifiedBatchExtendPrefix x)| ↔
      epsilon <=
        |prespecifiedBatchCumulativeFinalObservedDirectionalInformation theta h b K x -
          prespecifiedBatchCumulativeFinalPredictableVariancePrefix theta h b K x|
  rw [← prespecifiedBatchCumulativeCenteredFinalObservedInformation_exact_endpoint
    theta h b hInterior K x,
    prespecifiedBatchCumulativeCenteredFinalObservedInformation_eq]

/-! ## Uniform fourth moments for the cumulative final score -/

open SourceFaithfulMartingaleMoments

/-- The finite horizon-`K` final-score row, extended by zero to a sequence on
`Nat` as required by Hall--Heyde Theorem 2.12. -/
def prespecifiedBatchCumulativeExtendedIncrement
    (theta h b : RLSVector 3) (K n : Nat)
    (omega : ExactConcretePredeterminedBatchPath) : Real :=
  if hn : n < prespecifiedBatchCumulativeFinalRowLength K then
    prespecifiedBatchCumulativeEnumeratedIncrement theta h b K ⟨n, hn⟩ omega
  else 0

theorem prespecifiedBatchCumulativeExtendedIncrement_of_lt
    (theta h b : RLSVector 3) (K n : Nat)
    (hn : n < prespecifiedBatchCumulativeFinalRowLength K) :
    prespecifiedBatchCumulativeExtendedIncrement theta h b K n =
      prespecifiedBatchCumulativeEnumeratedIncrement theta h b K ⟨n, hn⟩ := by
  funext omega
  simp [prespecifiedBatchCumulativeExtendedIncrement, hn]

theorem prespecifiedBatchCumulativeExtendedIncrement_of_not_lt
    (theta h b : RLSVector 3) (K n : Nat)
    (hn : ¬ n < prespecifiedBatchCumulativeFinalRowLength K) :
    prespecifiedBatchCumulativeExtendedIncrement theta h b K n =
      (fun _ => (0 : Real)) := by
  funext omega
  simp [prespecifiedBatchCumulativeExtendedIncrement, hn]

theorem prespecifiedBatchCumulativeExtendedIncrement_measurable_succ
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K n : Nat) :
    Measurable[(globalFinalFiltration theta h b hInterior).seq (n + 1)]
      (prespecifiedBatchCumulativeExtendedIncrement theta h b K n) := by
  by_cases hn : n < prespecifiedBatchCumulativeFinalRowLength K
  · rw [prespecifiedBatchCumulativeExtendedIncrement_of_lt theta h b K n hn]
    exact cumulativeIncrement_measurable_succ theta h b hInterior K ⟨n, hn⟩
  · rw [prespecifiedBatchCumulativeExtendedIncrement_of_not_lt theta h b K n hn]
    exact measurable_const

theorem prespecifiedBatchCumulativeExtendedIncrement_integrable
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K n : Nat) :
    Integrable (prespecifiedBatchCumulativeExtendedIncrement theta h b K n)
      (exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior)) := by
  letI : IsProbabilityMeasure
      (exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior)) :=
    exactConcretePredeterminedBatchPathMeasure_isProbability
      theta b (le_of_lt hInterior)
  by_cases hn : n < prespecifiedBatchCumulativeFinalRowLength K
  · rw [prespecifiedBatchCumulativeExtendedIncrement_of_lt theta h b K n hn]
    exact
      cumulativeIncrement_integrable theta h b hInterior K ⟨n, hn⟩
  · rw [prespecifiedBatchCumulativeExtendedIncrement_of_not_lt theta h b K n hn]
    exact integrable_const 0

theorem prespecifiedBatchCumulativeExtendedIncrement_condExp_zero
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K n : Nat) :
    (exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior))[
      prespecifiedBatchCumulativeExtendedIncrement theta h b K n |
        globalFinalFiltrationSigma theta h b hInterior n] =ᵐ[
          exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior)]
      (fun _ => (0 : Real)) := by
  by_cases hn : n < prespecifiedBatchCumulativeFinalRowLength K
  · rw [prespecifiedBatchCumulativeExtendedIncrement_of_lt theta h b K n hn]
    exact
      cumulativeIncrement_condExp_zero theta h b hInterior K ⟨n, hn⟩
  · rw [prespecifiedBatchCumulativeExtendedIncrement_of_not_lt theta h b K n hn]
    simp

/-- The zero-extended cumulative score has martingale partial sums under the
completed batch-major filtration. -/
theorem prespecifiedBatchCumulativeExtendedPartialSum_martingale
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1) (K : Nat) :
    Martingale
      (scalarPartialSum
        (prespecifiedBatchCumulativeExtendedIncrement theta h b K))
      (globalFinalFiltration theta h b hInterior)
      (exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior)) := by
  letI : IsProbabilityMeasure
      (exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior)) :=
    exactConcretePredeterminedBatchPathMeasure_isProbability
      theta b (le_of_lt hInterior)
  apply martingale_of_condExp_sub_eq_zero_nat
  · intro n
    apply Measurable.stronglyMeasurable
    unfold scalarPartialSum
    apply Finset.measurable_sum
    intro k hk
    have hkn : k + 1 <= n := Nat.succ_le_iff.mpr (Finset.mem_range.mp hk)
    exact (prespecifiedBatchCumulativeExtendedIncrement_measurable_succ
      theta h b hInterior K k).mono
        ((globalFinalFiltration theta h b hInterior).mono hkn) le_rfl
  · intro n
    unfold scalarPartialSum
    exact integrable_finset_sum _ fun k _ =>
      prespecifiedBatchCumulativeExtendedIncrement_integrable
        theta h b hInterior K k
  · intro n
    have hdiff :
        (fun omega =>
          scalarPartialSum
              (prespecifiedBatchCumulativeExtendedIncrement theta h b K)
              (n + 1) omega -
            scalarPartialSum
              (prespecifiedBatchCumulativeExtendedIncrement theta h b K)
              n omega) =
          prespecifiedBatchCumulativeExtendedIncrement theta h b K n := by
      funext omega
      simp [scalarPartialSum, Finset.sum_range_succ]
    change
      (exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior))[
        (fun omega =>
          scalarPartialSum
              (prespecifiedBatchCumulativeExtendedIncrement theta h b K)
              (n + 1) omega -
            scalarPartialSum
              (prespecifiedBatchCumulativeExtendedIncrement theta h b K)
              n omega) |
        globalFinalFiltrationSigma theta h b hInterior n] =ᵐ[
          exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior)]
        (fun _ => (0 : Real))
    rw [hdiff]
    exact prespecifiedBatchCumulativeExtendedIncrement_condExp_zero
      theta h b hInterior K n

/-- At the finite terminal index, the zero-extended partial sum is exactly the
enumerated cumulative final score. -/
theorem prespecifiedBatchCumulativeExtendedPartialSum_terminal
    (theta h b : RLSVector 3) (K : Nat)
    (omega : ExactConcretePredeterminedBatchPath) :
    scalarPartialSum
        (prespecifiedBatchCumulativeExtendedIncrement theta h b K)
        (prespecifiedBatchCumulativeFinalRowLength K) omega =
      hallHeydeDeterministicVarianceRowSum
        prespecifiedBatchCumulativeFinalRowLength
        (prespecifiedBatchCumulativeEnumeratedIncrement theta h b) K omega := by
  unfold scalarPartialSum hallHeydeDeterministicVarianceRowSum
  symm
  calc
    (∑ k : Fin (prespecifiedBatchCumulativeFinalRowLength K),
        prespecifiedBatchCumulativeEnumeratedIncrement theta h b K k omega) =
      ∑ k : Fin (prespecifiedBatchCumulativeFinalRowLength K),
        prespecifiedBatchCumulativeExtendedIncrement theta h b K k.val omega := by
          apply Finset.sum_congr rfl
          intro k _
          rw [prespecifiedBatchCumulativeExtendedIncrement_of_lt theta h b K k.val k.isLt]
    _ = ∑ k ∈ Finset.range (prespecifiedBatchCumulativeFinalRowLength K),
        prespecifiedBatchCumulativeExtendedIncrement theta h b K k omega :=
      Fin.sum_univ_eq_sum_range
        (fun n => prespecifiedBatchCumulativeExtendedIncrement theta h b K n omega)
        (prespecifiedBatchCumulativeFinalRowLength K)

/-- Fixed interior directional-information envelope. -/
def prespecifiedBatchDirectionalInformationEnvelope
    (theta h : RLSVector 3) : Real :=
  QubitOracle.blochNormSq h / exactConcreteMixedInformationGap theta

/-- The completed final-shot predictable variance is nonnegative and bounded
uniformly in the horizon by the fixed interior Fisher envelope. -/
theorem prespecifiedBatchCumulativeConditionalVariance_nonnegative_and_le
    (theta h b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (K : Nat) (omega : ExactConcretePredeterminedBatchPath) :
    0 <= ∑ t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
        prespecifiedBatchCumulativeConditionalVariance theta h b K t omega ∧
      (∑ t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
        prespecifiedBatchCumulativeConditionalVariance theta h b K t omega) <=
        prespecifiedBatchDirectionalInformationEnvelope theta h := by
  rw [prespecifiedBatchCumulativeConditionalVariance_sum_eq_batched]
  unfold batchedPredictableScalarAverage
    prespecifiedBatchDirectionalInformationEnvelope
  let C := QubitOracle.blochNormSq h / exactConcreteMixedInformationGap theta
  let N := ∑ k ∈ Finset.range K, (exactConcreteBatchSize k : Real)
  have hC : 0 <= C := by
    exact div_nonneg (by
      unfold QubitOracle.blochNormSq
      positivity) (exactConcreteMixedInformationGap_pos theta hTruth).le
  have hterm (k : Nat) (hk : k ∈ Finset.range K) :
      0 <=
          (exactConcreteBatchSize k : Real) *
              exactCumulativeBatchFrameDirectionalInformation
                theta h b k (omega k).1 +
            (exactConcreteBatchExplorationSize k : Real) *
              (0 - exactCumulativeBatchFrameDirectionalInformation
                theta h b k (omega k).1) ∧
        (exactConcreteBatchSize k : Real) *
              exactCumulativeBatchFrameDirectionalInformation
                theta h b k (omega k).1 +
            (exactConcreteBatchExplorationSize k : Real) *
              (0 - exactCumulativeBatchFrameDirectionalInformation
                theta h b k (omega k).1) <=
          (exactConcreteBatchSize k : Real) * C := by
    have hI := exactCumulativeBatchFrameDirectionalInformation_nonnegative_and_le
      theta h b hTruth k (omega k).1
    rw [batchAllocation_identity _ _ _ _
      (exactConcreteBatchExplorationSize_le k)]
    simp only [mul_zero, add_zero]
    constructor
    · exact mul_nonneg (by positivity) hI.1
    · calc
        ((exactConcreteBatchSize k - exactConcreteBatchExplorationSize k : Nat) : Real) *
            exactCumulativeBatchFrameDirectionalInformation
              theta h b k (omega k).1 <=
          ((exactConcreteBatchSize k - exactConcreteBatchExplorationSize k : Nat) : Real) * C :=
            mul_le_mul_of_nonneg_left hI.2 (by positivity)
        _ <= (exactConcreteBatchSize k : Real) * C := by
          exact mul_le_mul_of_nonneg_right (by
            exact_mod_cast Nat.sub_le (exactConcreteBatchSize k)
              (exactConcreteBatchExplorationSize k)) hC
  have hsumNonneg : 0 <=
      ∑ k ∈ Finset.range K,
        ((exactConcreteBatchSize k : Real) *
            exactCumulativeBatchFrameDirectionalInformation
              theta h b k (omega k).1 +
          (exactConcreteBatchExplorationSize k : Real) *
            (0 - exactCumulativeBatchFrameDirectionalInformation
              theta h b k (omega k).1)) :=
    Finset.sum_nonneg fun k hk => (hterm k hk).1
  have hsumLe :
      (∑ k ∈ Finset.range K,
        ((exactConcreteBatchSize k : Real) *
            exactCumulativeBatchFrameDirectionalInformation
              theta h b k (omega k).1 +
          (exactConcreteBatchExplorationSize k : Real) *
            (0 - exactCumulativeBatchFrameDirectionalInformation
              theta h b k (omega k).1))) <= N * C := by
    calc
      _ <= ∑ k ∈ Finset.range K, (exactConcreteBatchSize k : Real) * C :=
        Finset.sum_le_sum fun k hk => (hterm k hk).2
      _ = N * C := by unfold N; rw [Finset.sum_mul]
  constructor
  · exact mul_nonneg
      (inv_nonneg.mpr (Finset.sum_nonneg fun k _ => Nat.cast_nonneg _))
      hsumNonneg
  · by_cases hK : K = 0
    · subst K
      simp [N, C, hC]
    · have hN : 0 < N := by
        unfold N
        have hzero : 0 ∈ Finset.range K := Finset.mem_range.mpr (Nat.pos_of_ne_zero hK)
        exact lt_of_lt_of_le (by
          exact_mod_cast exactConcreteBatchSize_pos 0)
          (Finset.single_le_sum (fun k _ => Nat.cast_nonneg (exactConcreteBatchSize k)) hzero)
      rw [inv_mul_le_iff₀ hN]
      simpa [mul_comm] using hsumLe

/-- Predictable variance associated with the zero-extended increment. -/
def prespecifiedBatchCumulativeExtendedConditionalVariance
    (theta h b : RLSVector 3) (K n : Nat)
    (omega : ExactConcretePredeterminedBatchPath) : Real :=
  if hn : n < prespecifiedBatchCumulativeFinalRowLength K then
    prespecifiedBatchCumulativeConditionalVariance theta h b K ⟨n, hn⟩ omega
  else 0

theorem prespecifiedBatchCumulativeExtendedConditionalVariance_of_lt
    (theta h b : RLSVector 3) (K n : Nat)
    (hn : n < prespecifiedBatchCumulativeFinalRowLength K) :
    prespecifiedBatchCumulativeExtendedConditionalVariance theta h b K n =
      prespecifiedBatchCumulativeConditionalVariance theta h b K ⟨n, hn⟩ := by
  funext omega
  simp [prespecifiedBatchCumulativeExtendedConditionalVariance, hn]

theorem prespecifiedBatchCumulativeExtendedConditionalVariance_of_not_lt
    (theta h b : RLSVector 3) (K n : Nat)
    (hn : ¬ n < prespecifiedBatchCumulativeFinalRowLength K) :
    prespecifiedBatchCumulativeExtendedConditionalVariance theta h b K n =
      (fun _ => (0 : Real)) := by
  funext omega
  simp [prespecifiedBatchCumulativeExtendedConditionalVariance, hn]

/-- Exact conditional square for every member of the zero-extended row. -/
theorem prespecifiedBatchCumulativeExtendedIncrement_square_condExp
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K n : Nat) :
    (exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior))[
      (fun omega =>
        |prespecifiedBatchCumulativeExtendedIncrement theta h b K n omega| ^ 2) |
        globalFinalFiltrationSigma theta h b hInterior n] =ᵐ[
          exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior)]
      prespecifiedBatchCumulativeExtendedConditionalVariance theta h b K n := by
  by_cases hn : n < prespecifiedBatchCumulativeFinalRowLength K
  · rw [prespecifiedBatchCumulativeExtendedIncrement_of_lt theta h b K n hn,
      prespecifiedBatchCumulativeExtendedConditionalVariance_of_lt theta h b K n hn]
    simpa only [sq_abs] using
      cumulativeIncrement_square_condExp_eq_variance
        theta h b hInterior K ⟨n, hn⟩
  · rw [prespecifiedBatchCumulativeExtendedIncrement_of_not_lt theta h b K n hn,
      prespecifiedBatchCumulativeExtendedConditionalVariance_of_not_lt theta h b K n hn]
    simp

/-- At the terminal horizon, Hall--Heyde's predictable quadratic variation
is exactly the concrete cumulative adaptive Fisher sum. -/
theorem prespecifiedBatchCumulativeConditionalVarianceSum_terminal
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1) (K : Nat) :
    conditionalVarianceSum
        (exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior))
        (globalFinalFiltration theta h b hInterior)
        (prespecifiedBatchCumulativeExtendedIncrement theta h b K)
        (prespecifiedBatchCumulativeFinalRowLength K) =ᵐ[
          exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior)]
      (fun omega =>
        ∑ t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
          prespecifiedBatchCumulativeConditionalVariance theta h b K t omega) := by
  unfold conditionalVarianceSum
  have hsum :
      (fun omega =>
        ∑ n ∈ Finset.range (prespecifiedBatchCumulativeFinalRowLength K),
          (exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior))[
            (fun omega' =>
              |prespecifiedBatchCumulativeExtendedIncrement theta h b K n omega'| ^ 2) |
            globalFinalFiltrationSigma theta h b hInterior n] omega) =ᵐ[
            exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior)]
        fun omega =>
          ∑ n ∈ Finset.range (prespecifiedBatchCumulativeFinalRowLength K),
            prespecifiedBatchCumulativeExtendedConditionalVariance
              theta h b K n omega := by
    classical
    have hall : ∀ᵐ omega ∂
        exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior),
        ∀ n ∈ Finset.range (prespecifiedBatchCumulativeFinalRowLength K),
          (exactConcretePredeterminedBatchPathMeasure theta b (le_of_lt hInterior))[
            (fun omega' =>
              |prespecifiedBatchCumulativeExtendedIncrement theta h b K n omega'| ^ 2) |
            globalFinalFiltrationSigma theta h b hInterior n] omega =
          prespecifiedBatchCumulativeExtendedConditionalVariance theta h b K n omega :=
      (Finset.eventually_all
        (Finset.range (prespecifiedBatchCumulativeFinalRowLength K))).2
        (fun n _ => prespecifiedBatchCumulativeExtendedIncrement_square_condExp
          theta h b hInterior K n)
    filter_upwards [hall] with omega homega
    exact Finset.sum_congr rfl homega
  refine hsum.trans (Filter.Eventually.of_forall fun omega => ?_)
  symm
  calc
    (∑ t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
        prespecifiedBatchCumulativeConditionalVariance theta h b K t omega) =
      ∑ t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
        prespecifiedBatchCumulativeExtendedConditionalVariance theta h b K t.val omega := by
          apply Finset.sum_congr rfl
          intro t _
          rw [prespecifiedBatchCumulativeExtendedConditionalVariance_of_lt
            theta h b K t.val t.isLt]
    _ = ∑ n ∈ Finset.range (prespecifiedBatchCumulativeFinalRowLength K),
        prespecifiedBatchCumulativeExtendedConditionalVariance theta h b K n omega :=
      Fin.sum_univ_eq_sum_range
        (fun n => prespecifiedBatchCumulativeExtendedConditionalVariance theta h b K n omega)
        (prespecifiedBatchCumulativeFinalRowLength K)

theorem prespecifiedBatchCumulativeExtendedIncrement_abs_le
    (theta h b : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (K n : Nat) (omega : ExactConcretePredeterminedBatchPath) :
    |prespecifiedBatchCumulativeExtendedIncrement theta h b K n omega| <=
      prespecifiedBatchCumulativeJumpEnvelope K theta h := by
  by_cases hn : n < prespecifiedBatchCumulativeFinalRowLength K
  · rw [prespecifiedBatchCumulativeExtendedIncrement_of_lt theta h b K n hn]
    simpa [prespecifiedBatchCumulativeEnumeratedIncrement] using
      prespecifiedBatchCumulativeShotIncrement_abs_le K theta h b hInterior
        (prespecifiedBatchCumulativeFinalShotOrderIso K ⟨n, hn⟩) omega
  · rw [prespecifiedBatchCumulativeExtendedIncrement_of_not_lt theta h b K n hn]
    simp only [Pi.zero_apply, abs_zero]
    unfold prespecifiedBatchCumulativeJumpEnvelope
    exact div_nonneg
      (mul_nonneg (by
        unfold mixedProjectionL1
        exact Finset.sum_nonneg fun i _ => abs_nonneg (h i))
        (inv_nonneg.mpr (mixedInteriorGap_pos theta hInterior).le))
      (Real.sqrt_nonneg _)

theorem prespecifiedBatchCumulativeFinalRowLength_le_totalObservations
    (K : Nat) :
    prespecifiedBatchCumulativeFinalRowLength K <=
      prespecifiedBatchTotalObservations K := by
  rw [prespecifiedBatchCumulativeFinalRowLength_eq_sum]
  rw [prespecifiedBatchTotalObservations_eq_cumulativeCount]
  unfold cumulativeCount
  calc
    (∑ k : Fin K, 3 * exactConcreteBatchFinalBlocks k) =
        ∑ k ∈ Finset.range K, 3 * exactConcreteBatchFinalBlocks k :=
      Fin.sum_univ_eq_sum_range
        (fun k => 3 * exactConcreteBatchFinalBlocks k) K
    _ <= ∑ k ∈ Finset.range K, exactConcreteBatchSize k := by
      apply Finset.sum_le_sum
      intro k hk
      rw [exactConcreteBatchSize_decompose]
      omega

/-- The predictable fourth-moment term in Hall--Heyde is uniformly bounded
by the square of the fixed directional Fisher envelope. -/
theorem prespecifiedBatchPredictableQuadraticFourthMoment_le
    (theta h b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta) (K : Nat) :
    predictableQuadraticMoment
        (exactConcretePredeterminedBatchPathMeasure theta b
          (mixedNonzeroInterior_pauliPilotPhysical theta hTruth))
        (globalFinalFiltration theta h b hTruth.2)
        (prespecifiedBatchCumulativeExtendedIncrement theta h b K)
        4 (prespecifiedBatchCumulativeFinalRowLength K) <=
      (ENNReal.ofReal
        (prespecifiedBatchDirectionalInformationEnvelope theta h)) ^ 2 := by
  unfold predictableQuadraticMoment
  simp only [Nat.reduceDiv]
  calc
    (∫⁻ omega,
      (ENNReal.ofReal
        (conditionalVarianceSum
          (exactConcretePredeterminedBatchPathMeasure theta b
            (mixedNonzeroInterior_pauliPilotPhysical theta hTruth))
          (globalFinalFiltration theta h b hTruth.2)
          (prespecifiedBatchCumulativeExtendedIncrement theta h b K)
          (prespecifiedBatchCumulativeFinalRowLength K) omega)) ^ 2
        ∂exactConcretePredeterminedBatchPathMeasure theta b
          (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)) <=
      ∫⁻ _omega,
        (ENNReal.ofReal
          (prespecifiedBatchDirectionalInformationEnvelope theta h)) ^ 2
        ∂exactConcretePredeterminedBatchPathMeasure theta b
          (mixedNonzeroInterior_pauliPilotPhysical theta hTruth) := by
      apply lintegral_mono_ae
      filter_upwards [prespecifiedBatchCumulativeConditionalVarianceSum_terminal
        theta h b hTruth.2 K] with omega heq
      rw [heq]
      exact pow_le_pow_left'
        (ENNReal.ofReal_le_ofReal
          (prespecifiedBatchCumulativeConditionalVariance_nonnegative_and_le
            theta h b hTruth K omega).2) 2
    _ = (ENNReal.ofReal
        (prespecifiedBatchDirectionalInformationEnvelope theta h)) ^ 2 := by
      letI : IsProbabilityMeasure
          (exactConcretePredeterminedBatchPathMeasure theta b
            (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)) :=
        exactConcretePredeterminedBatchPathMeasure_isProbability theta b
          (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)
      simp

/-- The bounded-jump contribution is uniformly bounded after root-total-
sample normalization. -/
theorem prespecifiedBatchJumpFourthRealEnvelope
    (theta h : RLSVector 3) (K : Nat) :
    (prespecifiedBatchCumulativeFinalRowLength K : Real) *
        prespecifiedBatchCumulativeJumpEnvelope K theta h ^ 4 <=
      mixedProjectedScoreEnvelope theta h ^ 4 := by
  by_cases hK : K = 0
  · subst K
    have hrowzero : prespecifiedBatchCumulativeFinalRowLength 0 = 0 := by
      simp [prespecifiedBatchCumulativeFinalRowLength]
    rw [hrowzero]
    norm_num only [Nat.cast_zero, zero_mul]
    calc
      0 <= (mixedProjectedScoreEnvelope theta h ^ 2) ^ 2 := sq_nonneg _
      _ = mixedProjectedScoreEnvelope theta h ^ 4 := by ring
  · have hKpos : 0 < K := Nat.pos_of_ne_zero hK
    let N : Real := prespecifiedBatchTotalObservations K
    let E : Real := mixedProjectedScoreEnvelope theta h
    have hN : 0 < N := by
      unfold N
      exact_mod_cast prespecifiedBatchTotalObservations_pos K hKpos
    have hrow :
        (prespecifiedBatchCumulativeFinalRowLength K : Real) <= N := by
      have hrowNat :=
        prespecifiedBatchCumulativeFinalRowLength_le_totalObservations K
      have hrowReal :
          (prespecifiedBatchCumulativeFinalRowLength K : Real) <=
            (prespecifiedBatchTotalObservations K : Real) := by
        exact_mod_cast hrowNat
      simpa [N] using hrowReal
    have hsqrt : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN.le
    have hpow : 0 <= (E / Real.sqrt N) ^ 4 := by positivity
    calc
      (prespecifiedBatchCumulativeFinalRowLength K : Real) *
          prespecifiedBatchCumulativeJumpEnvelope K theta h ^ 4 <=
        N * (E / Real.sqrt N) ^ 4 := by
          unfold prespecifiedBatchCumulativeJumpEnvelope
            prespecifiedBatchSampleScale N E
          exact mul_le_mul_of_nonneg_right hrow hpow
      _ = E ^ 4 / N := by
        rw [div_pow]
        have hsqrt4 : Real.sqrt N ^ 4 = N ^ 2 := by nlinarith
        rw [hsqrt4]
        field_simp [hN.ne']
      _ <= E ^ 4 := by
        have hN1 : 1 <= N := by
          have hN1Nat : 1 <= prespecifiedBatchTotalObservations K :=
            Nat.one_le_iff_ne_zero.mpr
              (Nat.ne_of_gt (prespecifiedBatchTotalObservations_pos K hKpos))
          have hN1Real : (1 : Real) <=
              (prespecifiedBatchTotalObservations K : Real) := by
            exact_mod_cast hN1Nat
          simpa [N] using hN1Real
        exact div_le_self (by positivity) hN1

/-- Fourth moment of the literal cumulative final directional score. -/
def prespecifiedBatchCumulativeFinalScoreFourthMoment
    (theta h b : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (K : Nat) : ENNReal :=
  ∫⁻ omega,
    (ENNReal.ofReal
      |hallHeydeDeterministicVarianceRowSum
        prespecifiedBatchCumulativeFinalRowLength
        (prespecifiedBatchCumulativeEnumeratedIncrement theta h b) K omega|) ^ 4
    ∂exactConcretePredeterminedBatchPathMeasure theta b hphysical

/-- Hall--Heyde Theorem 2.12 gives a `K`-uniform fourth moment for the
literal cumulative final score in every fixed direction. -/
theorem prespecifiedBatchCumulativeFinalScoreFourthMoment_uniform
    (theta h b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta) :
    ∃ C4 : ENNReal, 0 < C4 ∧ C4 ≠ ∞ ∧
      ∀ K : Nat,
        prespecifiedBatchCumulativeFinalScoreFourthMoment theta h b
            (mixedNonzeroInterior_pauliPilotPhysical theta hTruth) K <=
          C4 *
            ((ENNReal.ofReal
              (prespecifiedBatchDirectionalInformationEnvelope theta h)) ^ 2 +
              (ENNReal.ofReal (mixedProjectedScoreEnvelope theta h)) ^ 4) := by
  obtain ⟨C4, hC4, hC4top, hhall⟩ :=
    hallHeyde1980_theorem2_12_martingaleRosenthal_upper 4 (by omega)
  refine ⟨C4, hC4, hC4top, ?_⟩
  intro K
  let mu := exactConcretePredeterminedBatchPathMeasure theta b
    (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)
  let filtration := globalFinalFiltration theta h b hTruth.2
  let increment := prespecifiedBatchCumulativeExtendedIncrement theta h b K
  let n := prespecifiedBatchCumulativeFinalRowLength K
  let B := prespecifiedBatchCumulativeJumpEnvelope K theta h
  let E := mixedProjectedScoreEnvelope theta h
  letI : IsProbabilityMeasure mu :=
    exactConcretePredeterminedBatchPathMeasure_isProbability theta b
      (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)
  have hmartingale : Martingale (scalarPartialSum increment) filtration mu := by
    exact prespecifiedBatchCumulativeExtendedPartialSum_martingale
      theta h b hTruth.2 K
  have hB : 0 <= B := by
    unfold B
    exact (prespecifiedBatchCumulativeExtendedIncrement_abs_le
      theta h b hTruth.2 K n default).trans' (abs_nonneg _)
  have hbound : ∀ k, ∀ᵐ omega ∂mu, norm (increment k omega) <= B := by
    intro k
    filter_upwards with omega
    simpa only [Real.norm_eq_abs] using
      prespecifiedBatchCumulativeExtendedIncrement_abs_le
        theta h b hTruth.2 K k omega
  have hL4 : ∀ k < n, MemLp (increment k) (4 : ENNReal) mu :=
    fun k _ => increment_memLp_of_martingale_uniform_bound
      mu filtration increment hmartingale B hbound 4 k
  have hL2 : ∀ k < n, MemLp (increment k) 2 mu :=
    fun k _ => increment_memLp_of_martingale_uniform_bound
      mu filtration increment hmartingale B hbound 2 k
  have hsource := hhall mu filtration increment n hmartingale hL4 hL2
  have hpredictable :
      predictableQuadraticMoment mu filtration increment 4 n <=
        (ENNReal.ofReal
          (prespecifiedBatchDirectionalInformationEnvelope theta h)) ^ 2 := by
    exact prespecifiedBatchPredictableQuadraticFourthMoment_le
      theta h b hTruth K
  have hjump0 :
      incrementAbsoluteMomentSum mu increment 4 n <=
        (n : ENNReal) * (ENNReal.ofReal B) ^ 4 :=
    incrementAbsoluteFourthMomentSum_le_of_uniform_bound
      mu increment B hB hbound n
  have hjumpReal : (n : Real) * B ^ 4 <= E ^ 4 := by
    simpa [n, B, E] using prespecifiedBatchJumpFourthRealEnvelope theta h K
  have hjumpCast :
      (n : ENNReal) * (ENNReal.ofReal B) ^ 4 =
        ENNReal.ofReal ((n : Real) * B ^ 4) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg n),
      ENNReal.ofReal_natCast, ENNReal.ofReal_pow hB]
  have hjump :
      incrementAbsoluteMomentSum mu increment 4 n <=
        (ENNReal.ofReal E) ^ 4 := by
    calc
      incrementAbsoluteMomentSum mu increment 4 n <=
          (n : ENNReal) * (ENNReal.ofReal B) ^ 4 := hjump0
      _ = ENNReal.ofReal ((n : Real) * B ^ 4) := hjumpCast
      _ <= ENNReal.ofReal (E ^ 4) := ENNReal.ofReal_le_ofReal hjumpReal
      _ = (ENNReal.ofReal E) ^ 4 := ENNReal.ofReal_pow (by
        unfold E mixedProjectedScoreEnvelope
        exact mul_nonneg (by
          unfold mixedProjectionL1
          exact Finset.sum_nonneg fun i _ => abs_nonneg (h i))
          (inv_nonneg.mpr (mixedInteriorGap_pos theta hTruth.2).le)) 4
  have hterminal :
      prespecifiedBatchCumulativeFinalScoreFourthMoment theta h b
          (mixedNonzeroInterior_pauliPilotPhysical theta hTruth) K =
        terminalAbsoluteMoment mu increment 4 n := by
    unfold prespecifiedBatchCumulativeFinalScoreFourthMoment
      terminalAbsoluteMoment
    apply lintegral_congr
    intro omega
    rw [prespecifiedBatchCumulativeExtendedPartialSum_terminal theta h b K omega]
  rw [hterminal]
  exact hsource.trans (by
    gcongr)

/-- Coordinate direction used to recover the full three-dimensional score
from its scalar projections. -/
def prespecifiedBatchCoordinateDirection (j : Fin 3) : RLSVector 3 :=
  fun i => if i = j then 1 else 0

/-- Literal cumulative final score vector. -/
def prespecifiedBatchCumulativeFinalScoreVector
    (theta b : RLSVector 3) (K : Nat)
    (omega : ExactConcretePredeterminedBatchPath) : RLSVector 3 :=
  fun j => hallHeydeDeterministicVarianceRowSum
    prespecifiedBatchCumulativeFinalRowLength
    (prespecifiedBatchCumulativeEnumeratedIncrement theta
      (prespecifiedBatchCoordinateDirection j) b) K omega

/-- Fourth moment of the Euclidean norm of the literal final score vector. -/
def prespecifiedBatchCumulativeFinalScoreVectorFourthMoment
    (theta b : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (K : Nat) : ENNReal :=
  ∫⁻ omega,
    ENNReal.ofReal
      (QubitOracle.blochNormSq
        (prespecifiedBatchCumulativeFinalScoreVector theta b K omega) ^ 2)
    ∂exactConcretePredeterminedBatchPathMeasure theta b hphysical

theorem fin3_blochNormSq_sq_le_three_sum_fourth (x : RLSVector 3) :
    QubitOracle.blochNormSq x ^ 2 <= 3 * ∑ j : Fin 3, |x j| ^ 4 := by
  have habsFourth (a : Real) : |a| ^ 4 = a ^ 4 := by
    rw [← abs_pow]
    exact abs_of_nonneg (by positivity)
  have hsumSq :
      (∑ j : Fin 3, x j ^ 2) = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
    norm_num [Fin.sum_univ_succ]
    ring
  have hsumFourth :
      (∑ j : Fin 3, |x j| ^ 4) =
        x 0 ^ 4 + x 1 ^ 4 + x 2 ^ 4 := by
    norm_num [Fin.sum_univ_succ, habsFourth]
    ring
  have hsquares : 0 <=
      (x 0 ^ 2 - x 1 ^ 2) ^ 2 +
      (x 0 ^ 2 - x 2 ^ 2) ^ 2 +
      (x 1 ^ 2 - x 2 ^ 2) ^ 2 := by positivity
  unfold QubitOracle.blochNormSq
  rw [hsumSq, hsumFourth]
  nlinarith

/-- The three scalar Hall--Heyde bounds imply a `K`-uniform fourth moment
for the Euclidean norm of the full `Fin 3` cumulative final score vector. -/
theorem prespecifiedBatchCumulativeFinalScoreVectorFourthMoment_uniform
    (theta b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta) :
    ∃ Cvec : ENNReal, Cvec ≠ ∞ ∧ ∀ K : Nat,
      prespecifiedBatchCumulativeFinalScoreVectorFourthMoment theta b
          (mixedNonzeroInterior_pauliPilotPhysical theta hTruth) K <= Cvec := by
  choose C hCpos hCtop hCbound using fun j : Fin 3 =>
    prespecifiedBatchCumulativeFinalScoreFourthMoment_uniform theta
      (prespecifiedBatchCoordinateDirection j) b hTruth
  let Bj : Fin 3 -> ENNReal := fun j =>
    C j *
      ((ENNReal.ofReal
        (prespecifiedBatchDirectionalInformationEnvelope theta
          (prespecifiedBatchCoordinateDirection j))) ^ 2 +
        (ENNReal.ofReal
          (mixedProjectedScoreEnvelope theta
            (prespecifiedBatchCoordinateDirection j))) ^ 4)
  refine ⟨3 * ∑ j : Fin 3, Bj j, ?_, ?_⟩
  · apply ENNReal.mul_ne_top
    · norm_num
    · exact (ENNReal.sum_ne_top (s := Finset.univ) (f := Bj)).2 (by
      intro j hj
      unfold Bj
      apply ENNReal.mul_ne_top (hCtop j)
      exact (ENNReal.add_ne_top).2 ⟨by finiteness, by finiteness⟩)
  · intro K
    have hscoreMeasurable (j : Fin 3) :
        Measurable (fun omega =>
          prespecifiedBatchCumulativeFinalScoreVector theta b K omega j) := by
      unfold prespecifiedBatchCumulativeFinalScoreVector
      have hpartial :
          Measurable
            (scalarPartialSum
              (prespecifiedBatchCumulativeExtendedIncrement theta
                (prespecifiedBatchCoordinateDirection j) b K)
              (prespecifiedBatchCumulativeFinalRowLength K)) := by
        unfold scalarPartialSum
        apply Finset.measurable_sum
        intro k hk
        exact
          (prespecifiedBatchCumulativeExtendedIncrement_measurable_succ
            theta (prespecifiedBatchCoordinateDirection j) b hTruth.2 K k).mono
            ((globalFinalFiltration theta
              (prespecifiedBatchCoordinateDirection j) b hTruth.2).le (k + 1))
            le_rfl
      convert hpartial using 1
      funext omega
      exact (prespecifiedBatchCumulativeExtendedPartialSum_terminal theta
        (prespecifiedBatchCoordinateDirection j) b K omega).symm
    unfold prespecifiedBatchCumulativeFinalScoreVectorFourthMoment
    calc
      (∫⁻ omega,
        ENNReal.ofReal
          (QubitOracle.blochNormSq
            (prespecifiedBatchCumulativeFinalScoreVector theta b K omega) ^ 2)
        ∂exactConcretePredeterminedBatchPathMeasure theta b
          (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)) <=
        ∫⁻ omega,
          ENNReal.ofReal
            (3 * ∑ j : Fin 3,
              |prespecifiedBatchCumulativeFinalScoreVector theta b K omega j| ^ 4)
          ∂exactConcretePredeterminedBatchPathMeasure theta b
            (mixedNonzeroInterior_pauliPilotPhysical theta hTruth) := by
        apply lintegral_mono
        intro omega
        exact ENNReal.ofReal_le_ofReal
          (fin3_blochNormSq_sq_le_three_sum_fourth
            (prespecifiedBatchCumulativeFinalScoreVector theta b K omega))
      _ = 3 * ∑ j : Fin 3,
          prespecifiedBatchCumulativeFinalScoreFourthMoment theta
            (prespecifiedBatchCoordinateDirection j) b
            (mixedNonzeroInterior_pauliPilotPhysical theta hTruth) K := by
        have hpoint (omega : ExactConcretePredeterminedBatchPath) :
            ENNReal.ofReal
                (3 * ∑ j : Fin 3,
                  |prespecifiedBatchCumulativeFinalScoreVector theta b K omega j| ^ 4) =
              3 * ∑ j : Fin 3,
                (ENNReal.ofReal
                  |prespecifiedBatchCumulativeFinalScoreVector theta b K omega j|) ^ 4 := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : Real) <= 3)]
          norm_num
          rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          exact ENNReal.ofReal_pow (abs_nonneg _) 4
        rw [lintegral_congr hpoint]
        rw [lintegral_const_mul]
        · rw [lintegral_finset_sum]
          · rfl
          · intro j hj
            exact ((hscoreMeasurable j).abs.ennreal_ofReal).pow measurable_const
        · apply Finset.measurable_sum
          intro j hj
          exact ((hscoreMeasurable j).abs.ennreal_ofReal).pow measurable_const
      _ <= 3 * ∑ j : Fin 3, Bj j := by
        gcongr with j
        exact hCbound j K

end

end QubitOracle.Paper
