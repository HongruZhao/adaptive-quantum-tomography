import QubitOracle.Paper.OneQubitPrespecifiedBatchFiniteExperiment
import QubitOracle.Paper.OneQubitPrespecifiedBatchCumulativeSchedule
import QubitOracle.Paper.OneQubitMixedExactCycleTaylorRemainder
import QubitOracle.Paper.OneQubitMixedPolynomialPilotLANNegligible

/-!
# Cumulative likelihood expansion for the prespecified batches

This file performs only finite likelihood algebra and deterministic remainder
estimates.  At horizon `K`, every pilot and final Born factor is perturbed by
the same physical displacement `h / sqrt(N_K)`, where `N_K` is the exact
cumulative observation count.  The resulting exact log likelihood is split
into its normalized score, observed directional information, and summed
third-order logarithm remainder.

The score CLT and convergence of the random final observed information are not
asserted here.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory Topology

noncomputable section

open PureMultilevelSequentialBatchAdaptive

attribute [local instance]
  pauliPilotBornPathMeasurableSpace
  mixedTwoStageFiniteRowMeasurableSpace
  mixedTwoStageFiniteRowMeasurableSingletonClass

/-- Genuine root-total-sample local Bloch alternative. -/
def prespecifiedBatchLocalParameter
    (theta h : RLSVector 3) (K : Nat) : RLSVector 3 :=
  mixedLocalAlternative theta prespecifiedBatchTotalObservations K h

/-- Direction transported to the root-size normalization of final batch `k`.
It makes the final exact-cycle local parameter equal to the common physical
alternative `theta + h / sqrt(N_K)`. -/
def prespecifiedBatchFinalDirection
    (h : RLSVector 3) (K : Nat) (k : Finset.range K) : RLSVector 3 :=
  fun j =>
    Real.sqrt (exactConcreteBatchExploitationSize k.1 : Real) /
      Real.sqrt (prespecifiedBatchTotalObservations K : Real) * h j

/-- One pilot score increment at the common root-total-sample scale. -/
def prespecifiedBatchPilotNormalizedScore
    (theta h : RLSVector 3) (K : Nat)
    (j : Fin 3) (outcome : Bool) : Real :=
  mixedPilotOneShotDirectionalScore theta h j outcome /
    Real.sqrt (prespecifiedBatchTotalObservations K : Real)

/-- One final score increment at the common root-total-sample scale, expressed
through the exact-cycle normalization of its own batch. -/
def prespecifiedBatchFinalNormalizedScore
    (theta h b : RLSVector 3) (K : Nat) (k : Finset.range K)
    (row : ExactConcretePredeterminedBatchRow k.1)
    (t : Fin (3 * exactConcreteBatchFinalBlocks k.1)) : Real :=
  mixedExactCycleNormalizedDirectionalScore theta
    (prespecifiedBatchFinalDirection h K k)
    (exactConcreteBatchSelectedFrame k.1 b) row.1 t row.2

/-- Exact cumulative log likelihood, defined observation-by-observation from
the Born factors whose products are the exact finite row masses. -/
def prespecifiedBatchCumulativeLogLikelihood
    (theta h b : RLSVector 3) (K : Nat)
    (x : PrespecifiedBatchFinitePrefix K) : Real :=
  ∑ k : Finset.range K,
    ((∑ s : Fin (exactConcreteBatchPilotBlocks k.1),
        ∑ j : Fin 3,
          Real.log
            (pauliBornProbability (prespecifiedBatchLocalParameter theta h K)
                j ((x k).1 s j) /
              pauliBornProbability theta j ((x k).1 s j))) +
      ∑ t : Fin (3 * exactConcreteBatchFinalBlocks k.1),
        Real.log
          (mixedTwoStageFinalBornProbability
              (prespecifiedBatchLocalParameter theta h K)
              (exactConcreteBatchSelectedFrame k.1 b) (x k).1 t ((x k).2 t) /
            mixedTwoStageFinalBornProbability theta
              (exactConcreteBatchSelectedFrame k.1 b) (x k).1 t ((x k).2 t)))

/-- Cumulative normalized directional score. -/
def prespecifiedBatchCumulativeNormalizedScore
    (theta h b : RLSVector 3) (K : Nat)
    (x : PrespecifiedBatchFinitePrefix K) : Real :=
  ∑ k : Finset.range K,
    ((∑ s : Fin (exactConcreteBatchPilotBlocks k.1),
        ∑ j : Fin 3,
          prespecifiedBatchPilotNormalizedScore theta h K j ((x k).1 s j)) +
      ∑ t : Fin (3 * exactConcreteBatchFinalBlocks k.1),
        prespecifiedBatchFinalNormalizedScore theta h b K k (x k) t)

/-- Cumulative observed directional information. -/
def prespecifiedBatchCumulativeObservedDirectionalInformation
    (theta h b : RLSVector 3) (K : Nat)
    (x : PrespecifiedBatchFinitePrefix K) : Real :=
  ∑ k : Finset.range K,
    ((∑ s : Fin (exactConcreteBatchPilotBlocks k.1),
        ∑ j : Fin 3,
          prespecifiedBatchPilotNormalizedScore theta h K j ((x k).1 s j) ^ 2) +
      ∑ t : Fin (3 * exactConcreteBatchFinalBlocks k.1),
        prespecifiedBatchFinalNormalizedScore theta h b K k (x k) t ^ 2)

/-- Sum of the literal scalar third-order Taylor residuals. -/
def prespecifiedBatchCumulativeTaylorRemainder
    (theta h b : RLSVector 3) (K : Nat)
    (x : PrespecifiedBatchFinitePrefix K) : Real :=
  ∑ k : Finset.range K,
    ((∑ s : Fin (exactConcreteBatchPilotBlocks k.1),
        ∑ j : Fin 3,
          logThirdOrderRemainder
            (prespecifiedBatchPilotNormalizedScore theta h K j
              ((x k).1 s j))) +
      ∑ t : Fin (3 * exactConcreteBatchFinalBlocks k.1),
        logThirdOrderRemainder
          (prespecifiedBatchFinalNormalizedScore theta h b K k (x k) t))

theorem prespecifiedBatchTotalObservations_eq (K : Nat) :
    prespecifiedBatchTotalObservations K = (3 * K) ^ 6 := by
  exact exactConcreteBatchSize_cumulative K

theorem prespecifiedBatchTotalObservations_pos
    (K : Nat) (hK : 0 < K) :
    0 < prespecifiedBatchTotalObservations K := by
  rw [prespecifiedBatchTotalObservations_eq]
  positivity

/-- The transported final direction represents the same physical local
alternative as the global total-sample parameter. -/
theorem mixedExactCycleLocalParameter_prespecifiedBatchFinalDirection
    (theta h : RLSVector 3) (K : Nat) (hK : 0 < K)
    (k : Finset.range K) :
    mixedExactCycleLocalParameter theta
        (prespecifiedBatchFinalDirection h K k)
        (exactConcreteBatchFinalBlocks k.1) =
      prespecifiedBatchLocalParameter theta h K := by
  have hfinal : 0 < exactConcreteBatchExploitationSize k.1 :=
    exactConcreteBatchExploitationSize_pos k.1
  have htotal : 0 < prespecifiedBatchTotalObservations K :=
    prespecifiedBatchTotalObservations_pos K hK
  have hfinalEq :
      3 * exactConcreteBatchFinalBlocks k.1 =
        exactConcreteBatchExploitationSize k.1 := rfl
  have hsFinal : Real.sqrt
      (exactConcreteBatchExploitationSize k.1 : Real) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hfinal))
  have hsTotal : Real.sqrt
      (prespecifiedBatchTotalObservations K : Real) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast htotal))
  funext j
  unfold mixedExactCycleLocalParameter prespecifiedBatchFinalDirection
    prespecifiedBatchLocalParameter mixedLocalAlternative mixedLocalScale
  rw [hfinalEq]
  field_simp [hsFinal, hsTotal]

/-- Exact pilot Born-factor ratio. -/
theorem prespecifiedBatchPilotBornRatio_eq_one_add_score
    (theta h : RLSVector 3) (hInterior : MixedPilotStrictInterior theta)
    (K : Nat) (hK : 0 < K) (j : Fin 3) (outcome : Bool) :
    pauliBornProbability (prespecifiedBatchLocalParameter theta h K) j outcome /
        pauliBornProbability theta j outcome =
      1 + prespecifiedBatchPilotNormalizedScore theta h K j outcome := by
  have htotal := prespecifiedBatchTotalObservations_pos K hK
  have hsqrt : Real.sqrt
      (prespecifiedBatchTotalObservations K : Real) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast htotal))
  have hden : 0 < 1 + pauliOutcomeSign outcome * theta j :=
    (mixedPilotInteriorMargin_pos theta hInterior).trans_le
      (mixedPilot_scoreDenominator_ge_margin theta hInterior j outcome)
  rw [pauliBornProbability_eq_signed, pauliBornProbability_eq_signed]
  unfold prespecifiedBatchLocalParameter mixedLocalAlternative mixedLocalScale
    prespecifiedBatchPilotNormalizedScore mixedPilotOneShotDirectionalScore
  field_simp [hsqrt, ne_of_gt hden]
  ring

/-- Exact final Born-factor ratio. -/
theorem prespecifiedBatchFinalBornRatio_eq_one_add_score
    (theta h b : RLSVector 3) (hInterior : MixedPilotStrictInterior theta)
    (K : Nat) (hK : 0 < K) (k : Finset.range K)
    (row : ExactConcretePredeterminedBatchRow k.1)
    (t : Fin (3 * exactConcreteBatchFinalBlocks k.1)) :
    mixedTwoStageFinalBornProbability
          (prespecifiedBatchLocalParameter theta h K)
          (exactConcreteBatchSelectedFrame k.1 b) row.1 t (row.2 t) /
        mixedTwoStageFinalBornProbability theta
          (exactConcreteBatchSelectedFrame k.1 b) row.1 t (row.2 t) =
      1 + prespecifiedBatchFinalNormalizedScore theta h b K k row t := by
  rw [← mixedExactCycleLocalParameter_prespecifiedBatchFinalDirection
      theta h K hK k]
  exact mixedExactCycleFinalBornRatio_eq_one_add_normalizedScore
    theta (prespecifiedBatchFinalDirection h K k)
    (exactConcreteBatchSelectedFrame k.1 b) row.1 row.2 t
    hInterior (exactConcreteBatchFinalBlocks_pos k.1)

/-- Exact finite Taylor decomposition of the cumulative likelihood. -/
theorem prespecifiedBatchCumulativeLogLikelihood_exactTaylor
    (theta h b : RLSVector 3) (hInterior : MixedPilotStrictInterior theta)
    (K : Nat) (hK : 0 < K) (x : PrespecifiedBatchFinitePrefix K) :
    prespecifiedBatchCumulativeLogLikelihood theta h b K x =
      prespecifiedBatchCumulativeNormalizedScore theta h b K x -
        prespecifiedBatchCumulativeObservedDirectionalInformation
          theta h b K x / 2 +
      prespecifiedBatchCumulativeTaylorRemainder theta h b K x := by
  classical
  unfold prespecifiedBatchCumulativeLogLikelihood
    prespecifiedBatchCumulativeNormalizedScore
    prespecifiedBatchCumulativeObservedDirectionalInformation
    prespecifiedBatchCumulativeTaylorRemainder
  rw [Finset.sum_div, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp_rw [prespecifiedBatchPilotBornRatio_eq_one_add_score
    theta h hInterior K hK]
  simp_rw [prespecifiedBatchFinalBornRatio_eq_one_add_score
    theta h b hInterior K hK k]
  have hscalar (z : Real) :
      Real.log (1 + z) =
        z - z ^ 2 / 2 + logThirdOrderRemainder z := by
    unfold logThirdOrderRemainder
    ring
  simp_rw [hscalar]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_div, add_div]
  abel_nf

/-- Exponentiating the cumulative log likelihood recovers the ratio of the
products of the exact finite row masses. -/
theorem prespecifiedBatchCumulativeLogLikelihood_exp_eq_productRowMassRatio
    (theta h b : RLSVector 3)
    (hTheta : MixedPilotStrictInterior theta)
    (K : Nat)
    (hEta : MixedPilotStrictInterior
      (prespecifiedBatchLocalParameter theta h K))
    (x : PrespecifiedBatchFinitePrefix K) :
    Real.exp (prespecifiedBatchCumulativeLogLikelihood theta h b K x) =
      (∏ k : Finset.range K,
        mixedTwoStageFiniteRowMass
          (prespecifiedBatchLocalParameter theta h K)
          (exactConcreteBatchSelectedFrame k.1 b) (x k)) /
      (∏ k : Finset.range K,
        mixedTwoStageFiniteRowMass theta
          (exactConcreteBatchSelectedFrame k.1 b) (x k)) := by
  classical
  unfold prespecifiedBatchCumulativeLogLikelihood
  rw [Real.exp_sum]
  simp_rw [Real.exp_add, Real.exp_sum]
  simp_rw [Real.exp_log
    (div_pos
      (pauliBornProbability_pos_of_strictInterior _ hEta _ _)
      (pauliBornProbability_pos_of_strictInterior theta hTheta _ _))]
  simp_rw [Real.exp_log
    (div_pos
      (mixedTwoStageFinalBornProbability_pos_of_strictInterior
        _ _ hEta _ _ _)
      (mixedTwoStageFinalBornProbability_pos_of_strictInterior
        theta _ hTheta _ _ _))]
  unfold mixedTwoStageFiniteRowMass pauliPilotPathMass
    pauliPilotBlockMass mixedTwoStageConditionalFinalPathMass
  simp_rw [Finset.prod_div_distrib]
  have hfourProductRatio
      (alpha : Type) [Fintype alpha]
      (A B C D : alpha → Real) :
      (∏ i : alpha, (A i / B i) * (C i / D i)) =
        (∏ i : alpha, A i * C i) /
          (∏ i : alpha, B i * D i) := by
    have hprod (f g : alpha → Real) :
        (∏ i : alpha, f i * g i) =
          (∏ i : alpha, f i) * ∏ i : alpha, g i := by
      simpa only using
        (Finset.prod_mul_distrib
          (s := Finset.univ) (f := f) (g := g))
    have hinv (f : alpha → Real) :
        (∏ i : alpha, (f i)⁻¹) = (∏ i : alpha, f i)⁻¹ := by
      simpa only using
        (Finset.prod_inv_distrib (s := Finset.univ) f)
    simp only [div_eq_mul_inv, hprod, hinv, mul_inv_rev]
    ring
  simpa only [div_eq_mul_inv] using
    (hfourProductRatio (Finset.range K)
      (fun k =>
        ∏ s : Fin (exactConcreteBatchPilotBlocks k.1),
          ∏ j : Fin 3,
            pauliBornProbability (prespecifiedBatchLocalParameter theta h K)
              j ((x k).1 s j))
      (fun k =>
        ∏ s : Fin (exactConcreteBatchPilotBlocks k.1),
          ∏ j : Fin 3, pauliBornProbability theta j ((x k).1 s j))
      (fun k =>
        ∏ t : Fin (3 * exactConcreteBatchFinalBlocks k.1),
          mixedTwoStageFinalBornProbability
            (prespecifiedBatchLocalParameter theta h K)
            (exactConcreteBatchSelectedFrame k.1 b) (x k).1 t ((x k).2 t))
      (fun k =>
        ∏ t : Fin (3 * exactConcreteBatchFinalBlocks k.1),
          mixedTwoStageFinalBornProbability theta
            (exactConcreteBatchSelectedFrame k.1 b) (x k).1 t ((x k).2 t)))

/-- One envelope covering both pilot and adaptive final score increments. -/
def prespecifiedBatchScoreEnvelope
    (theta h : RLSVector 3) : Real :=
  mixedPilotDirectionalEnvelope theta h +
    mixedProjectedScoreEnvelope theta h

theorem prespecifiedBatchScoreEnvelope_nonnegative
    (theta h : RLSVector 3) (hInterior : MixedPilotStrictInterior theta) :
    0 ≤ prespecifiedBatchScoreEnvelope theta h := by
  unfold prespecifiedBatchScoreEnvelope
  exact add_nonneg
    (mixedPilotDirectionalEnvelope_nonneg theta h hInterior)
    (by
      unfold mixedProjectedScoreEnvelope mixedProjectionL1
      exact mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (inv_nonneg.mpr (mixedInteriorGap_pos theta hInterior).le))

/-- Deterministic cubic envelope for all `N_K` observations. -/
def prespecifiedBatchCubicRemainderEnvelope
    (theta h : RLSVector 3) (K : Nat) : Real :=
  (2 / 3 : Real) * prespecifiedBatchScoreEnvelope theta h ^ 3 *
    mixedLocalScale prespecifiedBatchTotalObservations K

theorem prespecifiedBatchCubicRemainderEnvelope_tendsto_zero
    (theta h : RLSVector 3) :
    Tendsto (prespecifiedBatchCubicRemainderEnvelope theta h)
      atTop (nhds 0) := by
  unfold prespecifiedBatchCubicRemainderEnvelope
  simpa using
    (tendsto_const_nhds.mul prespecifiedBatchLocalScale_tendsto_zero)

/-- Deterministic coefficient controlling the cumulative pilot quadratic
term. -/
def prespecifiedBatchPilotQuadraticEnvelope
    (theta h : RLSVector 3) (K : Nat) : Real :=
  prespecifiedBatchScoreEnvelope theta h ^ 2 *
    ((prespecifiedBatchTotalObservations K : Real)⁻¹ *
      (cumulativeCount exactConcreteBatchExplorationSize K : Real))

theorem prespecifiedBatchPilotQuadraticEnvelope_tendsto_zero
    (theta h : RLSVector 3) :
    Tendsto (prespecifiedBatchPilotQuadraticEnvelope theta h)
      atTop (nhds 0) := by
  unfold prespecifiedBatchPilotQuadraticEnvelope
  simpa [prespecifiedBatchTotalObservations] using
    (tendsto_const_nhds.mul
      exactConcreteBatch_explorationFraction_tendsto_zero)

/-- The variance scale of the normalized cumulative pilot score is exactly
controlled by `Q_K/N_K`, hence tends to zero.  Turning this coefficient into a
probability statement requires only the finite-product centering/variance
transfer, not a CLT. -/
def prespecifiedBatchPilotLinearVarianceEnvelope
    (theta h : RLSVector 3) (K : Nat) : Real :=
  mixedPilotScoreVarianceConstant theta h *
    ((prespecifiedBatchTotalObservations K : Real)⁻¹ *
      (cumulativeCount exactConcreteBatchExplorationSize K : Real) / 3)

theorem prespecifiedBatchPilotLinearVarianceEnvelope_tendsto_zero
    (theta h : RLSVector 3) :
    Tendsto (prespecifiedBatchPilotLinearVarianceEnvelope theta h)
      atTop (nhds 0) := by
  have hscaled :=
    exactConcreteBatch_explorationFraction_tendsto_zero.div_const 3
  unfold prespecifiedBatchPilotLinearVarianceEnvelope
  simpa [prespecifiedBatchTotalObservations, mul_assoc] using
    (tendsto_const_nhds.mul hscaled)

/-! ## Actual pilot terms and pathwise remainder control -/

/-- The literal pilot part of the cumulative normalized score. -/
def prespecifiedBatchCumulativePilotNormalizedScore
    (theta h : RLSVector 3) (K : Nat)
    (x : PrespecifiedBatchFinitePrefix K) : Real :=
  ∑ k : Finset.range K,
    ∑ s : Fin (exactConcreteBatchPilotBlocks k.1),
      ∑ j : Fin 3,
        prespecifiedBatchPilotNormalizedScore theta h K j ((x k).1 s j)

/-- The literal pilot part of the cumulative observed information. -/
def prespecifiedBatchCumulativePilotObservedInformation
    (theta h : RLSVector 3) (K : Nat)
    (x : PrespecifiedBatchFinitePrefix K) : Real :=
  ∑ k : Finset.range K,
    ∑ s : Fin (exactConcreteBatchPilotBlocks k.1),
      ∑ j : Fin 3,
        prespecifiedBatchPilotNormalizedScore theta h K j ((x k).1 s j) ^ 2

/-- Every pilot increment obeys the common root-total-sample envelope. -/
theorem prespecifiedBatchPilotNormalizedScore_abs_le
    (theta h : RLSVector 3) (hInterior : MixedPilotStrictInterior theta)
    (K : Nat) (hK : 0 < K) (j : Fin 3) (outcome : Bool) :
    |prespecifiedBatchPilotNormalizedScore theta h K j outcome| ≤
      prespecifiedBatchScoreEnvelope theta h /
        Real.sqrt (prespecifiedBatchTotalObservations K : Real) := by
  have htotal := prespecifiedBatchTotalObservations_pos K hK
  have hsqrt : 0 < Real.sqrt
      (prespecifiedBatchTotalObservations K : Real) :=
    Real.sqrt_pos.2 (by exact_mod_cast htotal)
  have hmargin := mixedPilotInteriorMargin_pos theta hInterior
  have hj : |h j| ≤ ∑ i : Fin 3, |h i| :=
    Finset.single_le_sum (fun i _ => abs_nonneg (h i)) (Finset.mem_univ j)
  have hpilot :
      |mixedPilotOneShotDirectionalScore theta h j outcome| ≤
        mixedPilotDirectionalEnvelope theta h := by
    calc
      |mixedPilotOneShotDirectionalScore theta h j outcome| ≤
          |h j| / mixedPilotInteriorMargin theta :=
        abs_mixedPilotOneShotDirectionalScore_le
          theta h hInterior j outcome
      _ ≤ (∑ i : Fin 3, |h i|) / mixedPilotInteriorMargin theta :=
        div_le_div_of_nonneg_right hj hmargin.le
      _ = mixedPilotDirectionalEnvelope theta h := rfl
  have hfinalNonneg : 0 ≤ mixedProjectedScoreEnvelope theta h := by
    unfold mixedProjectedScoreEnvelope mixedProjectionL1
    exact mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (inv_nonneg.mpr (mixedInteriorGap_pos theta hInterior).le)
  unfold prespecifiedBatchPilotNormalizedScore
  rw [abs_div, abs_of_pos hsqrt]
  exact div_le_div_of_nonneg_right
    (hpilot.trans (le_add_of_nonneg_right hfinalNonneg)) hsqrt.le

/-- Every adaptive final increment obeys the same common envelope. -/
theorem prespecifiedBatchFinalNormalizedScore_abs_le
    (theta h b : RLSVector 3) (hInterior : MixedPilotStrictInterior theta)
    (K : Nat) (hK : 0 < K) (k : Finset.range K)
    (row : ExactConcretePredeterminedBatchRow k.1)
    (t : Fin (3 * exactConcreteBatchFinalBlocks k.1)) :
    |prespecifiedBatchFinalNormalizedScore theta h b K k row t| ≤
      prespecifiedBatchScoreEnvelope theta h /
        Real.sqrt (prespecifiedBatchTotalObservations K : Real) := by
  have hfinal : 0 < exactConcreteBatchExploitationSize k.1 :=
    exactConcreteBatchExploitationSize_pos k.1
  have htotal := prespecifiedBatchTotalObservations_pos K hK
  have hsFinal : 0 < Real.sqrt
      (exactConcreteBatchExploitationSize k.1 : Real) :=
    Real.sqrt_pos.2 (by exact_mod_cast hfinal)
  have hsTotal : 0 < Real.sqrt
      (prespecifiedBatchTotalObservations K : Real) :=
    Real.sqrt_pos.2 (by exact_mod_cast htotal)
  let c : Real :=
    Real.sqrt (exactConcreteBatchExploitationSize k.1 : Real) /
      Real.sqrt (prespecifiedBatchTotalObservations K : Real)
  have hc : 0 ≤ c := div_nonneg hsFinal.le hsTotal.le
  have hbase :=
    mixedExactCycleNormalizedDirectionalScore_abs_le_envelope
      theta (prespecifiedBatchFinalDirection h K k)
      (exactConcreteBatchSelectedFrame k.1 b) row.1 row.2 t
      hInterior (exactConcreteBatchFinalBlocks_pos k.1)
  have hdir : prespecifiedBatchFinalDirection h K k =
      fun j => c * h j := by rfl
  rw [hdir, mixedProjectedScoreEnvelope_scale theta h c hc] at hbase
  have hscale :
      c * mixedProjectedScoreEnvelope theta h /
          Real.sqrt (3 * exactConcreteBatchFinalBlocks k.1 : Nat) =
        mixedProjectedScoreEnvelope theta h /
          Real.sqrt (prespecifiedBatchTotalObservations K : Real) := by
    change
      (Real.sqrt (exactConcreteBatchExploitationSize k.1 : Real) /
          Real.sqrt (prespecifiedBatchTotalObservations K : Real)) *
          mixedProjectedScoreEnvelope theta h /
          Real.sqrt (exactConcreteBatchExploitationSize k.1 : Real) = _
    field_simp [ne_of_gt hsFinal, ne_of_gt hsTotal]
  rw [hscale] at hbase
  have hpilotNonneg :=
    mixedPilotDirectionalEnvelope_nonneg theta h hInterior
  exact hbase.trans
    (div_le_div_of_nonneg_right
      (le_add_of_nonneg_left hpilotNonneg) hsTotal.le)

/-- Raw pathwise cubic envelope before cancelling `N_K / N_K^(3/2)`. -/
def prespecifiedBatchRawCubicRemainderEnvelope
    (theta h : RLSVector 3) (K : Nat) : Real :=
  (prespecifiedBatchTotalObservations K : Real) * (2 / 3 : Real) *
    (prespecifiedBatchScoreEnvelope theta h /
      Real.sqrt (prespecifiedBatchTotalObservations K : Real)) ^ 3

theorem prespecifiedBatchRawCubicRemainderEnvelope_eventually_eq
    (theta h : RLSVector 3) :
    prespecifiedBatchRawCubicRemainderEnvelope theta h =ᶠ[atTop]
      prespecifiedBatchCubicRemainderEnvelope theta h := by
  filter_upwards [eventually_gt_atTop (0 : Nat)] with K hK
  have htotal := prespecifiedBatchTotalObservations_pos K hK
  have hs : Real.sqrt
      (prespecifiedBatchTotalObservations K : Real) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast htotal))
  have hsq : Real.sqrt
      (prespecifiedBatchTotalObservations K : Real) ^ 2 =
        (prespecifiedBatchTotalObservations K : Real) :=
    Real.sq_sqrt (by positivity)
  unfold prespecifiedBatchRawCubicRemainderEnvelope
    prespecifiedBatchCubicRemainderEnvelope mixedLocalScale
  field_simp [hs]
  rw [hsq]
  ring

theorem prespecifiedBatchRawCubicRemainderEnvelope_tendsto_zero
    (theta h : RLSVector 3) :
    Tendsto (prespecifiedBatchRawCubicRemainderEnvelope theta h)
      atTop (nhds 0) :=
  (prespecifiedBatchCubicRemainderEnvelope_tendsto_zero theta h).congr'
    (prespecifiedBatchRawCubicRemainderEnvelope_eventually_eq theta h).symm

/-- Once the common one-shot envelope is at most `1/2`, the actual cumulative
Taylor remainder is bounded pathwise by the raw cubic envelope. -/
theorem prespecifiedBatchCumulativeTaylorRemainder_abs_le_rawEnvelope
    (theta h b : RLSVector 3) (hInterior : MixedPilotStrictInterior theta)
    (K : Nat) (hK : 0 < K)
    (hsmall : prespecifiedBatchScoreEnvelope theta h /
        Real.sqrt (prespecifiedBatchTotalObservations K : Real) ≤ 1 / 2)
    (x : PrespecifiedBatchFinitePrefix K) :
    |prespecifiedBatchCumulativeTaylorRemainder theta h b K x| ≤
      prespecifiedBatchRawCubicRemainderEnvelope theta h K := by
  classical
  let C : Real := (2 / 3 : Real) *
    (prespecifiedBatchScoreEnvelope theta h /
      Real.sqrt (prespecifiedBatchTotalObservations K : Real)) ^ 3
  have hpilot (j : Fin 3) (outcome : Bool) :
      |logThirdOrderRemainder
        (prespecifiedBatchPilotNormalizedScore theta h K j outcome)| ≤ C := by
    have hx := prespecifiedBatchPilotNormalizedScore_abs_le
      theta h hInterior K hK j outcome
    have hcube := pow_le_pow_left₀ (abs_nonneg _) hx 3
    unfold C
    exact (logThirdOrderRemainder_le_twoThirds _ (hx.trans hsmall)).trans
      (mul_le_mul_of_nonneg_left hcube (by norm_num))
  have hfinal (k : Finset.range K)
      (row : ExactConcretePredeterminedBatchRow k.1)
      (t : Fin (3 * exactConcreteBatchFinalBlocks k.1)) :
      |logThirdOrderRemainder
        (prespecifiedBatchFinalNormalizedScore theta h b K k row t)| ≤ C := by
    have hx := prespecifiedBatchFinalNormalizedScore_abs_le
      theta h b hInterior K hK k row t
    have hcube := pow_le_pow_left₀ (abs_nonneg _) hx 3
    unfold C
    exact (logThirdOrderRemainder_le_twoThirds _ (hx.trans hsmall)).trans
      (mul_le_mul_of_nonneg_left hcube (by norm_num))
  unfold prespecifiedBatchCumulativeTaylorRemainder
  let R : Finset.range K → Real := fun k =>
    ((∑ s : Fin (exactConcreteBatchPilotBlocks k.1),
        ∑ j : Fin 3,
          logThirdOrderRemainder
            (prespecifiedBatchPilotNormalizedScore theta h K j
              ((x k).1 s j))) +
      ∑ t : Fin (3 * exactConcreteBatchFinalBlocks k.1),
        logThirdOrderRemainder
          (prespecifiedBatchFinalNormalizedScore theta h b K k (x k) t))
  change |∑ k : Finset.range K, R k| ≤
    prespecifiedBatchRawCubicRemainderEnvelope theta h K
  calc
    |∑ k : Finset.range K, R k| ≤
        ∑ k : Finset.range K, |R k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Finset.range K,
          ((3 * exactConcreteBatchPilotBlocks k.1 : Nat) * C +
            (3 * exactConcreteBatchFinalBlocks k.1 : Nat) * C) := by
      apply Finset.sum_le_sum
      intro k _
      let P : Real :=
            ∑ s : Fin (exactConcreteBatchPilotBlocks k.1),
              ∑ j : Fin 3,
                logThirdOrderRemainder
                  (prespecifiedBatchPilotNormalizedScore theta h K j
                    ((x k).1 s j))
      let F : Real :=
            ∑ t : Fin (3 * exactConcreteBatchFinalBlocks k.1),
              logThirdOrderRemainder
                (prespecifiedBatchFinalNormalizedScore theta h b K k (x k) t)
      change |P + F| ≤
        (3 * exactConcreteBatchPilotBlocks k.1 : Nat) * C +
          (3 * exactConcreteBatchFinalBlocks k.1 : Nat) * C
      calc
        |P + F| ≤ |P| + |F| := abs_add_le _ _
        _ ≤ (3 * exactConcreteBatchPilotBlocks k.1 : Nat) * C +
            (3 * exactConcreteBatchFinalBlocks k.1 : Nat) * C := by
          gcongr
          · calc
                  |P| = |∑ s : Fin (exactConcreteBatchPilotBlocks k.1),
                      ∑ j : Fin 3,
                        logThirdOrderRemainder
                          (prespecifiedBatchPilotNormalizedScore theta h K j
                            ((x k).1 s j))| := rfl
                  _ ≤ ∑ s : Fin (exactConcreteBatchPilotBlocks k.1),
                        |∑ j : Fin 3,
                          logThirdOrderRemainder
                            (prespecifiedBatchPilotNormalizedScore theta h K j
                              ((x k).1 s j))| :=
                    Finset.abs_sum_le_sum_abs _ _
                  _ ≤
                      ∑ s : Fin (exactConcreteBatchPilotBlocks k.1),
                        ∑ j : Fin 3,
                          |logThirdOrderRemainder
                            (prespecifiedBatchPilotNormalizedScore theta h K j
                              ((x k).1 s j))| := by
                    apply Finset.sum_le_sum
                    intro s _
                    exact Finset.abs_sum_le_sum_abs _ _
                  _ ≤ ∑ s : Fin (exactConcreteBatchPilotBlocks k.1),
                        ∑ _j : Fin 3, C := by
                      gcongr with s j
                      exact hpilot j ((x k).1 s j)
                  _ = (3 * exactConcreteBatchPilotBlocks k.1 : Nat) * C := by
                      simp
                      ring
          · calc
                  |F| = |∑ t : Fin (3 * exactConcreteBatchFinalBlocks k.1),
                      logThirdOrderRemainder
                        (prespecifiedBatchFinalNormalizedScore theta h b K k
                          (x k) t)| := rfl
                  _ ≤
                      ∑ t : Fin (3 * exactConcreteBatchFinalBlocks k.1),
                        |logThirdOrderRemainder
                          (prespecifiedBatchFinalNormalizedScore theta h b K k
                            (x k) t)| := Finset.abs_sum_le_sum_abs _ _
                  _ ≤ ∑ _t : Fin (3 * exactConcreteBatchFinalBlocks k.1), C := by
                      gcongr with t
                      exact hfinal k (x k) t
                  _ = (3 * exactConcreteBatchFinalBlocks k.1 : Nat) * C := by simp
    _ = prespecifiedBatchRawCubicRemainderEnvelope theta h K := by
      unfold prespecifiedBatchRawCubicRemainderEnvelope
      rw [show
        (prespecifiedBatchTotalObservations K : Real) * (2 / 3 : Real) *
            (prespecifiedBatchScoreEnvelope theta h /
              Real.sqrt (prespecifiedBatchTotalObservations K : Real)) ^ 3 =
          (prespecifiedBatchTotalObservations K : Real) * C by
        dsimp [C]
        ring]
      calc
        (∑ k : Finset.range K,
          ((3 * exactConcreteBatchPilotBlocks k.1 : Nat) * C +
            (3 * exactConcreteBatchFinalBlocks k.1 : Nat) * C)) =
            (∑ k : Finset.range K,
              (exactConcreteBatchSize k.1 : Real)) * C := by
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro k _
                have hcast :
                    ((3 * exactConcreteBatchPilotBlocks k.1 : Nat) : Real) +
                        ((3 * exactConcreteBatchFinalBlocks k.1 : Nat) : Real) =
                      (exactConcreteBatchSize k.1 : Real) := by
                  exact_mod_cast exactConcreteBatch_observation_count k.1
                linear_combination C * hcast
        _ = (prespecifiedBatchTotalObservations K : Real) * C := by
          congr 1
          have hsumNat :
              (∑ k : Finset.range K, exactConcreteBatchSize k.1) =
                prespecifiedBatchTotalObservations K := by
            unfold prespecifiedBatchTotalObservations cumulativeCount
            change
              (∑ k ∈ (Finset.univ : Finset (Finset.range K)),
                exactConcreteBatchSize k.1) =
              ∑ k ∈ Finset.range K, exactConcreteBatchSize k
            rw [show (Finset.univ : Finset (Finset.range K)) =
                (Finset.range K).attach by
                  exact Finset.univ_eq_attach (Finset.range K)]
            exact Finset.sum_attach _ _
          exact_mod_cast hsumNat

/-- The actual cumulative Taylor remainder converges uniformly over all
finite-prefix paths to zero. -/
theorem prespecifiedBatchCumulativeTaylorRemainder_uniform_tendsto_zero
    (theta h b : RLSVector 3) (hInterior : MixedPilotStrictInterior theta) :
    ∀ epsilon : Real, 0 < epsilon →
      ∀ᶠ K : Nat in atTop, ∀ x : PrespecifiedBatchFinitePrefix K,
        |prespecifiedBatchCumulativeTaylorRemainder theta h b K x| < epsilon := by
  intro epsilon hepsilon
  have hnorm : Tendsto
      (fun K => prespecifiedBatchScoreEnvelope theta h *
        mixedLocalScale prespecifiedBatchTotalObservations K)
      atTop (nhds 0) := by
    simpa using
      ((tendsto_const_nhds : Tendsto
        (fun _ : Nat => prespecifiedBatchScoreEnvelope theta h)
        atTop (nhds (prespecifiedBatchScoreEnvelope theta h))).mul
        prespecifiedBatchLocalScale_tendsto_zero)
  have hsmall := hnorm.eventually_lt_const (by norm_num : (0 : Real) < 1 / 2)
  have hraw :=
    (prespecifiedBatchRawCubicRemainderEnvelope_tendsto_zero theta h).eventually_lt_const
      hepsilon
  filter_upwards [hsmall, hraw, eventually_gt_atTop (0 : Nat)] with K hs hr hK
  intro x
  have hscale :
      prespecifiedBatchScoreEnvelope theta h /
          Real.sqrt (prespecifiedBatchTotalObservations K : Real) =
        prespecifiedBatchScoreEnvelope theta h *
          mixedLocalScale prespecifiedBatchTotalObservations K := by
    simp [mixedLocalScale, div_eq_mul_inv]
  exact (prespecifiedBatchCumulativeTaylorRemainder_abs_le_rawEnvelope
    theta h b hInterior K hK (by rw [hscale]; exact le_of_lt hs) x).trans_lt hr

/-- The literal pilot observed-information contribution is nonnegative and is
bounded pathwise by `E(theta,h)^2 Q_K / N_K`. -/
theorem prespecifiedBatchCumulativePilotObservedInformation_le_envelope
    (theta h : RLSVector 3) (hInterior : MixedPilotStrictInterior theta)
    (K : Nat) (hK : 0 < K) (x : PrespecifiedBatchFinitePrefix K) :
    0 ≤ prespecifiedBatchCumulativePilotObservedInformation theta h K x ∧
      prespecifiedBatchCumulativePilotObservedInformation theta h K x ≤
        prespecifiedBatchPilotQuadraticEnvelope theta h K := by
  classical
  have htotal := prespecifiedBatchTotalObservations_pos K hK
  have hs : Real.sqrt
      (prespecifiedBatchTotalObservations K : Real) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast htotal))
  have hsq : Real.sqrt
      (prespecifiedBatchTotalObservations K : Real) ^ 2 =
        (prespecifiedBatchTotalObservations K : Real) :=
    Real.sq_sqrt (by positivity)
  let D : Real :=
    (prespecifiedBatchScoreEnvelope theta h /
      Real.sqrt (prespecifiedBatchTotalObservations K : Real)) ^ 2
  have hshot (j : Fin 3) (outcome : Bool) :
      prespecifiedBatchPilotNormalizedScore theta h K j outcome ^ 2 ≤ D := by
    have hx := prespecifiedBatchPilotNormalizedScore_abs_le
      theta h hInterior K hK j outcome
    have hp := pow_le_pow_left₀ (abs_nonneg _) hx 2
    simpa [D, sq_abs] using hp
  constructor
  · unfold prespecifiedBatchCumulativePilotObservedInformation
    positivity
  · unfold prespecifiedBatchCumulativePilotObservedInformation
    calc
      (∑ k : Finset.range K,
        ∑ s : Fin (exactConcreteBatchPilotBlocks k.1),
          ∑ j : Fin 3,
            prespecifiedBatchPilotNormalizedScore theta h K j
              ((x k).1 s j) ^ 2) ≤
          ∑ k : Finset.range K,
            (3 * exactConcreteBatchPilotBlocks k.1 : Nat) * D := by
        apply Finset.sum_le_sum
        intro k _
        calc
          (∑ s : Fin (exactConcreteBatchPilotBlocks k.1),
            ∑ j : Fin 3,
              prespecifiedBatchPilotNormalizedScore theta h K j
                ((x k).1 s j) ^ 2) ≤
              ∑ s : Fin (exactConcreteBatchPilotBlocks k.1),
                ∑ _j : Fin 3, D := by
            gcongr with s j
            exact hshot j ((x k).1 s j)
          _ = (3 * exactConcreteBatchPilotBlocks k.1 : Nat) * D := by
            simp
            ring
      _ = prespecifiedBatchPilotQuadraticEnvelope theta h K := by
        have hpilotNat :
            (∑ k : Finset.range K,
              3 * exactConcreteBatchPilotBlocks k.1) =
              cumulativeCount exactConcreteBatchExplorationSize K := by
          unfold cumulativeCount exactConcreteBatchExplorationSize
          change
            (∑ k ∈ (Finset.univ : Finset (Finset.range K)),
              3 * exactConcreteBatchPilotBlocks k.1) =
              ∑ k ∈ Finset.range K, 3 * exactConcreteBatchPilotBlocks k
          rw [show (Finset.univ : Finset (Finset.range K)) =
              (Finset.range K).attach by
                exact Finset.univ_eq_attach (Finset.range K)]
          exact Finset.sum_attach (Finset.range K)
            (fun k : Nat => 3 * exactConcreteBatchPilotBlocks k)
        unfold prespecifiedBatchPilotQuadraticEnvelope D
        rw [← Finset.sum_mul]
        rw [show
          (∑ k : Finset.range K,
            ((3 * exactConcreteBatchPilotBlocks k.1 : Nat) : Real)) =
              (cumulativeCount exactConcreteBatchExplorationSize K : Real) by
          exact_mod_cast hpilotNat]
        unfold prespecifiedBatchScoreEnvelope
        field_simp [hs]
        rw [hsq]

/-- The actual pilot quadratic contribution converges uniformly over every
finite-prefix path to zero. -/
theorem prespecifiedBatchCumulativePilotObservedInformation_uniform_tendsto_zero
    (theta h : RLSVector 3) (hInterior : MixedPilotStrictInterior theta) :
    ∀ epsilon : Real, 0 < epsilon →
      ∀ᶠ K : Nat in atTop, ∀ x : PrespecifiedBatchFinitePrefix K,
        prespecifiedBatchCumulativePilotObservedInformation theta h K x <
          epsilon := by
  intro epsilon hepsilon
  have henv :=
    (prespecifiedBatchPilotQuadraticEnvelope_tendsto_zero theta h).eventually_lt_const
      hepsilon
  filter_upwards [henv, eventually_gt_atTop (0 : Nat)] with K hbound hK
  intro x
  exact (prespecifiedBatchCumulativePilotObservedInformation_le_envelope
    theta h hInterior K hK x).2.trans_lt hbound

/-! ## Pilot linear term under the exact finite-prefix law -/

/-- Chebyshev envelope for the literal cumulative pilot score. -/
def prespecifiedBatchPilotScoreTailRealEnvelope
    (theta h : RLSVector 3) (epsilon : Real) (K : Nat) : Real :=
  prespecifiedBatchPilotLinearVarianceEnvelope theta h K / epsilon ^ 2

/-- The unnormalized pilot score contributed by one complete batch row. -/
def prespecifiedBatchPilotRowDirectionalScore
    (theta h : RLSVector 3) (k : Nat)
    (row : ExactConcretePredeterminedBatchRow k) : Real :=
  mixedPilotDirectionalScore theta h row.1

/-- Under the exact finite-prefix experiment, the literal cumulative pilot
score satisfies the variance-scale Chebyshev bound.  This is a finite-product
calculation, not a CLT. -/
theorem prespecifiedBatchCumulativePilotNormalizedScore_tail_bound
    (theta h b : RLSVector 3)
    (hInterior : MixedPilotStrictInterior theta)
    (epsilon : Real) (hepsilon : 0 < epsilon) (K : Nat) (hK : 0 < K) :
    prespecifiedBatchPrefixMeasure theta b K
        {x : PrespecifiedBatchFinitePrefix K |
          epsilon ≤
            |prespecifiedBatchCumulativePilotNormalizedScore theta h K x|} ≤
      ENNReal.ofReal
        (prespecifiedBatchPilotScoreTailRealEnvelope theta h epsilon K) := by
  classical
  have hphysical := mixedPilotStrictInterior_physical theta hInterior
  let rowMeasure : (k : Finset.range K) →
      Measure (ExactConcretePredeterminedBatchRow k.1) :=
    fun k => exactConcretePredeterminedBatchRowMeasure theta b k.1
  let Xrow : (k : Finset.range K) →
      ExactConcretePredeterminedBatchRow k.1 → Real :=
    fun k row => prespecifiedBatchPilotRowDirectionalScore theta h k.1 row
  let mu : Measure (PrespecifiedBatchFinitePrefix K) := Measure.pi rowMeasure
  let X : PrespecifiedBatchFinitePrefix K → Real :=
    fun x => ∑ k : Finset.range K, Xrow k (x k)
  letI : ∀ k : Finset.range K, IsProbabilityMeasure (rowMeasure k) :=
    fun k => exactConcretePredeterminedBatchRowMeasure_isProbability
      theta b hphysical k.1
  letI : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  have hmemRow : ∀ k : Finset.range K,
      MemLp (Xrow k) 2 (rowMeasure k) := by
    intro k
    refine MemLp.of_bound
      (measurable_of_finite (Xrow k)).aestronglyMeasurable
      ((exactConcreteBatchPilotBlocks k.1 : Real) *
        mixedPilotDirectionalEnvelope theta h) ?_
    exact Filter.Eventually.of_forall fun row => by
      rw [Real.norm_eq_abs]
      change
        |∑ s : Fin (exactConcreteBatchPilotBlocks k.1),
          mixedPilotBlockDirectionalScore theta h (row.1 s)| ≤
            (exactConcreteBatchPilotBlocks k.1 : Real) *
              mixedPilotDirectionalEnvelope theta h
      calc
        |∑ s : Fin (exactConcreteBatchPilotBlocks k.1),
            mixedPilotBlockDirectionalScore theta h (row.1 s)| ≤
            ∑ s : Fin (exactConcreteBatchPilotBlocks k.1),
              |mixedPilotBlockDirectionalScore theta h (row.1 s)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _s : Fin (exactConcreteBatchPilotBlocks k.1),
            mixedPilotDirectionalEnvelope theta h := by
          exact Finset.sum_le_sum fun s _ =>
            abs_mixedPilotBlockDirectionalScore_le
              theta h hInterior (row.1 s)
        _ = (exactConcreteBatchPilotBlocks k.1 : Real) *
            mixedPilotDirectionalEnvelope theta h := by simp
  have hmeanRow : ∀ k : Finset.range K,
      (∫ row, Xrow k row ∂rowMeasure k) = 0 := by
    intro k
    have hIntegralMap :
        (∫ pilot, mixedPilotDirectionalScore theta h pilot
          ∂(rowMeasure k).map (fun row => row.1)) =
        ∫ row, mixedPilotDirectionalScore theta h row.1
          ∂rowMeasure k := by
      exact integral_map
        (measurable_of_finite (fun row :
          ExactConcretePredeterminedBatchRow k.1 => row.1)).aemeasurable
        (measurable_of_finite
          (mixedPilotDirectionalScore (q :=
            exactConcreteBatchPilotBlocks k.1) theta h)).aestronglyMeasurable
    calc
      (∫ row, Xrow k row ∂rowMeasure k) =
          ∫ row, mixedPilotDirectionalScore theta h row.1
            ∂rowMeasure k := by rfl
      _ = ∫ pilot, mixedPilotDirectionalScore theta h pilot
          ∂(rowMeasure k).map (fun row => row.1) := hIntegralMap.symm
      _ = ∫ pilot, mixedPilotDirectionalScore theta h pilot
          ∂pauliPilotBornProductMeasure
            (q := exactConcreteBatchPilotBlocks k.1) theta := by
        rw [show (rowMeasure k).map (fun row => row.1) =
            pauliPilotBornProductMeasure
              (q := exactConcreteBatchPilotBlocks k.1) theta by
          exact exactConcretePredeterminedBatchRowMeasure_map_pilot
            theta b hphysical k.1]
      _ = 0 := mixedPilotDirectionalScore_mean_zero
        theta h hInterior
  have hvarianceRow : ∀ k : Finset.range K,
      variance (Xrow k) (rowMeasure k) ≤
        (exactConcreteBatchPilotBlocks k.1 : Real) *
          mixedPilotScoreVarianceConstant theta h := by
    intro k
    have hXrow :
        Xrow k =
          mixedPilotDirectionalScore (q :=
            exactConcreteBatchPilotBlocks k.1) theta h ∘
              (fun row : ExactConcretePredeterminedBatchRow k.1 => row.1) := by
      funext row
      rfl
    have hmap := variance_map
      (X := mixedPilotDirectionalScore (q :=
        exactConcreteBatchPilotBlocks k.1) theta h)
      (μ := rowMeasure k)
      (Y := fun row : ExactConcretePredeterminedBatchRow k.1 => row.1)
      (measurable_of_finite
        (mixedPilotDirectionalScore (q :=
          exactConcreteBatchPilotBlocks k.1) theta h)).aemeasurable
      (measurable_of_finite (fun row :
        ExactConcretePredeterminedBatchRow k.1 => row.1)).aemeasurable
    rw [show (rowMeasure k).map (fun row => row.1) =
        pauliPilotBornProductMeasure
          (q := exactConcreteBatchPilotBlocks k.1) theta by
      exact exactConcretePredeterminedBatchRowMeasure_map_pilot
        theta b hphysical k.1] at hmap
    rw [hXrow, ← hmap]
    exact mixedPilotDirectionalScore_variance_le theta h hInterior
  have hmemComp : ∀ k : Finset.range K,
      MemLp (fun x : PrespecifiedBatchFinitePrefix K => Xrow k (x k))
        2 mu := by
    intro k
    exact (hmemRow k).comp_measurePreserving
      (measurePreserving_eval rowMeasure k)
  have hmemX : MemLp X 2 mu := by
    have hsum := memLp_finsetSum
      (p := (2 : ENNReal)) (μ := mu)
      (Finset.univ : Finset (Finset.range K))
      (fun k _ => hmemComp k)
    simpa [X] using hsum
  have hmeanX : (∫ x, X x ∂mu) = 0 := by
    calc
      (∫ x, X x ∂mu) = ∑ k : Finset.range K,
          ∫ x, Xrow k (x k) ∂mu := by
        have hsum := integral_finsetSum
          (μ := mu) (Finset.univ : Finset (Finset.range K))
          (fun k _ => (hmemComp k).integrable (by norm_num))
        simpa [X] using hsum
      _ = ∑ k : Finset.range K,
          ∫ row, Xrow k row ∂rowMeasure k := by
        apply Finset.sum_congr rfl
        intro k _
        exact integral_comp_eval (hmemRow k).aestronglyMeasurable
      _ = 0 := by simp [hmeanRow]
  have hvarianceX :
      variance X mu =
        ∑ k : Finset.range K, variance (Xrow k) (rowMeasure k) := by
    change variance X (Measure.pi rowMeasure) =
      ∑ k : Finset.range K, variance (Xrow k) (rowMeasure k)
    rw [show X = ∑ k : Finset.range K,
        (fun x : PrespecifiedBatchFinitePrefix K => Xrow k (x k)) by
      funext x
      simp [X]]
    exact variance_sum_pi (μ := rowMeasure) hmemRow
  have hpilotNat :
      (∑ k : Finset.range K,
        3 * exactConcreteBatchPilotBlocks k.1) =
        cumulativeCount exactConcreteBatchExplorationSize K := by
    unfold cumulativeCount exactConcreteBatchExplorationSize
    change
      (∑ k ∈ (Finset.univ : Finset (Finset.range K)),
        3 * exactConcreteBatchPilotBlocks k.1) =
        ∑ k ∈ Finset.range K, 3 * exactConcreteBatchPilotBlocks k
    rw [show (Finset.univ : Finset (Finset.range K)) =
        (Finset.range K).attach by
      exact Finset.univ_eq_attach (Finset.range K)]
    exact Finset.sum_attach (Finset.range K)
      (fun k : Nat => 3 * exactConcreteBatchPilotBlocks k)
  have hblocksReal :
      (∑ k : Finset.range K,
        (exactConcreteBatchPilotBlocks k.1 : Real)) =
        (cumulativeCount exactConcreteBatchExplorationSize K : Real) / 3 := by
    have hthree :
        3 * (∑ k : Finset.range K,
          (exactConcreteBatchPilotBlocks k.1 : Real)) =
          (cumulativeCount exactConcreteBatchExplorationSize K : Real) := by
      have hcast :
          (∑ k : Finset.range K,
            ((3 * exactConcreteBatchPilotBlocks k.1 : Nat) : Real)) =
            (cumulativeCount exactConcreteBatchExplorationSize K : Real) := by
        exact_mod_cast hpilotNat
      calc
        3 * (∑ k : Finset.range K,
            (exactConcreteBatchPilotBlocks k.1 : Real)) =
            ∑ k : Finset.range K,
              3 * (exactConcreteBatchPilotBlocks k.1 : Real) := by
          rw [Finset.mul_sum]
        _ = ∑ k : Finset.range K,
            ((3 * exactConcreteBatchPilotBlocks k.1 : Nat) : Real) := by
          apply Finset.sum_congr rfl
          intro k _
          norm_num
        _ = (cumulativeCount exactConcreteBatchExplorationSize K : Real) :=
          hcast
    linarith
  have hvarianceX_le :
      variance X mu ≤
        mixedPilotScoreVarianceConstant theta h *
          ((cumulativeCount exactConcreteBatchExplorationSize K : Real) / 3) := by
    rw [hvarianceX]
    calc
      (∑ k : Finset.range K, variance (Xrow k) (rowMeasure k)) ≤
          ∑ k : Finset.range K,
            (exactConcreteBatchPilotBlocks k.1 : Real) *
              mixedPilotScoreVarianceConstant theta h := by
        exact Finset.sum_le_sum fun k _ => hvarianceRow k
      _ = mixedPilotScoreVarianceConstant theta h *
          ((cumulativeCount exactConcreteBatchExplorationSize K : Real) / 3) := by
        rw [← Finset.sum_mul, hblocksReal]
        ring
  have htotal := prespecifiedBatchTotalObservations_pos K hK
  have hsqrt : 0 < Real.sqrt
      (prespecifiedBatchTotalObservations K : Real) :=
    Real.sqrt_pos.2 (by exact_mod_cast htotal)
  have hscoreEq (x : PrespecifiedBatchFinitePrefix K) :
      prespecifiedBatchCumulativePilotNormalizedScore theta h K x =
        X x / Real.sqrt (prespecifiedBatchTotalObservations K : Real) := by
    simp only [prespecifiedBatchCumulativePilotNormalizedScore,
      prespecifiedBatchPilotNormalizedScore, X, Xrow,
      prespecifiedBatchPilotRowDirectionalScore,
      mixedPilotDirectionalScore, mixedPilotBlockDirectionalScore]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.sum_div]
  have hevent :
      {x : PrespecifiedBatchFinitePrefix K |
        epsilon ≤
          |prespecifiedBatchCumulativePilotNormalizedScore theta h K x|} =
      {x : PrespecifiedBatchFinitePrefix K |
        epsilon * Real.sqrt (prespecifiedBatchTotalObservations K : Real) ≤
          |X x - mu[X]|} := by
    ext x
    change
      epsilon ≤
          |prespecifiedBatchCumulativePilotNormalizedScore theta h K x| ↔
        epsilon * Real.sqrt (prespecifiedBatchTotalObservations K : Real) ≤
          |X x - ∫ y, X y ∂mu|
    rw [hscoreEq, hmeanX, sub_zero, abs_div, abs_of_pos hsqrt]
    exact le_div_iff₀ hsqrt
  have hchebyshev := meas_ge_le_variance_div_sq hmemX
    (mul_pos hepsilon hsqrt)
  have hthresholdSquare :
      (epsilon * Real.sqrt
        (prespecifiedBatchTotalObservations K : Real)) ^ 2 =
        epsilon ^ 2 * (prespecifiedBatchTotalObservations K : Real) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hreal :
      variance X mu /
          (epsilon * Real.sqrt
            (prespecifiedBatchTotalObservations K : Real)) ^ 2 ≤
        prespecifiedBatchPilotScoreTailRealEnvelope theta h epsilon K := by
    rw [hthresholdSquare]
    calc
      variance X mu /
          (epsilon ^ 2 * (prespecifiedBatchTotalObservations K : Real)) ≤
        (mixedPilotScoreVarianceConstant theta h *
            ((cumulativeCount exactConcreteBatchExplorationSize K : Real) / 3)) /
          (epsilon ^ 2 * (prespecifiedBatchTotalObservations K : Real)) :=
        div_le_div_of_nonneg_right hvarianceX_le (by positivity)
      _ = prespecifiedBatchPilotScoreTailRealEnvelope theta h epsilon K := by
        unfold prespecifiedBatchPilotScoreTailRealEnvelope
          prespecifiedBatchPilotLinearVarianceEnvelope
        have hN : (prespecifiedBatchTotalObservations K : Real) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt htotal)
        field_simp [hN]
  change mu
      {x : PrespecifiedBatchFinitePrefix K |
        epsilon ≤
          |prespecifiedBatchCumulativePilotNormalizedScore theta h K x|} ≤
    ENNReal.ofReal
      (prespecifiedBatchPilotScoreTailRealEnvelope theta h epsilon K)
  rw [hevent]
  exact hchebyshev.trans (ENNReal.ofReal_le_ofReal hreal)

/-- The literal cumulative pilot linear term converges to zero in probability
under the exact finite-prefix Born laws. -/
theorem prespecifiedBatchCumulativePilotNormalizedScore_convergesInProbability
    (theta h b : RLSVector 3)
    (hInterior : MixedPilotStrictInterior theta) :
    ∀ epsilon : Real, 0 < epsilon →
      Tendsto
        (fun K : Nat =>
          prespecifiedBatchPrefixMeasure theta b K
            {x : PrespecifiedBatchFinitePrefix K |
              epsilon ≤
                |prespecifiedBatchCumulativePilotNormalizedScore
                  theta h K x|})
        atTop (nhds 0) := by
  intro epsilon hepsilon
  have hreal :
      Tendsto
        (prespecifiedBatchPilotScoreTailRealEnvelope theta h epsilon)
        atTop (nhds 0) := by
    unfold prespecifiedBatchPilotScoreTailRealEnvelope
    simpa using
      (prespecifiedBatchPilotLinearVarianceEnvelope_tendsto_zero
        theta h).div_const (epsilon ^ 2)
  have hENN :
      Tendsto
        (fun K : Nat => ENNReal.ofReal
          (prespecifiedBatchPilotScoreTailRealEnvelope theta h epsilon K))
        atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hreal
  apply Tendsto.squeeze' tendsto_const_nhds hENN
  · exact Filter.Eventually.of_forall fun _ => bot_le
  · filter_upwards [eventually_gt_atTop (0 : Nat)] with K hK
    exact prespecifiedBatchCumulativePilotNormalizedScore_tail_bound
      theta h b hInterior epsilon hepsilon K hK

/-- Exact likelihood algebra, cubic control, and both pilot negligibility
arguments are closed.  Only final random information convergence and the
final score CLT remain outside this module. -/
theorem prespecifiedBatchLikelihoodExpansion_deterministicClosure
    (theta h : RLSVector 3) :
    Tendsto (prespecifiedBatchCubicRemainderEnvelope theta h)
        atTop (nhds 0) ∧
      Tendsto (prespecifiedBatchPilotQuadraticEnvelope theta h)
        atTop (nhds 0) ∧
      Tendsto (prespecifiedBatchPilotLinearVarianceEnvelope theta h)
        atTop (nhds 0) :=
  ⟨prespecifiedBatchCubicRemainderEnvelope_tendsto_zero theta h,
    prespecifiedBatchPilotQuadraticEnvelope_tendsto_zero theta h,
    prespecifiedBatchPilotLinearVarianceEnvelope_tendsto_zero theta h⟩

end

end QubitOracle.Paper
