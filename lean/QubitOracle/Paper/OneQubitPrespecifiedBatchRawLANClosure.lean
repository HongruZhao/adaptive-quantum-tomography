import QubitOracle.Paper.OneQubitPrespecifiedBatchFiniteExperiment
import QubitOracle.Paper.OneQubitPrespecifiedBatchLikelihoodExpansion
import QubitOracle.Paper.OneQubitPrespecifiedBatchCumulativeInformationClosure
import QubitOracle.Paper.OneQubitPrespecifiedBatchMartingaleCertificateClosure
import QubitOracle.Paper.OneQubitPrespecifiedBatchObservedInformationClosure
import QubitOracle.Paper.OneQubitPrespecifiedBatchOrthogonalLANTransfer
import QubitOracle.Paper.OneQubitCramerWoldBridge

/-!
# Raw LAN closure for the prespecified-batch mixed-qubit experiment

The score is a genuine three-coordinate statistic of the finite prefix.
Every directional projection is exactly the cumulative pilot-plus-final
likelihood score. The final part is supplied by the concrete Hall--Heyde
certificate; the pilot is transported on the common infinite Born path.
-/

noncomputable section

open Filter MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators ENNReal NNReal Topology RealInnerProductSpace

namespace QubitOracle.Paper

attribute [local instance]
  pauliPilotBornPathMeasurableSpace
  mixedTwoStageFiniteRowMeasurableSpace
  mixedTwoStageFiniteRowMeasurableSingletonClass

open PrespecifiedBatchMartingaleClosure

/-! ## Exact final-score normalization and scalar CLT -/

def rawLANFinRangeEquiv (K : Nat) :
    Fin K ≃ Finset.range K where
  toFun k := ⟨k, Finset.mem_range.2 k.2⟩
  invFun k := ⟨k, Finset.mem_range.1 k.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem prespecifiedBatchFinalNormalizedScore_eq_scaled
    (theta h b : RLSVector 3) (K : Nat) (k : Fin K)
    (row : ExactConcretePredeterminedBatchRow k.1)
    (t : Fin (3 * exactConcreteBatchFinalBlocks k.1)) :
    prespecifiedBatchFinalNormalizedScore theta h b K
        ⟨k.1, Finset.mem_range.2 k.2⟩ row t =
      prespecifiedBatchCumulativeShotScale K k *
        mixedExactCycleNormalizedDirectionalScore theta h
          (exactConcreteBatchSelectedFrame k.1 b) row.1 t row.2 := by
  unfold prespecifiedBatchFinalNormalizedScore
    prespecifiedBatchFinalDirection
    prespecifiedBatchCumulativeShotScale
    prespecifiedBatchSampleScale
    exactConcreteBatchExploitationSize
    mixedExactCycleNormalizedDirectionalScore
    mixedTwoStageFinalPathDirectionalScore
    mixedTwoStageFinalShotDirectionalScore
    mixedTwoStageAxisDirectionalScore
  simp only [QubitOracle.blochDot, Finset.mul_sum]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  rw [← Finset.mul_sum]
  rw [← Finset.mul_sum]
  rw [← Finset.mul_sum]
  ring

def prespecifiedBatchCumulativeFinalScoreOnPrefix
    (theta h b : RLSVector 3) (K : Nat)
    (x : PrespecifiedBatchFinitePrefix K) : Real :=
  ∑ k : Fin K,
    ∑ t : Fin (3 * exactConcreteBatchFinalBlocks k.1),
      prespecifiedBatchFinalNormalizedScore theta h b K
        ⟨k.1, Finset.mem_range.2 k.2⟩
        (x ⟨k.1, Finset.mem_range.2 k.2⟩) t

theorem prespecifiedBatchCumulativeFinalScoreOnPrefix_comp_restrict
    (theta h b : RLSVector 3) (K : Nat)
    (omega : ExactConcretePredeterminedBatchPath) :
    prespecifiedBatchCumulativeFinalScoreOnPrefix theta h b K
        ((Finset.range K).restrict omega) =
      hallHeydeDeterministicVarianceRowSum
        prespecifiedBatchCumulativeFinalRowLength
        (prespecifiedBatchCumulativeEnumeratedIncrement theta h b) K omega := by
  rw [prespecifiedBatchCumulativeRowSum_eq_batchSums]
  unfold prespecifiedBatchCumulativeFinalScoreOnPrefix
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  exact prespecifiedBatchFinalNormalizedScore_eq_scaled
    theta h b K k (omega k.1) t

theorem mixedPolynomialTruthFrameDirectionalInformation_nonnegative
    (theta h b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    0 <= mixedPolynomialTruthFrameDirectionalInformation theta h b := by
  rw [← mixedPolynomialTruthFrameInformationMatrix_quadratic theta h b]
  simpa [dotProduct] using
    (mixedPolynomialTruthFrameInformationMatrix_posDef
      theta b hTruth hSeed).posSemidef.dotProduct_mulVec_nonneg h

theorem prespecifiedBatchCumulativeFinalScore_CLT_closed
    (theta h b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    PrespecifiedBatchCumulativeFinalScoreCLT theta h b
      (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)
      (mixedPolynomialTruthFrameDirectionalInformation theta h b) := by
  exact prespecifiedBatchCumulativeFinalScore_CLT_of_hallHeyde
    theta h b
    (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)
    (mixedPolynomialTruthFrameDirectionalInformation theta h b)
    (mixedPolynomialTruthFrameDirectionalInformation_nonnegative
      theta h b hTruth hSeed)
    (prespecifiedBatchCumulativeMartingaleCertificate
      theta h b hTruth.2)
    (prespecifiedBatchCumulativeFisherConvergesInProbability_closed
      theta h b hTruth hSeed)

/-! ## Exact finite-prefix transport and pilot Slutsky closure -/

theorem prespecifiedBatchPrefixRestriction_measurable (K : Nat) :
    Measurable
      ((Finset.range K).restrict :
        ExactConcretePredeterminedBatchPath ->
          PrespecifiedBatchFinitePrefix K) := by
  fun_prop

theorem exactConcretePredeterminedBatchPathMeasure_map_prefix_eq
    (theta b : RLSVector 3)
    (hphysical : PauliPilotPhysicalBloch theta) (K : Nat) :
    (exactConcretePredeterminedBatchPathMeasure theta b hphysical).map
        (Finset.range K).restrict =
      prespecifiedBatchPrefixMeasure theta b K := by
  simpa [prespecifiedBatchPrefixMeasure] using
    (exactConcretePredeterminedBatchPathMeasure_map_prefix
      theta b hphysical K)

def prespecifiedBatchCumulativePilotScoreOnPath
    (theta h : RLSVector 3) (K : Nat) :
    ExactConcretePredeterminedBatchPath -> Real :=
  fun omega =>
    prespecifiedBatchCumulativePilotNormalizedScore theta h K
      ((Finset.range K).restrict omega)

theorem prespecifiedBatchCumulativePilotScoreOnPath_tendstoInMeasure_zero
    (theta h b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta) :
    TendstoInMeasure
      (exactConcretePredeterminedBatchPathMeasure theta b
        (mixedNonzeroInterior_pauliPilotPhysical theta hTruth))
      (prespecifiedBatchCumulativePilotScoreOnPath theta h)
      atTop (fun _ => (0 : Real)) := by
  rw [tendstoInMeasure_iff_norm]
  intro epsilon hepsilon
  have hpilot :=
    prespecifiedBatchCumulativePilotNormalizedScore_convergesInProbability
      theta h b hTruth.2 epsilon hepsilon
  convert hpilot using 1
  funext K
  let s : Set (PrespecifiedBatchFinitePrefix K) :=
    {x |
      epsilon <=
        |prespecifiedBatchCumulativePilotNormalizedScore theta h K x|}
  have hs : MeasurableSet s :=
    Set.Finite.measurableSet (Set.toFinite s)
  have hmap := Measure.map_apply
    (μ := exactConcretePredeterminedBatchPathMeasure theta b
      (mixedNonzeroInterior_pauliPilotPhysical theta hTruth))
    (prespecifiedBatchPrefixRestriction_measurable K) hs
  rw [exactConcretePredeterminedBatchPathMeasure_map_prefix_eq
    theta b (mixedNonzeroInterior_pauliPilotPhysical theta hTruth) K] at hmap
  simpa [s, prespecifiedBatchCumulativePilotScoreOnPath,
    Real.norm_eq_abs] using hmap.symm

def prespecifiedBatchCumulativeTotalScoreOnPath
    (theta h b : RLSVector 3) (K : Nat) :
    ExactConcretePredeterminedBatchPath -> Real :=
  fun omega =>
    hallHeydeDeterministicVarianceRowSum
        prespecifiedBatchCumulativeFinalRowLength
        (prespecifiedBatchCumulativeEnumeratedIncrement theta h b) K omega +
      prespecifiedBatchCumulativePilotScoreOnPath theta h K omega

def PrespecifiedBatchCumulativeTotalScoreCLT
    (theta h b : RLSVector 3)
    (hphysical : PauliPilotPhysicalBloch theta)
    (sigmaSq : Real) : Prop := by
  letI : IsProbabilityMeasure
      (exactConcretePredeterminedBatchPathMeasure theta b hphysical) :=
    exactConcretePredeterminedBatchPathMeasure_isProbability
      theta b hphysical
  letI : forall _ : Nat, IsProbabilityMeasure
      (exactConcretePredeterminedBatchPathMeasure theta b hphysical) :=
    fun _ => inferInstance
  exact TendstoInDistribution
    (prespecifiedBatchCumulativeTotalScoreOnPath theta h b)
    atTop (fun x => id x + 0)
    (fun _ => exactConcretePredeterminedBatchPathMeasure theta b hphysical)
    (gaussianReal 0 sigmaSq.toNNReal)

theorem prespecifiedBatchCumulativeTotalScoreOnPath_CLT
    (theta h b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    PrespecifiedBatchCumulativeTotalScoreCLT theta h b
      (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)
      (mixedPolynomialTruthFrameDirectionalInformation theta h b) := by
  unfold PrespecifiedBatchCumulativeTotalScoreCLT
  let hprob : IsProbabilityMeasure
      (exactConcretePredeterminedBatchPathMeasure theta b
        (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)) :=
    exactConcretePredeterminedBatchPathMeasure_isProbability
      theta b (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)
  letI : IsProbabilityMeasure
      (exactConcretePredeterminedBatchPathMeasure theta b
        (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)) :=
    hprob
  letI : forall _ : Nat, IsProbabilityMeasure
      (exactConcretePredeterminedBatchPathMeasure theta b
        (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)) :=
    fun _ => hprob
  have hfinal :=
    prespecifiedBatchCumulativeFinalScore_CLT_closed
      theta h b hTruth hSeed
  have hpilot :=
    prespecifiedBatchCumulativePilotScoreOnPath_tendstoInMeasure_zero
      theta h b hTruth
  have hsum := hfinal.add_of_tendstoInMeasure_const hpilot
    (fun K =>
      ((measurable_of_finite
        (prespecifiedBatchCumulativePilotNormalizedScore theta h K)).comp
          (prespecifiedBatchPrefixRestriction_measurable K)).aemeasurable)
  exact hsum

theorem prespecifiedBatchCumulativeNormalizedScore_eq_pilot_add_final
    (theta h b : RLSVector 3) (K : Nat)
    (x : PrespecifiedBatchFinitePrefix K) :
    prespecifiedBatchCumulativeNormalizedScore theta h b K x =
      prespecifiedBatchCumulativePilotNormalizedScore theta h K x +
        prespecifiedBatchCumulativeFinalScoreOnPrefix theta h b K x := by
  unfold prespecifiedBatchCumulativeNormalizedScore
    prespecifiedBatchCumulativePilotNormalizedScore
    prespecifiedBatchCumulativeFinalScoreOnPrefix
  rw [Finset.sum_add_distrib]
  congr 1
  exact (Fintype.sum_equiv (rawLANFinRangeEquiv K)
    (fun k : Fin K =>
      ∑ t : Fin (3 * exactConcreteBatchFinalBlocks k.1),
        prespecifiedBatchFinalNormalizedScore theta h b K
          ⟨k.1, Finset.mem_range.2 k.2⟩
          (x ⟨k.1, Finset.mem_range.2 k.2⟩) t)
    (fun k : Finset.range K =>
      ∑ t : Fin (3 * exactConcreteBatchFinalBlocks k.1),
        prespecifiedBatchFinalNormalizedScore theta h b K k (x k) t)
    (fun _ => rfl)).symm

theorem prespecifiedBatchCumulativeNormalizedScore_comp_restrict
    (theta h b : RLSVector 3) (K : Nat)
    (omega : ExactConcretePredeterminedBatchPath) :
    prespecifiedBatchCumulativeNormalizedScore theta h b K
        ((Finset.range K).restrict omega) =
      prespecifiedBatchCumulativeTotalScoreOnPath theta h b K omega := by
  rw [prespecifiedBatchCumulativeNormalizedScore_eq_pilot_add_final,
    prespecifiedBatchCumulativeFinalScoreOnPrefix_comp_restrict]
  simp [prespecifiedBatchCumulativeTotalScoreOnPath,
    prespecifiedBatchCumulativePilotScoreOnPath, add_comm]

/-! ## Direction-independent finite-prefix vector score -/

theorem prespecifiedBatchPilotNormalizedScore_basis_projection
    (theta h : RLSVector 3) (K : Nat)
    (j : Fin 3) (outcome : Bool) :
    dotProduct h (fun i =>
      prespecifiedBatchPilotNormalizedScore theta (standardBasis3 i)
        K j outcome) =
      prespecifiedBatchPilotNormalizedScore theta h K j outcome := by
  unfold prespecifiedBatchPilotNormalizedScore
    mixedPilotOneShotDirectionalScore
  fin_cases j <;>
    simp [dotProduct, standardBasis3, Fin.sum_univ_succ] <;> ring

theorem prespecifiedBatchFinalNormalizedScore_basis_projection
    (theta h b : RLSVector 3) (K : Nat) (k : Finset.range K)
    (row : ExactConcretePredeterminedBatchRow k.1)
    (t : Fin (3 * exactConcreteBatchFinalBlocks k.1)) :
    dotProduct h (fun i =>
      prespecifiedBatchFinalNormalizedScore theta (standardBasis3 i)
        b K k row t) =
      prespecifiedBatchFinalNormalizedScore theta h b K k row t := by
  unfold prespecifiedBatchFinalNormalizedScore
    prespecifiedBatchFinalDirection
    mixedExactCycleNormalizedDirectionalScore
    mixedTwoStageFinalPathDirectionalScore
    mixedTwoStageFinalShotDirectionalScore
    mixedTwoStageAxisDirectionalScore
  simp [dotProduct, standardBasis3, QubitOracle.blochDot,
    Fin.sum_univ_succ]
  ring

def prespecifiedBatchRawVectorScore
    (theta b : RLSVector 3) (K : Nat)
    (x : PrespecifiedBatchFinitePrefix K) : HajekParameter (Fin 3) :=
  fun i =>
    prespecifiedBatchCumulativeNormalizedScore theta
      (standardBasis3 i) b K x

set_option maxRecDepth 10000 in
theorem prespecifiedBatchRawVectorScore_projection
    (theta h b : RLSVector 3) (K : Nat)
    (x : PrespecifiedBatchFinitePrefix K) :
    dotProduct h (prespecifiedBatchRawVectorScore theta b K x) =
      prespecifiedBatchCumulativeNormalizedScore theta h b K x := by
  unfold prespecifiedBatchRawVectorScore
    prespecifiedBatchCumulativeNormalizedScore
  simp only [dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  · simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    exact prespecifiedBatchPilotNormalizedScore_basis_projection
      theta h K j ((x k).1 s j)
  · simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t ht
    exact prespecifiedBatchFinalNormalizedScore_basis_projection
      theta h b K k (x k) t

theorem prespecifiedBatchRawVectorScore_measurable
    (theta b : RLSVector 3) (K : Nat) (i : Fin 3) :
    Measurable (fun x : PrespecifiedBatchFinitePrefix K =>
      prespecifiedBatchRawVectorScore theta b K x i) :=
  measurable_of_finite _

/-! ## Finite-prefix score law and Hajek characteristic convergence -/

def PrespecifiedBatchCumulativePrefixScoreCLT
    (theta h b : RLSVector 3)
    (hphysical : PauliPilotPhysicalBloch theta)
    (sigmaSq : Real) : Prop := by
  letI : forall K : Nat,
      IsProbabilityMeasure (prespecifiedBatchPrefixMeasure theta b K) :=
    fun K => prespecifiedBatchPrefixMeasure_isProbability
      theta b hphysical K
  exact TendstoInDistribution
    (fun K x =>
      prespecifiedBatchCumulativeNormalizedScore theta h b K x)
    atTop id
    (fun K => prespecifiedBatchPrefixMeasure theta b K)
    (gaussianReal 0 sigmaSq.toNNReal)

theorem prespecifiedBatchCumulativePrefixScore_CLT
    (theta h b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    PrespecifiedBatchCumulativePrefixScoreCLT theta h b
      (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)
      (mixedPolynomialTruthFrameDirectionalInformation theta h b) := by
  let hphysical := mixedNonzeroInterior_pauliPilotPhysical theta hTruth
  let pathMu := exactConcretePredeterminedBatchPathMeasure theta b hphysical
  let hpathProb : IsProbabilityMeasure pathMu :=
    exactConcretePredeterminedBatchPathMeasure_isProbability
      theta b hphysical
  letI : IsProbabilityMeasure pathMu := hpathProb
  letI : forall _ : Nat, IsProbabilityMeasure pathMu :=
    fun _ => hpathProb
  letI : forall K : Nat,
      IsProbabilityMeasure (prespecifiedBatchPrefixMeasure theta b K) :=
    fun K => prespecifiedBatchPrefixMeasure_isProbability
      theta b hphysical K
  have hpath :=
    prespecifiedBatchCumulativeTotalScoreOnPath_CLT
      theta h b hTruth hSeed
  unfold PrespecifiedBatchCumulativeTotalScoreCLT at hpath
  unfold PrespecifiedBatchCumulativePrefixScoreCLT
  refine
    { forall_aemeasurable := fun K =>
        (measurable_of_finite _).aemeasurable
      aemeasurable_limit := measurable_id.aemeasurable
      tendsto := ?_ }
  have hsource :
      (fun K =>
        (⟨(prespecifiedBatchPrefixMeasure theta b K).map
            (prespecifiedBatchCumulativeNormalizedScore theta h b K),
          Measure.isProbabilityMeasure_map
            (measurable_of_finite _).aemeasurable⟩ :
          ProbabilityMeasure Real)) =
      (fun K =>
        (⟨pathMu.map
            (prespecifiedBatchCumulativeTotalScoreOnPath theta h b K),
          Measure.isProbabilityMeasure_map
            (hpath.forall_aemeasurable K)⟩ :
          ProbabilityMeasure Real)) := by
    funext K
    apply ProbabilityMeasure.toMeasure_injective
    have hrestrict := prespecifiedBatchPrefixRestriction_measurable K
    have hscore :
        Measurable
          (prespecifiedBatchCumulativeNormalizedScore theta h b K) :=
      measurable_of_finite _
    calc
      (prespecifiedBatchPrefixMeasure theta b K).map
          (prespecifiedBatchCumulativeNormalizedScore theta h b K) =
          (pathMu.map (Finset.range K).restrict).map
            (prespecifiedBatchCumulativeNormalizedScore theta h b K) := by
            rw [exactConcretePredeterminedBatchPathMeasure_map_prefix_eq
              theta b hphysical K]
      _ = pathMu.map
          (prespecifiedBatchCumulativeNormalizedScore theta h b K ∘
            (Finset.range K).restrict) := by
            rw [MeasureTheory.Measure.map_map hscore hrestrict]
      _ = pathMu.map
          (prespecifiedBatchCumulativeTotalScoreOnPath theta h b K) := by
            apply Measure.map_congr
            filter_upwards with omega
            exact prespecifiedBatchCumulativeNormalizedScore_comp_restrict
              theta h b K omega
  have htarget :
      (⟨(gaussianReal 0
          (mixedPolynomialTruthFrameDirectionalInformation
            theta h b).toNNReal).map id,
        Measure.isProbabilityMeasure_map measurable_id.aemeasurable⟩ :
        ProbabilityMeasure Real) =
      (⟨(gaussianReal 0
          (mixedPolynomialTruthFrameDirectionalInformation
            theta h b).toNNReal).map (fun x => id x + 0),
        Measure.isProbabilityMeasure_map
          (by fun_prop : AEMeasurable (fun x : Real => id x + 0)
            (gaussianReal 0
              (mixedPolynomialTruthFrameDirectionalInformation
                theta h b).toNNReal))⟩ :
        ProbabilityMeasure Real) := by
    apply ProbabilityMeasure.toMeasure_injective
    apply Measure.map_congr
    filter_upwards with x
    simp
  rw [hsource, htarget]
  exact hpath.tendsto

set_option maxHeartbeats 1000000 in
theorem prespecifiedBatchRawVectorScore_converges
    (theta b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    HajekScoreConvergesToGaussian
      (prespecifiedBatchHajekExperiment theta b hTruth) 0
      (mixedBuresTarget theta)
      (prespecifiedBatchRawVectorScore theta b) := by
  intro z
  let hphysical := mixedNonzeroInterior_pauliPilotPhysical theta hTruth
  letI : forall K : Nat,
      IsProbabilityMeasure (prespecifiedBatchPrefixMeasure theta b K) :=
    fun K => prespecifiedBatchPrefixMeasure_isProbability
      theta b hphysical K
  have hscalar :=
    prespecifiedBatchCumulativePrefixScore_CLT
      theta z b hTruth hSeed
  unfold PrespecifiedBatchCumulativePrefixScoreCLT at hscalar
  have hz :=
    (ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 hscalar.tendsto)
      (1 : Real)
  have htarget :
      charFun
          (gaussianReal 0
            (mixedPolynomialTruthFrameDirectionalInformation
              theta z b).toNNReal)
          (1 : Real) =
        Complex.exp
          (-((hajekQuadraticForm (mixedBuresTarget theta) z : Real) :
              Complex) / 2) := by
    have hinfo :=
      mixedPolynomialTruthFrameDirectionalInformation_nonnegative
        theta z b hTruth hSeed
    rw [ProbabilityTheory.charFun_gaussianReal]
    rw [Real.coe_toNNReal _ hinfo]
    rw [← mixedPolynomialTruthFrameInformationMatrix_quadratic theta z b,
      mixedPolynomialTruthFrameInformationMatrix_eq_mixedBuresTarget
        theta b hTruth hSeed]
    simp [hajekQuadraticForm, dotProduct]
    ring
  have hzGaussian :
      Tendsto
        (fun K =>
          charFun
            (⟨(prespecifiedBatchPrefixMeasure theta b K).map
                (prespecifiedBatchCumulativeNormalizedScore theta z b K),
              Measure.isProbabilityMeasure_map
                (measurable_of_finite _).aemeasurable⟩ :
              ProbabilityMeasure Real)
            (1 : Real))
        atTop
        (nhds
          (charFun
            (gaussianReal 0
              (mixedPolynomialTruthFrameDirectionalInformation
                theta z b).toNNReal)
            (1 : Real))) := by
    simpa using hz
  rw [htarget] at hzGaussian
  have hsource :
      (fun K =>
        charFun
          (⟨(prespecifiedBatchPrefixMeasure theta b K).map
              (prespecifiedBatchCumulativeNormalizedScore theta z b K),
            Measure.isProbabilityMeasure_map
              (measurable_of_finite _).aemeasurable⟩ :
            ProbabilityMeasure Real)
          (1 : Real)) =
      (fun K =>
        ∫ x : PrespecifiedBatchFinitePrefix K,
            Complex.exp
              (Complex.I *
                (dotProduct z
                  (prespecifiedBatchRawVectorScore theta b K x)))
          ∂((prespecifiedBatchHajekExperiment theta b hTruth).law K 0)) := by
    funext K
    rw [prespecifiedBatchHajekExperiment_baseLaw]
    change
      charFun
        ((prespecifiedBatchPrefixMeasure theta b K).map
          (prespecifiedBatchCumulativeNormalizedScore theta z b K))
        (1 : Real) = _
    rw [show
      charFun
          ((prespecifiedBatchPrefixMeasure theta b K).map
            (prespecifiedBatchCumulativeNormalizedScore theta z b K))
          (1 : Real) =
        ∫ y : Real, Complex.exp ((y : Complex) * Complex.I)
          ∂((prespecifiedBatchPrefixMeasure theta b K).map
            (prespecifiedBatchCumulativeNormalizedScore theta z b K)) by
          simp [charFun]]
    rw [MeasureTheory.integral_map
      (measurable_of_finite _).aemeasurable (by fun_prop)]
    apply integral_congr_ae
    filter_upwards with x
    rw [prespecifiedBatchRawVectorScore_projection]
    ring_nf
  rw [hsource] at hzGaussian
  change Tendsto
    (fun K =>
      ∫ x : PrespecifiedBatchFinitePrefix K,
        Complex.exp
          (Complex.I *
            ((dotProduct z
              (prespecifiedBatchRawVectorScore theta b K x) : Real) : Complex))
        ∂((prespecifiedBatchHajekExperiment theta b hTruth).law K 0))
    atTop
    (nhds
      (Complex.exp
        (-((hajekQuadraticForm (mixedBuresTarget theta) z : Real) :
          Complex) / 2)))
  simpa [mul_comm] using hzGaussian

/-! ## Exact likelihood expansion and raw LAN remainder -/

def prespecifiedBatchRawLANRemainder
    (theta b : RLSVector 3) (K : Nat)
    (h : HajekParameter (Fin 3))
    (x : PrespecifiedBatchFinitePrefix K) : Real :=
  -(prespecifiedBatchCumulativeObservedDirectionalInformation
      theta h b K x -
        mixedPolynomialTruthFrameDirectionalInformation theta h b) / 2 +
    prespecifiedBatchCumulativeTaylorRemainder theta h b K x

theorem prespecifiedBatchRawLANRemainder_measurable
    (theta b : RLSVector 3) (K : Nat)
    (h : HajekParameter (Fin 3)) :
    Measurable (prespecifiedBatchRawLANRemainder theta b K h) :=
  measurable_of_finite _

theorem mixedBuresTarget_posDef
    (theta b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    (mixedBuresTarget theta).PosDef := by
  rw [← mixedPolynomialTruthFrameInformationMatrix_eq_mixedBuresTarget
    theta b hTruth hSeed]
  exact mixedPolynomialTruthFrameInformationMatrix_posDef
    theta b hTruth hSeed

theorem prespecifiedBatchRawLAN_localParameter_eventually_mem
    (theta b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (h : HajekParameter (Fin 3)) :
    exists N, forall K, N <= K ->
      hajekLocalParameter 0 h K ∈
        (prespecifiedBatchHajekExperiment theta b hTruth).parameterSet :=
  ⟨0, fun _ _ => Set.mem_univ _⟩

set_option maxHeartbeats 800000 in
theorem prespecifiedBatchRawLAN_likelihood_ratio_expansion
    (theta b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (h : HajekParameter (Fin 3)) :
    exists N, forall K, N <= K ->
      forall x : PrespecifiedBatchFinitePrefix K,
        hajekLikelihoodRatio
            (prespecifiedBatchHajekExperiment theta b hTruth) K
            (hajekLocalParameter 0 h K) 0 x =
          Real.exp
            (dotProduct h (prespecifiedBatchRawVectorScore theta b K x) -
              (1 / 2) *
                hajekQuadraticForm (mixedBuresTarget theta) h +
              prespecifiedBatchRawLANRemainder theta b K h x) := by
  obtain ⟨Krn, hRN⟩ :=
    prespecifiedBatchHajekLikelihoodRatio_eventually_eq_productMassRatio
      theta b h hTruth
  obtain ⟨Keta, hEta⟩ := eventually_atTop.1
    (prespecifiedBatchLocalAlternative_eventually_strictInterior
      theta h hTruth)
  let N := max 1 (max Krn Keta)
  refine ⟨N, fun K hK x => ?_⟩
  have hKpos : 0 < K := lt_of_lt_of_le (by simp [N]) hK
  have hKrn : Krn <= K := le_trans
    (le_trans (le_max_left Krn Keta) (le_max_right 1 (max Krn Keta))) hK
  have hKeta : Keta <= K := le_trans
    (le_trans (le_max_right Krn Keta) (le_max_right 1 (max Krn Keta))) hK
  rw [hRN K hKrn x]
  have hexp :=
    prespecifiedBatchCumulativeLogLikelihood_exp_eq_productRowMassRatio
      theta h b hTruth.2 K (hEta K hKeta) x
  unfold prespecifiedBatchLocalParameter at hexp
  rw [← hexp]
  congr 1
  rw [prespecifiedBatchCumulativeLogLikelihood_exactTaylor
    theta h b hTruth.2 K hKpos x]
  rw [← prespecifiedBatchRawVectorScore_projection theta h b K x]
  unfold hajekQuadraticForm
  rw [← mixedPolynomialTruthFrameInformationMatrix_eq_mixedBuresTarget
      theta b hTruth hSeed,
    mixedPolynomialTruthFrameInformationMatrix_quadratic theta h b]
  unfold prespecifiedBatchRawLANRemainder
  ring

/-! ## Final remainder transfer -/

def PrespecifiedBatchObservedInformationConvergesInProbability
    (theta b : RLSVector 3) : Prop :=
  forall h : RLSVector 3, forall epsilon : Real, 0 < epsilon ->
    Tendsto
      (fun K =>
        (prespecifiedBatchPrefixMeasure theta b K)
          {x |
            epsilon <=
              |prespecifiedBatchCumulativeObservedDirectionalInformation
                  theta h b K x -
                mixedPolynomialTruthFrameDirectionalInformation theta h b|})
      atTop (nhds 0)

set_option maxHeartbeats 800000 in
theorem prespecifiedBatchRawLANRemainder_converges_of_observedInformation
    (theta b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hObserved :
      PrespecifiedBatchObservedInformationConvergesInProbability theta b) :
    HajekRemainderConvergesInProbability
      (prespecifiedBatchHajekExperiment theta b hTruth) 0
      (prespecifiedBatchRawLANRemainder theta b) := by
  intro h epsilon hepsilon
  simp only [prespecifiedBatchHajekExperiment,
    prespecifiedBatchHajekSafePhysicalParameter_zero theta hTruth]
  have htaylor :=
    prespecifiedBatchCumulativeTaylorRemainder_uniform_tendsto_zero
      theta h b hTruth.2 (epsilon / 2) (half_pos hepsilon)
  have hobs := hObserved h epsilon hepsilon
  apply Tendsto.squeeze' tendsto_const_nhds hobs
  · filter_upwards
    intro K
    exact bot_le
  · filter_upwards [htaylor] with K hTaylor
    change
      (prespecifiedBatchPrefixMeasure theta b K)
          {x : PrespecifiedBatchFinitePrefix K |
            epsilon <= |prespecifiedBatchRawLANRemainder theta b K h x|} <=
        (prespecifiedBatchPrefixMeasure theta b K)
          {x : PrespecifiedBatchFinitePrefix K |
            epsilon <=
              |prespecifiedBatchCumulativeObservedDirectionalInformation
                  theta h b K x -
                mixedPolynomialTruthFrameDirectionalInformation theta h b|}
    apply measure_mono
    intro x hx
    by_contra hxObs
    have hdiff :
        |prespecifiedBatchCumulativeObservedDirectionalInformation
              theta h b K x -
            mixedPolynomialTruthFrameDirectionalInformation theta h b| <
          epsilon := by
      simpa only [Set.mem_setOf_eq, not_le] using hxObs
    have hrem :
        |prespecifiedBatchRawLANRemainder theta b K h x| < epsilon := by
      unfold prespecifiedBatchRawLANRemainder
      calc
        |-(prespecifiedBatchCumulativeObservedDirectionalInformation
              theta h b K x -
            mixedPolynomialTruthFrameDirectionalInformation theta h b) / 2 +
            prespecifiedBatchCumulativeTaylorRemainder theta h b K x| <=
            |-(prespecifiedBatchCumulativeObservedDirectionalInformation
                theta h b K x -
              mixedPolynomialTruthFrameDirectionalInformation theta h b) / 2| +
              |prespecifiedBatchCumulativeTaylorRemainder
                theta h b K x| :=
                  abs_add_le _ _
        _ =
            |prespecifiedBatchCumulativeObservedDirectionalInformation
                theta h b K x -
              mixedPolynomialTruthFrameDirectionalInformation theta h b| / 2 +
              |prespecifiedBatchCumulativeTaylorRemainder
                theta h b K x| := by
                  rw [abs_div, abs_neg,
                    abs_of_nonneg (by norm_num : (0 : Real) <= 2)]
        _ < epsilon / 2 + epsilon / 2 :=
          add_lt_add (div_lt_div_of_pos_right hdiff (by norm_num))
            (hTaylor x)
        _ = epsilon := by ring
    exact (not_lt_of_ge hx) hrem

noncomputable def prespecifiedBatchRawBuresLAN_of_observedInformation
    (theta b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hObserved :
      PrespecifiedBatchObservedInformationConvergesInProbability theta b) :
    Hajek1972Assumption31LAN
      (prespecifiedBatchHajekExperiment theta b hTruth) 0 where
  truth_mem := Set.mem_univ 0
  information := mixedBuresTarget theta
  information_posDef := mixedBuresTarget_posDef theta b hTruth hSeed
  score := prespecifiedBatchRawVectorScore theta b
  score_measurable := prespecifiedBatchRawVectorScore_measurable theta b
  remainder := prespecifiedBatchRawLANRemainder theta b
  remainder_measurable :=
    prespecifiedBatchRawLANRemainder_measurable theta b
  local_parameter_eventually_mem :=
    prespecifiedBatchRawLAN_localParameter_eventually_mem theta b hTruth
  likelihood_ratio_expansion :=
    prespecifiedBatchRawLAN_likelihood_ratio_expansion
      theta b hTruth hSeed
  score_converges :=
    prespecifiedBatchRawVectorScore_converges theta b hTruth hSeed
  remainder_converges :=
    prespecifiedBatchRawLANRemainder_converges_of_observedInformation
      theta b hTruth hObserved

noncomputable def prespecifiedBatchRawBuresLANProof_of_observedInformation
    (theta b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hObserved :
      PrespecifiedBatchObservedInformationConvergesInProbability theta b) :
    PrespecifiedBatchRawBuresLANProof
      (prespecifiedBatchHajekExperiment theta b hTruth) theta where
  lan := prespecifiedBatchRawBuresLAN_of_observedInformation
    theta b hTruth hSeed hObserved
  information_eq := rfl

/-- Extending a finite prefix and then evaluating the cumulative predictable
Fisher sum does not change any of the first `K` batch contributions. -/
theorem prespecifiedBatchCumulativeConditionalVariance_extend_restrict
    (theta h b : RLSVector 3) (K : Nat)
    (omega : ExactConcretePredeterminedBatchPath) :
    (∑ t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
      prespecifiedBatchCumulativeConditionalVariance theta h b K t
        (prespecifiedBatchExtendPrefix ((Finset.range K).restrict omega))) =
    ∑ t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
      prespecifiedBatchCumulativeConditionalVariance theta h b K t omega := by
  rw [prespecifiedBatchCumulativeConditionalVariance_sum_eq_batched,
    prespecifiedBatchCumulativeConditionalVariance_sum_eq_batched]
  unfold OneQubitPredeterminedBatchHeadline.batchedPredictableScalarAverage
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hklt : k < K := Finset.mem_range.mp hk
  have hrow :
      prespecifiedBatchExtendPrefix ((Finset.range K).restrict omega) k = omega k := by
    simpa using prespecifiedBatchExtendPrefix_apply
      ((Finset.range K).restrict omega) ⟨k, Finset.mem_range.2 hklt⟩
  dsimp only
  rw [hrow]

/-- The common-path predictable Fisher convergence transported exactly to
the finite-prefix Born law used by the Hajek experiment. -/
theorem prespecifiedBatchCumulativePredictableVariancePrefix_convergesInProbability
    (theta h b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    forall epsilon : Real, 0 < epsilon ->
      Tendsto
        (fun K => prespecifiedBatchPrefixMeasure theta b K
          {x | epsilon <=
            |(∑ t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
                prespecifiedBatchCumulativeConditionalVariance theta h b K t
                  (prespecifiedBatchExtendPrefix x)) -
              mixedPolynomialTruthFrameDirectionalInformation theta h b|})
        atTop (nhds 0) := by
  intro epsilon hepsilon
  have hpath := prespecifiedBatchCumulativeFisherConvergesInProbability_closed
    theta h b hTruth hSeed epsilon hepsilon
  let hphysical := mixedNonzeroInterior_pauliPilotPhysical theta hTruth
  have heq : (fun K => prespecifiedBatchPrefixMeasure theta b K
          {x | epsilon <=
            |(∑ t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
                prespecifiedBatchCumulativeConditionalVariance theta h b K t
                  (prespecifiedBatchExtendPrefix x)) -
              mixedPolynomialTruthFrameDirectionalInformation theta h b|}) =
      (fun K => exactConcretePredeterminedBatchPathMeasure theta b hphysical
          {omega | epsilon <=
            |(∑ t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
                prespecifiedBatchCumulativeConditionalVariance theta h b K t omega) -
              mixedPolynomialTruthFrameDirectionalInformation theta h b|}) := by
    funext K
    rw [← exactConcretePredeterminedBatchPathMeasure_map_prefix_eq
      theta b hphysical K]
    rw [MeasureTheory.Measure.map_apply
      (prespecifiedBatchPrefixRestriction_measurable K)
      MeasurableSet.of_discrete]
    congr 1
    ext omega
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [prespecifiedBatchCumulativeConditionalVariance_extend_restrict]
  rw [heq]
  exact hpath

/-- Closed finite-prefix observed-information convergence.  The proof combines
Gauss's batchwise observed-minus-predictable theorem, exact transport of the
predictable Fisher limit, and the uniformly negligible pilot information. -/
theorem prespecifiedBatchObservedInformationConvergesInProbability_closed
    (theta b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    PrespecifiedBatchObservedInformationConvergesInProbability theta b := by
  intro h epsilon hepsilon
  let delta : Real := epsilon / 3
  have hdelta : 0 < delta := div_pos hepsilon (by norm_num)
  have hdev := prespecifiedBatchObservedInformationLANDeviationEvent_tendsto_zero
    theta h b hTruth.2 delta hdelta
  have hpred :=
    prespecifiedBatchCumulativePredictableVariancePrefix_convergesInProbability
      theta h b hTruth hSeed delta hdelta
  have hpilot := prespecifiedBatchCumulativePilotObservedInformation_uniform_tendsto_zero
    theta h hTruth.2 delta hdelta
  have hupper : Tendsto
      (fun K =>
        prespecifiedBatchPrefixMeasure theta b K
          {x | delta <=
            |(prespecifiedBatchCumulativeObservedDirectionalInformation theta h b K x -
                prespecifiedBatchCumulativePilotObservedInformation theta h K x) -
              ∑ t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
                prespecifiedBatchCumulativeConditionalVariance theta h b K t
                  (prespecifiedBatchExtendPrefix x)|} +
        prespecifiedBatchPrefixMeasure theta b K
          {x | delta <=
            |(∑ t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
                prespecifiedBatchCumulativeConditionalVariance theta h b K t
                  (prespecifiedBatchExtendPrefix x)) -
              mixedPolynomialTruthFrameDirectionalInformation theta h b|})
      atTop (nhds 0) := by
    simpa only [zero_add] using hdev.add hpred
  apply Tendsto.squeeze' tendsto_const_nhds hupper
  · exact Filter.Eventually.of_forall fun K => bot_le
  · filter_upwards [hpilot] with K hpilotK
    let mu := prespecifiedBatchPrefixMeasure theta b K
    let observed := prespecifiedBatchCumulativeObservedDirectionalInformation theta h b K
    let pilot := prespecifiedBatchCumulativePilotObservedInformation theta h K
    let predictable := fun x : PrespecifiedBatchFinitePrefix K =>
      ∑ t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
        prespecifiedBatchCumulativeConditionalVariance theta h b K t
          (prespecifiedBatchExtendPrefix x)
    let target := mixedPolynomialTruthFrameDirectionalInformation theta h b
    let devEvent : Set (PrespecifiedBatchFinitePrefix K) :=
      {x | delta <= |(observed x - pilot x) - predictable x|}
    let predEvent : Set (PrespecifiedBatchFinitePrefix K) :=
      {x | delta <= |predictable x - target|}
    calc
      mu {x | epsilon <= |observed x - target|} <= mu (devEvent ∪ predEvent) := by
        apply measure_mono
        intro x hx
        by_contra hxunion
        have hsmall :
            |(observed x - pilot x) - predictable x| < delta ∧
              |predictable x - target| < delta := by
          simpa [devEvent, predEvent] using hxunion
        have hpnonneg : 0 <= pilot x := by
          simp [pilot, prespecifiedBatchCumulativePilotObservedInformation]
          positivity
        have hp : |pilot x| < delta := by
          rw [abs_of_nonneg hpnonneg]
          exact hpilotK x
        have htriangle :
            |observed x - target| <=
              |(observed x - pilot x) - predictable x| +
                |pilot x| + |predictable x - target| := by
          calc
            |observed x - target| =
                |((observed x - pilot x) - predictable x) +
                  pilot x + (predictable x - target)| := by
                    congr 1
                    ring
            _ <= |(observed x - pilot x) - predictable x| +
                  |pilot x| + |predictable x - target| :=
                    abs_add_three _ _ _
        have : |observed x - target| < epsilon := by
          dsimp [delta] at hsmall hp ⊢
          linarith [htriangle]
        exact (not_lt_of_ge hx) this
      _ <= mu devEvent + mu predEvent := measure_union_le _ _
      _ =
          prespecifiedBatchPrefixMeasure theta b K
            {x | delta <=
              |(prespecifiedBatchCumulativeObservedDirectionalInformation theta h b K x -
                  prespecifiedBatchCumulativePilotObservedInformation theta h K x) -
                ∑ t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
                  prespecifiedBatchCumulativeConditionalVariance theta h b K t
                    (prespecifiedBatchExtendPrefix x)|} +
          prespecifiedBatchPrefixMeasure theta b K
            {x | delta <=
              |(∑ t : Fin (prespecifiedBatchCumulativeFinalRowLength K),
                  prespecifiedBatchCumulativeConditionalVariance theta h b K t
                    (prespecifiedBatchExtendPrefix x)) -
                mixedPolynomialTruthFrameDirectionalInformation theta h b|} := rfl

/-- Premise-free raw LAN for the exact finite-prefix prespecified-batch
experiment. -/
noncomputable def prespecifiedBatchRawBuresLAN
    (theta b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    Hajek1972Assumption31LAN
      (prespecifiedBatchHajekExperiment theta b hTruth) 0 :=
  prespecifiedBatchRawBuresLAN_of_observedInformation theta b hTruth hSeed
    (prespecifiedBatchObservedInformationConvergesInProbability_closed
      theta b hTruth hSeed)

/-- Terminal exact raw-Bures LAN package, with no protocol premise left as an
argument. -/
noncomputable def prespecifiedBatchRawBuresLANProof_closed
    (theta b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    PrespecifiedBatchRawBuresLANProof
      (prespecifiedBatchHajekExperiment theta b hTruth) theta :=
  prespecifiedBatchRawBuresLANProof_of_observedInformation theta b hTruth hSeed
    (prespecifiedBatchObservedInformationConvergesInProbability_closed
      theta b hTruth hSeed)

end QubitOracle.Paper
