import QubitOracle.Paper.OneQubitExactConcretePredeterminedBatchProductLaw
import QubitOracle.Paper.OneQubitMixedPolynomialFiniteRNClosure

/-!
# Finite-prefix experiment for the exact prespecified batches

At horizon `K` the sample is the finite dependent product of the first `K`
pilot-plus-final rows.  No infinite tail is retained in the statistical
experiment.  The parameterization below uses Hajek's formal `1 / sqrt K`
coordinate while the physical Bloch displacement is scaled by the exact total
number of observations in the first `K` batches.

A total fallback to the interior truth makes the law a probability measure for
every formal parameter.  For each fixed local direction, the fallback is
proved to disappear eventually.  Finite full support then gives exact
singleton, domination, and Radon--Nikodym product identities.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

noncomputable section

attribute [local instance]
  pauliPilotBornPathMeasurableSpace
  mixedTwoStageFiniteRowMeasurableSpace
  mixedTwoStageFiniteRowMeasurableSingletonClass

/-- Complete data observed through the end of prespecified batch `K - 1`. -/
abbrev PrespecifiedBatchFinitePrefix (K : Nat) : Type :=
  (k : Finset.range K) -> ExactConcretePredeterminedBatchRow k.1

/-- Exact total number of binary Born observations in the first `K` batches. -/
def prespecifiedBatchTotalObservations (K : Nat) : Nat :=
  PureMultilevelSequentialBatchAdaptive.cumulativeCount
    exactConcreteBatchSize K

/-- Exact finite dependent-product Born law through batch horizon `K`. -/
def prespecifiedBatchPrefixMeasure
    (eta b : RLSVector 3) (K : Nat) :
    Measure (PrespecifiedBatchFinitePrefix K) :=
  Measure.pi (fun k : Finset.range K =>
    exactConcretePredeterminedBatchRowMeasure eta b k.1)

/-- Every physical Bloch parameter gives a normalized finite-prefix law. -/
theorem prespecifiedBatchPrefixMeasure_isProbability
    (eta b : RLSVector 3) (hphysical : PauliPilotPhysicalBloch eta)
    (K : Nat) :
    IsProbabilityMeasure (prespecifiedBatchPrefixMeasure eta b K) := by
  letI : forall k : Finset.range K,
      IsProbabilityMeasure
        (exactConcretePredeterminedBatchRowMeasure eta b k.1) :=
    fun k =>
      exactConcretePredeterminedBatchRowMeasure_isProbability
        eta b hphysical k.1
  unfold prespecifiedBatchPrefixMeasure
  infer_instance

/-- Physical parameter represented by a formal Hajek coordinate at horizon
`K`.  The `sqrt K` factor cancels Hajek's own `1 / sqrt K`, leaving the exact
physical scale `1 / sqrt(prespecifiedBatchTotalObservations K)`. -/
def prespecifiedBatchHajekPhysicalCandidate
    (theta : RLSVector 3) (K : Nat)
    (eta : HajekParameter (Fin 3)) : RLSVector 3 :=
  if K = 0 then theta else
    mixedLocalAlternative theta prespecifiedBatchTotalObservations K
      (fun j => Real.sqrt (K : Real) * eta j)

/-- Total probability-law extension outside the Bloch ball. -/
def prespecifiedBatchHajekSafePhysicalParameter
    (theta : RLSVector 3) (K : Nat)
    (eta : HajekParameter (Fin 3)) : RLSVector 3 := by
  classical
  exact if PauliPilotPhysicalBloch
      (prespecifiedBatchHajekPhysicalCandidate theta K eta)
    then prespecifiedBatchHajekPhysicalCandidate theta K eta
    else theta

theorem prespecifiedBatchHajekPhysicalCandidate_zero
    (theta : RLSVector 3) (K : Nat) :
    prespecifiedBatchHajekPhysicalCandidate theta K 0 = theta := by
  by_cases hK : K = 0
  · simp [prespecifiedBatchHajekPhysicalCandidate, hK]
  · rw [prespecifiedBatchHajekPhysicalCandidate, if_neg hK]
    funext j
    simp [mixedLocalAlternative]

theorem prespecifiedBatchHajekSafePhysicalParameter_physical
    (theta : RLSVector 3) (hTruth : MixedNonzeroInteriorTruth theta)
    (K : Nat) (eta : HajekParameter (Fin 3)) :
    PauliPilotPhysicalBloch
      (prespecifiedBatchHajekSafePhysicalParameter theta K eta) := by
  unfold prespecifiedBatchHajekSafePhysicalParameter
  by_cases hphysical : PauliPilotPhysicalBloch
      (prespecifiedBatchHajekPhysicalCandidate theta K eta)
  · rw [if_pos hphysical]
    exact hphysical
  · rw [if_neg hphysical]
    exact mixedNonzeroInterior_pauliPilotPhysical theta hTruth

theorem prespecifiedBatchHajekSafePhysicalParameter_zero
    (theta : RLSVector 3) (hTruth : MixedNonzeroInteriorTruth theta)
    (K : Nat) :
    prespecifiedBatchHajekSafePhysicalParameter theta K 0 = theta := by
  rw [prespecifiedBatchHajekSafePhysicalParameter,
    prespecifiedBatchHajekPhysicalCandidate_zero theta K]
  simp [mixedNonzeroInterior_pauliPilotPhysical theta hTruth]

/-- The exact finite-prefix experiment, expressed in local coordinates. -/
def prespecifiedBatchHajekExperiment
    (theta b : RLSVector 3)
    (hTruth : MixedNonzeroInteriorTruth theta) :
    HajekExperimentSequence (Fin 3) where
  Sample K := PrespecifiedBatchFinitePrefix K
  measurableSpace K := inferInstance
  parameterSet := Set.univ
  law K eta := prespecifiedBatchPrefixMeasure
    (prespecifiedBatchHajekSafePhysicalParameter theta K eta) b K
  probabilityMeasure K eta :=
    prespecifiedBatchPrefixMeasure_isProbability
      (prespecifiedBatchHajekSafePhysicalParameter theta K eta) b
      (prespecifiedBatchHajekSafePhysicalParameter_physical
        theta hTruth K eta) K

/-- At local coordinate zero, the finite experiment is exactly the genuine
truth Born product law. -/
theorem prespecifiedBatchHajekExperiment_baseLaw
    (theta b : RLSVector 3)
    (hTruth : MixedNonzeroInteriorTruth theta) (K : Nat) :
    (prespecifiedBatchHajekExperiment theta b hTruth).law K 0 =
      prespecifiedBatchPrefixMeasure theta b K := by
  change prespecifiedBatchPrefixMeasure
      (prespecifiedBatchHajekSafePhysicalParameter theta K 0) b K =
    prespecifiedBatchPrefixMeasure theta b K
  rw [prespecifiedBatchHajekSafePhysicalParameter_zero theta hTruth K]

/-- The exact total-sample local scale tends to zero. -/
theorem prespecifiedBatchLocalScale_tendsto_zero :
    Tendsto (mixedLocalScale prespecifiedBatchTotalObservations)
      atTop (nhds 0) := by
  change Tendsto
    (fun K : Nat =>
      (Real.sqrt (prespecifiedBatchTotalObservations K : Real))⁻¹)
    atTop (nhds 0)
  exact tendsto_inv_atTop_zero.comp
    (Real.tendsto_sqrt_atTop.comp
      (by simpa [prespecifiedBatchTotalObservations] using
        exactConcreteBatch_totalSamples_tendsto_atTop))

/-- For positive horizons, Hajek's formal local coordinate is exactly the
physical direct-coordinate alternative at root-total-sample scale. -/
theorem prespecifiedBatchHajekPhysicalCandidate_localParameter
    (theta h : RLSVector 3) (K : Nat) (hK : K ≠ 0) :
    prespecifiedBatchHajekPhysicalCandidate theta K
        (hajekLocalParameter 0 h K) =
      mixedLocalAlternative theta prespecifiedBatchTotalObservations K h := by
  rw [prespecifiedBatchHajekPhysicalCandidate, if_neg hK]
  unfold hajekLocalParameter
  have hKpos : 0 < (K : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero hK
  have hsqrt : Real.sqrt (K : Real) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hKpos)
  congr 1
  funext j
  simp only [Pi.zero_apply, zero_add]
  field_simp [hsqrt]

/-- Every fixed root-total-sample local alternative is eventually a strictly
interior Bloch vector. -/
theorem prespecifiedBatchLocalAlternative_eventually_strictInterior
    (theta h : RLSVector 3)
    (hTruth : MixedNonzeroInteriorTruth theta) :
    ∀ᶠ eventuallyK : Nat in atTop,
      MixedPilotStrictInterior
        (mixedLocalAlternative theta prespecifiedBatchTotalObservations
          eventuallyK h) := by
  let H : Real := blochNormSq h + 1
  have hnorm : 0 <= blochNormSq h := by
    unfold blochNormSq
    positivity
  have hball : MixedLocalDirectionBall H h := by
    unfold MixedLocalDirectionBall H
    nlinarith [sq_nonneg (blochNormSq h)]
  filter_upwards
    [mixedLocalAlternative_eventually_uniform_interior
      theta prespecifiedBatchTotalObservations H hTruth.2
      prespecifiedBatchLocalScale_tendsto_zero] with K hK
  exact hK h hball

/-- Consequently the safety fallback disappears for every fixed local
direction at all sufficiently large horizons. -/
theorem prespecifiedBatchHajekSafePhysicalParameter_eventually_local
    (theta h : RLSVector 3)
    (hTruth : MixedNonzeroInteriorTruth theta) :
    ∀ᶠ eventuallyK : Nat in atTop,
      prespecifiedBatchHajekSafePhysicalParameter theta eventuallyK
          (hajekLocalParameter 0 h eventuallyK) =
        mixedLocalAlternative theta prespecifiedBatchTotalObservations
          eventuallyK h := by
  filter_upwards
    [prespecifiedBatchLocalAlternative_eventually_strictInterior
      theta h hTruth,
      eventually_ne_atTop 0] with K hInterior hK
  rw [prespecifiedBatchHajekSafePhysicalParameter,
    prespecifiedBatchHajekPhysicalCandidate_localParameter theta h K hK,
    if_pos (mixedPilotStrictInterior_physical _ hInterior)]

/-- Exact eventually genuine local law of the finite-prefix experiment. -/
theorem prespecifiedBatchHajekExperiment_eventually_localLaw
    (theta b h : RLSVector 3)
    (hTruth : MixedNonzeroInteriorTruth theta) :
    ∀ᶠ eventuallyK : Nat in atTop,
      (prespecifiedBatchHajekExperiment theta b hTruth).law eventuallyK
          (hajekLocalParameter 0 h eventuallyK) =
        prespecifiedBatchPrefixMeasure
          (mixedLocalAlternative theta prespecifiedBatchTotalObservations
            eventuallyK h) b eventuallyK := by
  filter_upwards
    [prespecifiedBatchHajekSafePhysicalParameter_eventually_local
      theta h hTruth] with K hK
  exact congrArg (fun eta => prespecifiedBatchPrefixMeasure eta b K) hK

/-- Exact singleton mass of the finite dependent product. -/
theorem prespecifiedBatchPrefixMeasure_singleton
    (eta b : RLSVector 3) (hphysical : PauliPilotPhysicalBloch eta)
    (K : Nat) (x : PrespecifiedBatchFinitePrefix K) :
    prespecifiedBatchPrefixMeasure eta b K {x} =
      ∏ k : Finset.range K,
        ENNReal.ofReal
          (mixedTwoStageFiniteRowMass eta
            (exactConcreteBatchSelectedFrame k.1 b) (x k)) := by
  letI : forall k : Finset.range K,
      IsProbabilityMeasure
        (exactConcretePredeterminedBatchRowMeasure eta b k.1) :=
    fun k =>
      exactConcretePredeterminedBatchRowMeasure_isProbability
        eta b hphysical k.1
  unfold prespecifiedBatchPrefixMeasure
  rw [<- Measure.infinitePi_eq_pi,
    Measure.infinitePi_singleton_of_fintype]
  apply Finset.prod_congr rfl
  intro k _
  exact mixedTwoStageFiniteBornMeasure_singleton eta
    (exactConcreteBatchSelectedFrame k.1 b) hphysical (x k)

/-- Strict interior truth gives full support to every finite prefix. -/
theorem prespecifiedBatchPrefixMeasure_singleton_pos
    (theta b : RLSVector 3) (hInterior : MixedPilotStrictInterior theta)
    (K : Nat) (x : PrespecifiedBatchFinitePrefix K) :
    0 < prespecifiedBatchPrefixMeasure theta b K {x} := by
  rw [prespecifiedBatchPrefixMeasure_singleton theta b
    (mixedPilotStrictInterior_physical theta hInterior) K x]
  apply bot_lt_iff_ne_bot.2
  change (∏ k : Finset.range K,
    ENNReal.ofReal
      (mixedTwoStageFiniteRowMass theta
        (exactConcreteBatchSelectedFrame k.1 b) (x k))) ≠ 0
  rw [Finset.prod_ne_zero_iff]
  intro k _
  exact ne_of_gt (ENNReal.ofReal_pos.2
    (mixedTwoStageFiniteRowMass_pos_of_strictInterior theta
      (exactConcreteBatchSelectedFrame k.1 b) hInterior (x k)))

/-- Every finite-prefix law is dominated by an interior truth law. -/
theorem prespecifiedBatchPrefixMeasure_absolutelyContinuous
    (eta theta b : RLSVector 3) (hTheta : MixedPilotStrictInterior theta)
    (K : Nat) :
    prespecifiedBatchPrefixMeasure eta b K ≪
      prespecifiedBatchPrefixMeasure theta b K :=
  finiteFullSupport_absolutelyContinuous
    (prespecifiedBatchPrefixMeasure eta b K)
    (prespecifiedBatchPrefixMeasure theta b K)
    (prespecifiedBatchPrefixMeasure_singleton_pos theta b hTheta K)

/-- Exact finite-support Radon--Nikodym density as a singleton-mass ratio. -/
theorem prespecifiedBatchPrefixMeasure_rnDeriv_toReal_eq_singletonRatio
    (eta theta b : RLSVector 3)
    (hEta : PauliPilotPhysicalBloch eta)
    (hTheta : MixedPilotStrictInterior theta)
    (K : Nat) (x : PrespecifiedBatchFinitePrefix K) :
    ((prespecifiedBatchPrefixMeasure eta b K).rnDeriv
      (prespecifiedBatchPrefixMeasure theta b K) x).toReal =
      (prespecifiedBatchPrefixMeasure eta b K {x}).toReal /
        (prespecifiedBatchPrefixMeasure theta b K {x}).toReal := by
  letI := prespecifiedBatchPrefixMeasure_isProbability eta b hEta K
  letI := prespecifiedBatchPrefixMeasure_isProbability theta b
    (mixedPilotStrictInterior_physical theta hTheta) K
  exact finiteFullSupport_rnDeriv_toReal_eq_singletonRatio
    (prespecifiedBatchPrefixMeasure eta b K)
    (prespecifiedBatchPrefixMeasure theta b K)
    (prespecifiedBatchPrefixMeasure_singleton_pos theta b hTheta K) x

/-- Exact finite-prefix likelihood: the density is the product of all exact
batch-row masses under the alternative divided by the corresponding product
under the truth. -/
theorem prespecifiedBatchPrefixMeasure_rnDeriv_toReal_eq_productMassRatio
    (eta theta b : RLSVector 3)
    (hEta : MixedPilotStrictInterior eta)
    (hTheta : MixedPilotStrictInterior theta)
    (K : Nat) (x : PrespecifiedBatchFinitePrefix K) :
    ((prespecifiedBatchPrefixMeasure eta b K).rnDeriv
      (prespecifiedBatchPrefixMeasure theta b K) x).toReal =
      (∏ k : Finset.range K,
        mixedTwoStageFiniteRowMass eta
          (exactConcreteBatchSelectedFrame k.1 b) (x k)) /
      (∏ k : Finset.range K,
        mixedTwoStageFiniteRowMass theta
          (exactConcreteBatchSelectedFrame k.1 b) (x k)) := by
  rw [prespecifiedBatchPrefixMeasure_rnDeriv_toReal_eq_singletonRatio
      eta theta b (mixedPilotStrictInterior_physical eta hEta) hTheta K x,
    prespecifiedBatchPrefixMeasure_singleton eta b
      (mixedPilotStrictInterior_physical eta hEta) K x,
    prespecifiedBatchPrefixMeasure_singleton theta b
      (mixedPilotStrictInterior_physical theta hTheta) K x]
  simp only [ENNReal.toReal_prod]
  congr 1 <;> apply Finset.prod_congr rfl <;> intro k _
  · rw [ENNReal.toReal_ofReal
      (mixedTwoStageFiniteRowMass_nonnegative eta
        (exactConcreteBatchSelectedFrame k.1 b)
        (mixedPilotStrictInterior_physical eta hEta) (x k))]
  · rw [ENNReal.toReal_ofReal
      (mixedTwoStageFiniteRowMass_nonnegative theta
        (exactConcreteBatchSelectedFrame k.1 b)
        (mixedPilotStrictInterior_physical theta hTheta) (x k))]

/-- The exact Hajek likelihood ratio is eventually the genuine product of all
batch-row mass ratios at the root-total-sample local alternative. -/
theorem prespecifiedBatchHajekLikelihoodRatio_eventually_eq_productMassRatio
    (theta b h : RLSVector 3)
    (hTruth : MixedNonzeroInteriorTruth theta) :
    exists K0, forall K, K0 <= K ->
      forall x : PrespecifiedBatchFinitePrefix K,
        hajekLikelihoodRatio
            (prespecifiedBatchHajekExperiment theta b hTruth) K
            (hajekLocalParameter 0 h K) 0 x =
          (∏ k : Finset.range K,
            mixedTwoStageFiniteRowMass
              (mixedLocalAlternative theta
                prespecifiedBatchTotalObservations K h)
              (exactConcreteBatchSelectedFrame k.1 b) (x k)) /
          (∏ k : Finset.range K,
            mixedTwoStageFiniteRowMass theta
              (exactConcreteBatchSelectedFrame k.1 b) (x k)) := by
  have hlaw := prespecifiedBatchHajekExperiment_eventually_localLaw
    theta b h hTruth
  have hinterior :=
    prespecifiedBatchLocalAlternative_eventually_strictInterior
      theta h hTruth
  rw [eventually_atTop] at hlaw hinterior
  obtain ⟨Klaw, hKlaw⟩ := hlaw
  obtain ⟨Kint, hKint⟩ := hinterior
  refine ⟨max Klaw Kint, ?_⟩
  intro K hK x
  have hLaw := hKlaw K (le_trans (Nat.le_max_left _ _) hK)
  have hInterior := hKint K (le_trans (Nat.le_max_right _ _) hK)
  unfold hajekLikelihoodRatio
  rw [hLaw, prespecifiedBatchHajekExperiment_baseLaw]
  exact prespecifiedBatchPrefixMeasure_rnDeriv_toReal_eq_productMassRatio
    (mixedLocalAlternative theta prespecifiedBatchTotalObservations K h)
    theta b hInterior hTruth.2 K x

end

end QubitOracle.Paper
