import QubitOracle.Paper.OneQubitPrespecifiedBatchLikelihoodExpansion
import QubitOracle.Paper.OneQubitPrespecifiedBatchSafeguardedEstimator
import QubitOracle.Paper.OneQubitPrespecifiedBatchCumulativeScoreCLT
import QubitOracle.Paper.OneQubitPrespecifiedBatchCumulativeInformationClosure
import QubitOracle.Paper.OneQubitPrespecifiedBatchObservedInformationClosure
import QubitOracle.Paper.OneQubitPrespecifiedBatchRawLANClosure
import QubitOracle.Paper.MixedRotationalTarget
import QubitOracle.Paper.MathlibHoeffding1963Bridge
import Mathlib.Probability.Independence.InfinitePi

/-!
# Available asymptotic inputs for the prespecified-batch safeguarded estimator

This module records only the concrete inputs that are presently closed for the
implemented estimator.  In particular, it does not manufacture the missing
`PrespecifiedBatchCumulativeMartingaleCertificate`: the imported cumulative
score module deliberately exposes that certificate as an unproved argument.
Consequently no estimator CLT, fourth-moment assertion, or `9/4` risk endpoint
is stated here until the concrete certificate and its moment strengthening are
available as proved imported theorems.

The results below close the exact pooled-pilot count, the vanishing ridge, and
the Bures target geometry needed by a future trustworthy Fisher import.  The
existing cumulative-information closure is intentionally not imported: its
focused build currently fails and its printed Fisher endpoint contains
`sorryAx`.
-/

namespace QubitOracle.Paper

set_option maxHeartbeats 800000
set_option maxRecDepth 10000

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory Topology
open PureMultilevelSequentialBatchAdaptive

noncomputable section

attribute [local instance]
  pauliPilotBornPathMeasurableSpace
  mixedTwoStageFiniteRowMeasurableSpace
  mixedTwoStageFiniteRowMeasurableSingletonClass

/-- The first `K` batches contain exactly `27 K^4` complete Pauli pilot
blocks, equivalently `(3K)^4` pilot observations. -/
theorem prespecifiedBatchPooledPilotBlocks_eq (K : Nat) :
    prespecifiedBatchPooledPilotBlocks K = 27 * K ^ 4 := by
  have hExploration := exactConcreteBatchExploration_cumulative K
  unfold cumulativeCount exactConcreteBatchExplorationSize at hExploration
  have hThree :
      3 * (∑ k : Fin K, exactConcreteBatchPilotBlocks k) =
        (3 * K) ^ 4 := by
    rw [Fin.sum_univ_eq_sum_range, Finset.mul_sum]
    exact hExploration
  unfold prespecifiedBatchPooledPilotBlocks
  norm_num [mul_pow] at hThree ⊢
  omega

/-- The deterministic ridge in the implemented inverse vanishes. -/
theorem prespecifiedBatchRidge_tendsto_zero :
    Tendsto prespecifiedBatchRidge atTop (nhds 0) := by
  change Tendsto
    (fun K : Nat => ((((K + 1 : Nat) : Real) ^ 2)⁻¹))
    atTop (nhds 0)
  have hbase : Tendsto (fun K : Nat => (((K : Real) + 1))⁻¹)
      atTop (nhds 0) := by
    simpa [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
  simpa [Nat.cast_add, inv_pow] using hbase.pow 2

/-! ## Exact pooled-pilot finite-prefix law -/

/-- Canonical identification of `Fin K` with the subtype of naturals in
`Finset.range K`, used by the finite-prefix product law. -/
def prespecifiedBatchFinRangeEquiv (K : Nat) :
    Fin K ≃ Finset.range K where
  toFun k := ⟨k, Finset.mem_range.mpr k.isLt⟩
  invFun k := ⟨k, Finset.mem_range.mp k.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Convert the estimator's native `Fin K` prefix into the finite dependent
product sample used by the exact Hajek experiment. -/
def prespecifiedBatchEstimatorPrefixToFinitePrefix (K : Nat)
    (omega : ExactConcretePredeterminedBatchPrefix K) :
    PrespecifiedBatchFinitePrefix K :=
  fun k => omega ⟨k.1, Finset.mem_range.mp k.2⟩

/-- The exact Raw-LAN central score, transported to the estimator's native
`Fin K` prefix. -/
def prespecifiedBatchEstimatorCentralScore
    (theta b : RLSVector 3) (K : Nat)
    (omega : ExactConcretePredeterminedBatchPrefix K) : LANParameter (Fin 3) :=
  prespecifiedBatchLANVector
    (prespecifiedBatchRawVectorScore theta b K
      (prespecifiedBatchEstimatorPrefixToFinitePrefix K omega))

/-- Exact finite-prefix alignment of the implemented central score with the
direction-independent Raw-LAN score. -/
theorem prespecifiedBatchEstimatorCentralScore_eq_rawVectorScore
    (theta b : RLSVector 3) (K : Nat)
    (omega : ExactConcretePredeterminedBatchPrefix K) :
    prespecifiedBatchEstimatorCentralScore theta b K omega =
      prespecifiedBatchLANVector
        (prespecifiedBatchRawVectorScore theta b K
          (prespecifiedBatchEstimatorPrefixToFinitePrefix K omega)) := rfl

/-- Every pilot block in the first `K` batches, retaining its batch label. -/
abbrev PrespecifiedBatchPooledPilotShot (K : Nat) :=
  (k : Fin K) × Fin (exactConcreteBatchPilotBlocks k)

/-- The ragged family of pilot blocks has exactly the pooled block count. -/
theorem prespecifiedBatchPooledPilotShot_card (K : Nat) :
    Fintype.card (PrespecifiedBatchPooledPilotShot K) =
      prespecifiedBatchPooledPilotBlocks K := by
  simp [PrespecifiedBatchPooledPilotShot,
    prespecifiedBatchPooledPilotBlocks]

/-- A deterministic enumeration of every pooled pilot block.  Its order is
irrelevant because the estimator uses only the sum. -/
noncomputable def prespecifiedBatchPooledPilotShotEquiv (K : Nat) :
    Fin (prespecifiedBatchPooledPilotBlocks K) ≃
      PrespecifiedBatchPooledPilotShot K :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, prespecifiedBatchPooledPilotShot_card])

/-- Extract the pilot path in batch `k` from an exact finite prefix. -/
def prespecifiedBatchPrefixPilot (K : Nat) (k : Fin K)
    (omega : ExactConcretePredeterminedBatchPrefix K) :
    PauliPilotPath (exactConcreteBatchPilotBlocks k) :=
  (omega k).1

/-- Exact dependent product law on the native sample type used by the
implemented estimator. -/
def prespecifiedBatchEstimatorPrefixMeasure
    (theta b : RLSVector 3) (K : Nat) :
    Measure (ExactConcretePredeterminedBatchPrefix K) :=
  Measure.pi (fun k : Fin K =>
    exactConcretePredeterminedBatchRowMeasure theta b k)

theorem prespecifiedBatchEstimatorPrefixMeasure_isProbability
    (theta b : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (K : Nat) :
    IsProbabilityMeasure
      (prespecifiedBatchEstimatorPrefixMeasure theta b K) := by
  letI : forall k : Fin K,
      IsProbabilityMeasure
        (exactConcretePredeterminedBatchRowMeasure theta b k) :=
    fun k => exactConcretePredeterminedBatchRowMeasure_isProbability
      theta b hphysical k
  unfold prespecifiedBatchEstimatorPrefixMeasure
  infer_instance

/-- The exact marginal of each extracted pilot is its finite Born product
law. -/
theorem prespecifiedBatchPrefixMeasure_map_pilot
    (theta b : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (K : Nat) (k : Fin K) :
    (prespecifiedBatchEstimatorPrefixMeasure theta b K).map
        (prespecifiedBatchPrefixPilot K k) =
      pauliPilotBornProductMeasure
        (q := exactConcreteBatchPilotBlocks k) theta := by
  letI : forall t : Fin K,
      IsProbabilityMeasure
        (exactConcretePredeterminedBatchRowMeasure theta b t) :=
    fun t => exactConcretePredeterminedBatchRowMeasure_isProbability
      theta b hphysical t
  have hEval :
      (prespecifiedBatchEstimatorPrefixMeasure theta b K).map
          (Function.eval k) =
        exactConcretePredeterminedBatchRowMeasure theta b k.1 := by
    unfold prespecifiedBatchEstimatorPrefixMeasure
    simpa [measure_univ] using
      (Measure.pi_map_eval
        (fun t : Fin K =>
          exactConcretePredeterminedBatchRowMeasure theta b t) k)
  rw [show prespecifiedBatchPrefixPilot K k =
      (fun row => row.1) ∘ Function.eval k by rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop), hEval]
  exact exactConcretePredeterminedBatchRowMeasure_map_pilot
    theta b hphysical k.1

private theorem iIndepFun_comp_of_map_eq
    {Omega Xi : Type*} [MeasurableSpace Omega] [MeasurableSpace Xi]
    {I : Type*} [Fintype I]
    {mu : Measure Omega} {nu : Measure Xi}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (f : Omega -> Xi) (hf : Measurable f)
    (hmap : mu.map f = nu)
    (X : I -> Xi -> Real) (hXmeas : forall i, Measurable (X i))
    (hX : iIndepFun X nu) :
    iIndepFun (fun i omega => X i (f omega)) mu := by
  change iIndepFun (fun i => X i ∘ f) mu
  rw [iIndepFun_iff_map_fun_eq_pi_map
    (fun i => ((hXmeas i).comp hf).aemeasurable)]
  calc
    mu.map (fun omega i => (X i ∘ f) omega) =
        (mu.map f).map (fun x i => X i x) := by
      rw [Measure.map_map (measurable_pi_lambda _ hXmeas) hf]
      rfl
    _ = nu.map (fun x i => X i x) := by rw [hmap]
    _ = Measure.pi (fun i => nu.map (X i)) :=
      (iIndepFun_iff_map_fun_eq_pi_map
        (fun i => (hXmeas i).aemeasurable)).1 hX
    _ = Measure.pi (fun i => mu.map (X i ∘ f)) := by
      congr 1
      funext i
      rw [← hmap, Measure.map_map (hXmeas i) hf]

/-- Under the exact finite-prefix product law, all fixed-coordinate signs in
all pooled pilot blocks are mutually independent. -/
theorem prespecifiedBatchPooledPilotCoordinate_iIndepFun
    (theta b : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (K : Nat) (j : Fin 3) :
    iIndepFun
      (fun i : Fin (prespecifiedBatchPooledPilotBlocks K) =>
        fun omega : ExactConcretePredeterminedBatchPrefix K =>
          let shot := prespecifiedBatchPooledPilotShotEquiv K i
          pauliOutcomeSign
            (prespecifiedBatchPrefixPilot K shot.1 omega shot.2 j))
      (prespecifiedBatchEstimatorPrefixMeasure theta b K) := by
  letI : forall t : Fin K,
      IsProbabilityMeasure
        (exactConcretePredeterminedBatchRowMeasure theta b t) :=
    fun t => exactConcretePredeterminedBatchRowMeasure_isProbability
      theta b hphysical t
  letI : IsProbabilityMeasure
      (prespecifiedBatchEstimatorPrefixMeasure theta b K) :=
    prespecifiedBatchEstimatorPrefixMeasure_isProbability
      theta b hphysical K
  have hOuter :
      iIndepFun
        (fun k : Fin K =>
          fun omega : ExactConcretePredeterminedBatchPrefix K =>
            fun r : Fin (exactConcreteBatchPilotBlocks k) =>
              pauliOutcomeSign
                (prespecifiedBatchPrefixPilot K k omega r j))
        (prespecifiedBatchEstimatorPrefixMeasure theta b K) := by
    unfold prespecifiedBatchEstimatorPrefixMeasure
    exact iIndepFun_pi (X := fun (k : Fin K)
        (row : ExactConcretePredeterminedBatchRow k) =>
      fun r : Fin (exactConcreteBatchPilotBlocks k) =>
        pauliOutcomeSign (row.1 r j)) (by fun_prop)
  have hInner (k : Fin K) :
      iIndepFun
        (fun r : Fin (exactConcreteBatchPilotBlocks k) =>
          fun omega : ExactConcretePredeterminedBatchPrefix K =>
            pauliOutcomeSign
              (prespecifiedBatchPrefixPilot K k omega r j))
        (prespecifiedBatchEstimatorPrefixMeasure theta b K) := by
    let nu := pauliPilotBornProductMeasure
      (q := exactConcreteBatchPilotBlocks k) theta
    letI : IsProbabilityMeasure nu :=
      ⟨pauliPilotBornProductMeasure_univ theta hphysical⟩
    have hPauli :
        iIndepFun
          (pauliPilotCoordinateVariable
            (q := exactConcreteBatchPilotBlocks k) j) nu :=
      finiteIndependentRealFamily_iIndepFun
        (pauliPilotBornProductMeasure_univ theta hphysical)
        (pauliPilotCoordinateVariable_finiteIndependent
          theta hphysical j)
    simpa [nu, pauliPilotCoordinateVariable] using
      iIndepFun_comp_of_map_eq
        (prespecifiedBatchPrefixPilot K k) (by fun_prop)
        (prespecifiedBatchPrefixMeasure_map_pilot
          theta b hphysical K k)
        (pauliPilotCoordinateVariable
          (q := exactConcreteBatchPilotBlocks k) j)
        (fun _ => Measurable.of_discrete) hPauli
  have hSigma :
      iIndepFun
        (fun shot : PrespecifiedBatchPooledPilotShot K =>
          fun omega : ExactConcretePredeterminedBatchPrefix K =>
            pauliOutcomeSign
              (prespecifiedBatchPrefixPilot K shot.1 omega shot.2 j))
        (prespecifiedBatchEstimatorPrefixMeasure theta b K) :=
    iIndepFun_uncurry (by fun_prop) hOuter hInner
  simpa using hSigma.precomp
    (prespecifiedBatchPooledPilotShotEquiv K).injective

/-- Rectangle-factorization form of pooled fixed-coordinate independence,
ready for the project Hoeffding interface. -/
theorem prespecifiedBatchPooledPilotCoordinate_finiteIndependent
    (theta b : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (K : Nat) (j : Fin 3) :
    FiniteIndependentRealFamily
      (prespecifiedBatchEstimatorPrefixMeasure theta b K)
      (fun i : Fin (prespecifiedBatchPooledPilotBlocks K) =>
        fun omega : ExactConcretePredeterminedBatchPrefix K =>
          let shot := prespecifiedBatchPooledPilotShotEquiv K i
          pauliOutcomeSign
            (prespecifiedBatchPrefixPilot K shot.1 omega shot.2 j)) := by
  intro events hEvents
  have h := (prespecifiedBatchPooledPilotCoordinate_iIndepFun
    theta b hphysical K j).measure_inter_preimage_eq_mul
      Finset.univ (fun i _ => hEvents i)
  simpa using h

/-- The enumerated pooled sign average is exactly the implemented weighted
pooled pilot. -/
theorem prespecifiedBatchPooledPilot_sampleAverage_eq
    (K : Nat) (hK : 0 < K) (j : Fin 3)
    (omega : ExactConcretePredeterminedBatchPrefix K) :
    hoeffdingSampleAverage
        (fun i : Fin (prespecifiedBatchPooledPilotBlocks K) =>
          fun omega : ExactConcretePredeterminedBatchPrefix K =>
            let shot := prespecifiedBatchPooledPilotShotEquiv K i
            pauliOutcomeSign
              (prespecifiedBatchPrefixPilot K shot.1 omega shot.2 j)) omega =
      prespecifiedBatchPooledPilot K omega j := by
  have hq : 0 < prespecifiedBatchPooledPilotBlocks K := by
    rw [prespecifiedBatchPooledPilotBlocks_eq]
    positivity
  have hqne : (prespecifiedBatchPooledPilotBlocks K : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hq)
  have hden : prespecifiedBatchPooledPilotDenominator K =
      (prespecifiedBatchPooledPilotBlocks K : Real) := by
    unfold prespecifiedBatchPooledPilotDenominator
    rw [Nat.max_eq_right (by omega)]
  have hsum :
      (∑ i : Fin (prespecifiedBatchPooledPilotBlocks K),
        let shot := prespecifiedBatchPooledPilotShotEquiv K i
        pauliOutcomeSign
          (prespecifiedBatchPrefixPilot K shot.1 omega shot.2 j)) =
      ∑ shot : PrespecifiedBatchPooledPilotShot K,
        pauliOutcomeSign
          (prespecifiedBatchPrefixPilot K shot.1 omega shot.2 j) := by
    exact Fintype.sum_equiv (prespecifiedBatchPooledPilotShotEquiv K)
      _ _ (fun _ => rfl)
  unfold hoeffdingSampleAverage prespecifiedBatchPooledPilot
  rw [hsum, hden]
  simp only [Fintype.sum_sigma]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  unfold pauliPilotEstimate pauliPilotCoordinateSum
    prespecifiedBatchPrefixPilot
  have hkne : (exactConcreteBatchPilotBlocks k : Real) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (exactConcreteBatchPilotBlocks_pos k)
  field_simp [hqne, hkne]

/-- Every enumerated pooled sign has exact Born mean `theta j` under the
native finite-prefix product law. -/
theorem prespecifiedBatchPooledPilotCoordinate_integral
    (theta b : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (K : Nat) (j : Fin 3)
    (i : Fin (prespecifiedBatchPooledPilotBlocks K)) :
    (∫ omega,
      (let shot := prespecifiedBatchPooledPilotShotEquiv K i
       pauliOutcomeSign
        (prespecifiedBatchPrefixPilot K shot.1 omega shot.2 j))
      ∂prespecifiedBatchEstimatorPrefixMeasure theta b K) = theta j := by
  let shot := prespecifiedBatchPooledPilotShotEquiv K i
  have hmap := prespecifiedBatchPrefixMeasure_map_pilot
    theta b hphysical K shot.1
  have hIntegralMap := integral_map_of_stronglyMeasurable
    (μ := prespecifiedBatchEstimatorPrefixMeasure theta b K)
    (φ := prespecifiedBatchPrefixPilot K shot.1)
    (f := fun path : PauliPilotPath
        (exactConcreteBatchPilotBlocks shot.1) =>
      pauliOutcomeSign (path shot.2 j))
    Measurable.of_discrete StronglyMeasurable.of_discrete
  rw [hmap] at hIntegralMap
  change (∫ omega,
      pauliOutcomeSign
        (prespecifiedBatchPrefixPilot K shot.1 omega shot.2 j)
      ∂prespecifiedBatchEstimatorPrefixMeasure theta b K) = theta j
  rw [← hIntegralMap]
  simpa [pauliPilotCoordinateVariable] using
    integral_pauliPilotCoordinateVariable_eq
      theta hphysical j shot.2

/-- Positive-sign Hoeffding data for the exact pooled pilot. -/
noncomputable def prespecifiedBatchPooledPilotPositiveHoeffdingData
    (theta b : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (K : Nat) (hK : 0 < K) (j : Fin 3) :
    HoeffdingTheorem2Data
      (Ω := ExactConcretePredeterminedBatchPrefix K)
      (prespecifiedBatchPooledPilotBlocks K) where
  μ := prespecifiedBatchEstimatorPrefixMeasure theta b K
  X := fun i omega =>
    let shot := prespecifiedBatchPooledPilotShotEquiv K i
    pauliOutcomeSign
      (prespecifiedBatchPrefixPilot K shot.1 omega shot.2 j)
  lower := fun _ => -1
  upper := fun _ => 1
  nonemptyFamily := by
    rw [prespecifiedBatchPooledPilotBlocks_eq]
    positivity
  probabilityMeasure := by
    letI := prespecifiedBatchEstimatorPrefixMeasure_isProbability
      theta b hphysical K
    exact measure_univ
  measurableVariable := fun _ => Measurable.of_discrete
  integrableVariable := fun _ => by
    letI := prespecifiedBatchEstimatorPrefixMeasure_isProbability
      theta b hphysical K
    exact Integrable.of_finite
  independent := prespecifiedBatchPooledPilotCoordinate_finiteIndependent
    theta b hphysical K j
  orderedBounds := fun _ => by norm_num
  boundedAlmostEverywhere := fun i =>
    Filter.Eventually.of_forall (fun omega => by
      let shot := prespecifiedBatchPooledPilotShotEquiv K i
      change (-1 : Real) <= pauliOutcomeSign
          (prespecifiedBatchPrefixPilot K shot.1 omega shot.2 j) /\
        pauliOutcomeSign
          (prespecifiedBatchPrefixPilot K shot.1 omega shot.2 j) <= 1
      cases h : prespecifiedBatchPrefixPilot K shot.1 omega shot.2 j <;>
        norm_num [pauliOutcomeSign, h])

/-- Negative-sign Hoeffding data for the exact pooled pilot. -/
noncomputable def prespecifiedBatchPooledPilotNegativeHoeffdingData
    (theta b : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (K : Nat) (hK : 0 < K) (j : Fin 3) :
    HoeffdingTheorem2Data
      (Ω := ExactConcretePredeterminedBatchPrefix K)
      (prespecifiedBatchPooledPilotBlocks K) :=
  let positive := prespecifiedBatchPooledPilotPositiveHoeffdingData
    theta b hphysical K hK j
  { positive with
    X := fun i omega => -positive.X i omega
    measurableVariable := fun i => (positive.measurableVariable i).neg
    integrableVariable := fun i => (positive.integrableVariable i).neg
    independent := finiteIndependentRealFamily_neg positive.μ positive.X
      positive.independent
    boundedAlmostEverywhere := fun i =>
      Filter.Eventually.of_forall (fun omega => by
        let shot := prespecifiedBatchPooledPilotShotEquiv K i
        change (-1 : Real) <= -pauliOutcomeSign
            (prespecifiedBatchPrefixPilot K shot.1 omega shot.2 j) /\
          -pauliOutcomeSign
            (prespecifiedBatchPrefixPilot K shot.1 omega shot.2 j) <= 1
        cases h : prespecifiedBatchPrefixPilot K shot.1 omega shot.2 j <;>
          norm_num [pauliOutcomeSign, h]) }

/-- Exact pooled-sign mean average. -/
theorem prespecifiedBatchPooledPilot_meanAverage_eq
    (theta b : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (K : Nat) (hK : 0 < K) (j : Fin 3) :
    hoeffdingMeanAverage
      (prespecifiedBatchEstimatorPrefixMeasure theta b K)
      (prespecifiedBatchPooledPilotPositiveHoeffdingData
        theta b hphysical K hK j).X = theta j := by
  unfold hoeffdingMeanAverage
  dsimp [prespecifiedBatchPooledPilotPositiveHoeffdingData]
  simp_rw [prespecifiedBatchPooledPilotCoordinate_integral
    theta b hphysical K j]
  have hq : (prespecifiedBatchPooledPilotBlocks K : Real) ≠ 0 := by
    rw [prespecifiedBatchPooledPilotBlocks_eq]
    positivity
  simp [hq]

private theorem hoeffdingMeanAverage_neg
    {Omega : Type*} [MeasurableSpace Omega] {n : Nat}
    (mu : Measure Omega) (X : Fin n -> Omega -> Real) :
    hoeffdingMeanAverage mu (fun i omega => -X i omega) =
      -hoeffdingMeanAverage mu X := by
  unfold hoeffdingMeanAverage
  simp_rw [integral_neg]
  rw [Finset.sum_neg_distrib]
  ring

private theorem hoeffdingSampleAverage_neg
    {Omega : Type*} {n : Nat} (X : Fin n -> Omega -> Real)
    (omega : Omega) :
    hoeffdingSampleAverage (fun i omega => -X i omega) omega =
      -hoeffdingSampleAverage X omega := by
  unfold hoeffdingSampleAverage
  rw [Finset.sum_neg_distrib]
  ring

/-- Exact two-sided pooled-pilot coordinate concentration under the actual
finite-prefix Born product law. -/
theorem prespecifiedBatchPooledPilot_coordinate_tail
    (theta b : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (K : Nat) (hK : 0 < K) (j : Fin 3)
    (t : Real) (ht : 0 < t) :
    prespecifiedBatchEstimatorPrefixMeasure theta b K
        {omega | t <= |prespecifiedBatchPooledPilot K omega j - theta j|} <=
      2 * ENNReal.ofReal
        (Real.exp (-(prespecifiedBatchPooledPilotBlocks K : Real) *
          t ^ 2 / 2)) := by
  let pos := prespecifiedBatchPooledPilotPositiveHoeffdingData
    theta b hphysical K hK j
  let neg := prespecifiedBatchPooledPilotNegativeHoeffdingData
    theta b hphysical K hK j
  have hPos := hoeffding1963Theorem2_of_mathlib pos t ht
  have hNeg := hoeffding1963Theorem2_of_mathlib neg t ht
  unfold HoeffdingTheorem2Conclusion at hPos hNeg
  dsimp [pos] at hPos
  dsimp [neg] at hNeg
  have hMean := prespecifiedBatchPooledPilot_meanAverage_eq
    theta b hphysical K hK j
  have hSample (omega : ExactConcretePredeterminedBatchPrefix K) :
      hoeffdingSampleAverage pos.X omega =
        prespecifiedBatchPooledPilot K omega j :=
    prespecifiedBatchPooledPilot_sampleAverage_eq K hK j omega
  dsimp [prespecifiedBatchPooledPilotPositiveHoeffdingData] at hPos
  dsimp [prespecifiedBatchPooledPilotNegativeHoeffdingData,
    prespecifiedBatchPooledPilotPositiveHoeffdingData] at hNeg
  have hMean' :
      hoeffdingMeanAverage
        (prespecifiedBatchEstimatorPrefixMeasure theta b K)
        (fun i omega =>
          pauliOutcomeSign
            (prespecifiedBatchPrefixPilot K
              (prespecifiedBatchPooledPilotShotEquiv K i).1 omega
              (prespecifiedBatchPooledPilotShotEquiv K i).2 j)) = theta j := by
    simpa [prespecifiedBatchPooledPilotPositiveHoeffdingData] using hMean
  have hSample' (omega : ExactConcretePredeterminedBatchPrefix K) :
      hoeffdingSampleAverage
        (fun i omega =>
          pauliOutcomeSign
            (prespecifiedBatchPrefixPilot K
              (prespecifiedBatchPooledPilotShotEquiv K i).1 omega
              (prespecifiedBatchPooledPilotShotEquiv K i).2 j)) omega =
        prespecifiedBatchPooledPilot K omega j := by
    simpa [pos, prespecifiedBatchPooledPilotPositiveHoeffdingData] using
      hSample omega
  have hNegMean' :
      hoeffdingMeanAverage
        (prespecifiedBatchEstimatorPrefixMeasure theta b K)
        (fun i omega =>
          -pauliOutcomeSign
            (prespecifiedBatchPrefixPilot K
              (prespecifiedBatchPooledPilotShotEquiv K i).1 omega
              (prespecifiedBatchPooledPilotShotEquiv K i).2 j)) = -theta j := by
    rw [hoeffdingMeanAverage_neg, hMean']
  have hNegSample' (omega : ExactConcretePredeterminedBatchPrefix K) :
      hoeffdingSampleAverage
        (fun i omega =>
          -pauliOutcomeSign
            (prespecifiedBatchPrefixPilot K
              (prespecifiedBatchPooledPilotShotEquiv K i).1 omega
              (prespecifiedBatchPooledPilotShotEquiv K i).2 j)) omega =
        -prespecifiedBatchPooledPilot K omega j := by
    rw [hoeffdingSampleAverage_neg, hSample']
  rw [hMean'] at hPos
  simp_rw [hSample'] at hPos
  rw [hNegMean'] at hNeg
  simp_rw [hNegSample'] at hNeg
  rw [pauliPilot_hoeffdingExponent
      (prespecifiedBatchPooledPilotBlocks K)
      (by rw [prespecifiedBatchPooledPilotBlocks_eq]; positivity) t] at hPos hNeg
  let upper := {omega : ExactConcretePredeterminedBatchPrefix K |
    theta j + t <= prespecifiedBatchPooledPilot K omega j}
  let lower := {omega : ExactConcretePredeterminedBatchPrefix K |
    prespecifiedBatchPooledPilot K omega j <= theta j - t}
  have hsubset :
      {omega | t <= |prespecifiedBatchPooledPilot K omega j - theta j|} <=
        upper ∪ lower := by
    intro omega homega
    change t <= |prespecifiedBatchPooledPilot K omega j - theta j| at homega
    rw [le_abs] at homega
    rcases homega with homega | homega
    · exact Or.inl (by dsimp [upper]; linarith)
    · exact Or.inr (by dsimp [lower]; linarith)
  have hPos' : prespecifiedBatchEstimatorPrefixMeasure theta b K upper <=
      ENNReal.ofReal (Real.exp
        (-(prespecifiedBatchPooledPilotBlocks K : Real) * t ^ 2 / 2)) := by
    simpa [pos, upper] using hPos
  have hNeg' : prespecifiedBatchEstimatorPrefixMeasure theta b K lower <=
      ENNReal.ofReal (Real.exp
        (-(prespecifiedBatchPooledPilotBlocks K : Real) * t ^ 2 / 2)) := by
    have hset :
        {omega : ExactConcretePredeterminedBatchPrefix K |
          -theta j + t <= -prespecifiedBatchPooledPilot K omega j} = lower := by
      ext omega
      change (-theta j + t <= -prespecifiedBatchPooledPilot K omega j) <->
        prespecifiedBatchPooledPilot K omega j <= theta j - t
      constructor <;> intro h <;> linarith
    rw [← hset]
    exact hNeg
  calc
    prespecifiedBatchEstimatorPrefixMeasure theta b K
        {omega | t <= |prespecifiedBatchPooledPilot K omega j - theta j|} <=
      prespecifiedBatchEstimatorPrefixMeasure theta b K (upper ∪ lower) :=
        measure_mono hsubset
    _ <= prespecifiedBatchEstimatorPrefixMeasure theta b K upper +
        prespecifiedBatchEstimatorPrefixMeasure theta b K lower :=
      measure_union_le _ _
    _ <= ENNReal.ofReal (Real.exp
          (-(prespecifiedBatchPooledPilotBlocks K : Real) * t ^ 2 / 2)) +
        ENNReal.ofReal (Real.exp
          (-(prespecifiedBatchPooledPilotBlocks K : Real) * t ^ 2 / 2)) :=
      add_le_add hPos' hNeg'
    _ = 2 * ENNReal.ofReal (Real.exp
          (-(prespecifiedBatchPooledPilotBlocks K : Real) * t ^ 2 / 2)) := by ring

/-! ## Deterministic pilot threshold and sample scale -/

/-- Threshold used for the pooled pilot: `(K+1)^(-7/4)`. -/
noncomputable def prespecifiedBatchPilotDelta (K : Nat) : Real :=
  Real.rpow ((K : Real) + 1) (-(7 / 4 : Real))

theorem prespecifiedBatchPilotDelta_pos (K : Nat) :
    0 < prespecifiedBatchPilotDelta K := by
  unfold prespecifiedBatchPilotDelta
  exact Real.rpow_pos_of_pos (by positivity) _

theorem prespecifiedBatchPilotDelta_tendsto_zero :
    Tendsto prespecifiedBatchPilotDelta atTop (nhds 0) := by
  have hbase : Tendsto (fun K : Nat => (K : Real) + 1) atTop atTop := by
    rw [tendsto_atTop]
    intro a
    filter_upwards
      [(tendsto_atTop.1 tendsto_natCast_atTop_atTop) a] with K hK
    linarith
  exact (tendsto_rpow_neg_atTop
    (by norm_num : (0 : Real) < 7 / 4)).comp hbase

/-- The exact final sample scale is `27 K^3`. -/
theorem prespecifiedBatchSampleScale_eq (K : Nat) :
    prespecifiedBatchSampleScale K = 27 * (K : Real) ^ 3 := by
  unfold prespecifiedBatchSampleScale prespecifiedBatchTotalObservations
  rw [exactConcreteBatchSize_cumulative]
  have hnonneg : (0 : Real) <= 27 * (K : Real) ^ 3 := by positivity
  rw [show (((3 * K) ^ 6 : Nat) : Real) =
      (27 * (K : Real) ^ 3) ^ 2 by push_cast; ring]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg]

/-- Squaring the chosen threshold gives the exact exponent `-7/2`. -/
theorem prespecifiedBatchPilotDelta_sq (K : Nat) :
    prespecifiedBatchPilotDelta K ^ 2 =
      Real.rpow ((K : Real) + 1) (-(7 / 2 : Real)) := by
  unfold prespecifiedBatchPilotDelta
  calc
    Real.rpow ((K : Real) + 1) (-(7 / 4 : Real)) ^ 2 =
        Real.rpow ((K : Real) + 1) (-(7 / 4 : Real) * 2) :=
      (Real.rpow_mul_natCast (by positivity)
        (-(7 / 4 : Real)) 2).symm
    _ = Real.rpow ((K : Real) + 1) (-(7 / 2 : Real)) := by norm_num

/-- The pilot is fast enough for a one-step Taylor remainder:
`sqrt(N_K) delta_K^2 -> 0`. -/
theorem prespecifiedBatchSampleScale_mul_delta_sq_tendsto_zero :
    Tendsto
      (fun K => prespecifiedBatchSampleScale K *
        prespecifiedBatchPilotDelta K ^ 2)
      atTop (nhds 0) := by
  let upper : Nat -> Real := fun K =>
    27 * Real.rpow ((K : Real) + 1) (-(1 / 2 : Real))
  have hUpper : Tendsto upper atTop (nhds 0) := by
    have hbase : Tendsto (fun K : Nat => (K : Real) + 1) atTop atTop := by
      rw [tendsto_atTop]
      intro a
      filter_upwards
        [(tendsto_atTop.1 tendsto_natCast_atTop_atTop) a] with K hK
      linarith
    have hc : Tendsto (fun _ : Nat => (27 : Real)) atTop (nhds 27) :=
      tendsto_const_nhds
    have hp : Tendsto
        (fun K : Nat => Real.rpow ((K : Real) + 1) (-(1 / 2 : Real)))
        atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop
        (by norm_num : (0 : Real) < 1 / 2)).comp hbase
    simpa [upper] using hc.mul hp
  apply squeeze_zero' ?_ ?_ hUpper
  · filter_upwards with K
    exact mul_nonneg (by rw [prespecifiedBatchSampleScale_eq]; positivity)
      (sq_nonneg _)
  · filter_upwards with K
    rw [prespecifiedBatchSampleScale_eq,
      prespecifiedBatchPilotDelta_sq]
    have hx : 0 < (K : Real) + 1 := by positivity
    have hKpow : (K : Real) ^ 3 <= ((K : Real) + 1) ^ 3 := by
      gcongr
      linarith
    have hneg : 0 <= Real.rpow ((K : Real) + 1) (-(7 / 2 : Real)) :=
      Real.rpow_nonneg hx.le _
    calc
      27 * (K : Real) ^ 3 *
          Real.rpow ((K : Real) + 1) (-(7 / 2 : Real)) <=
        27 * (((K : Real) + 1) ^ 3) *
          Real.rpow ((K : Real) + 1) (-(7 / 2 : Real)) := by
            gcongr
      _ = 27 * Real.rpow ((K : Real) + 1) (-(1 / 2 : Real)) := by
        rw [← Real.rpow_natCast ((K : Real) + 1) 3]
        calc
          27 * Real.rpow ((K : Real) + 1) (3 : Real) *
              Real.rpow ((K : Real) + 1) (-(7 / 2 : Real)) =
            27 * (Real.rpow ((K : Real) + 1) (3 : Real) *
              Real.rpow ((K : Real) + 1) (-(7 / 2 : Real))) := by ring
          _ = 27 * Real.rpow ((K : Real) + 1)
              ((3 : Real) + (-(7 / 2 : Real))) := by
            congr 1
            exact (Real.rpow_add hx (3 : Real) (-(7 / 2 : Real))).symm
          _ = 27 * Real.rpow ((K : Real) + 1) (-(1 / 2 : Real)) := by
            norm_num
      _ = upper K := rfl

/-- Three coordinatewise pilot bounds imply the exact finite-dimensional
squared-error envelope `3 delta^2`. -/
theorem prespecifiedBatchPooledPilot_blochError_le_three_delta_sq
    (K : Nat) (theta : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K)
    (hcoord : forall j : Fin 3,
      |prespecifiedBatchPooledPilot K omega j - theta j| <=
        prespecifiedBatchPilotDelta K) :
    QubitOracle.blochNormSq
        (fun j => prespecifiedBatchPooledPilot K omega j - theta j) <=
      3 * prespecifiedBatchPilotDelta K ^ 2 := by
  have hsq (j : Fin 3) :
      (prespecifiedBatchPooledPilot K omega j - theta j) ^ 2 <=
        prespecifiedBatchPilotDelta K ^ 2 := by
    have habs := hcoord j
    have hdelta := (prespecifiedBatchPilotDelta_pos K).le
    have habs0 : 0 <=
        |prespecifiedBatchPooledPilot K omega j - theta j| := abs_nonneg _
    nlinarith [sq_abs (prespecifiedBatchPooledPilot K omega j - theta j)]
  unfold QubitOracle.blochNormSq
  simp only [Fin.sum_univ_three]
  nlinarith [hsq 0, hsq 1, hsq 2]

/-- The deterministic root-sample-size quadratic pilot envelope tends to
zero.  This is the rate consumed by second-order Taylor/Newton defects. -/
theorem prespecifiedBatchSampleScale_mul_three_delta_sq_tendsto_zero :
    Tendsto
      (fun K => prespecifiedBatchSampleScale K *
        (3 * prespecifiedBatchPilotDelta K ^ 2))
      atTop (nhds 0) := by
  have h := (tendsto_const_nhds :
    Tendsto (fun _ : Nat => (3 : Real)) atTop (nhds 3)).mul
      prespecifiedBatchSampleScale_mul_delta_sq_tendsto_zero
  convert h using 1 <;> ring

/-- On the concrete coordinate-good event, the root-sample-size quadratic
pilot error is bounded by the vanishing deterministic envelope. -/
theorem prespecifiedBatchPooledPilot_scaledBlochError_le
    (K : Nat) (theta : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K)
    (hcoord : forall j : Fin 3,
      |prespecifiedBatchPooledPilot K omega j - theta j| <=
        prespecifiedBatchPilotDelta K) :
    prespecifiedBatchSampleScale K *
        QubitOracle.blochNormSq
          (fun j => prespecifiedBatchPooledPilot K omega j - theta j) <=
      prespecifiedBatchSampleScale K *
        (3 * prespecifiedBatchPilotDelta K ^ 2) := by
  exact mul_le_mul_of_nonneg_left
    (prespecifiedBatchPooledPilot_blochError_le_three_delta_sq
      K theta omega hcoord)
    (by rw [prespecifiedBatchSampleScale_eq]; positivity)

/-- Any trajectory sequence which is eventually coordinate-good has
root-sample-size quadratic pilot error tending to zero. -/
theorem prespecifiedBatchPooledPilot_scaledBlochError_tendsto_zero
    (theta : RLSVector 3)
    (omega : forall K : Nat, ExactConcretePredeterminedBatchPrefix K)
    (hcoord : ∀ᶠ K : Nat in atTop, forall j : Fin 3,
      |prespecifiedBatchPooledPilot K (omega K) j - theta j| <=
        prespecifiedBatchPilotDelta K) :
    Tendsto
      (fun K => prespecifiedBatchSampleScale K *
        QubitOracle.blochNormSq
          (fun j => prespecifiedBatchPooledPilot K (omega K) j - theta j))
      atTop (nhds 0) := by
  apply squeeze_zero' ?_ ?_
    prespecifiedBatchSampleScale_mul_three_delta_sq_tendsto_zero
  · filter_upwards with K
    exact mul_nonneg
      (by rw [prespecifiedBatchSampleScale_eq]; positivity)
      (by
        unfold QubitOracle.blochNormSq
        exact Finset.sum_nonneg (fun j _ => sq_nonneg _))
  · filter_upwards [hcoord] with K hK
    exact prespecifiedBatchPooledPilot_scaledBlochError_le
      K theta (omega K) hK

/-- The revised squared ridge times the pilot threshold has exact power
`(K+1)^(-15/4)`. -/
theorem prespecifiedBatchRidge_mul_pilotDelta (K : Nat) :
    prespecifiedBatchRidge K * prespecifiedBatchPilotDelta K =
      Real.rpow ((K : Real) + 1) (-(15 / 4 : Real)) := by
  unfold prespecifiedBatchRidge prespecifiedBatchPilotDelta
  have hx : 0 < (K : Real) + 1 := by positivity
  rw [show ((((K + 1 : Nat) : Real) ^ 2)⁻¹) =
      Real.rpow ((K : Real) + 1) (-(2 : Real)) by
    rw [Nat.cast_add, Nat.cast_one, ← Real.rpow_natCast]
    exact (Real.rpow_neg hx.le (2 : Real)).symm]
  calc
    Real.rpow ((K : Real) + 1) (-(2 : Real)) *
        Real.rpow ((K : Real) + 1) (-(7 / 4 : Real)) =
      Real.rpow ((K : Real) + 1)
        ((-(2 : Real)) + (-(7 / 4 : Real))) :=
      (Real.rpow_add hx (-(2 : Real)) (-(7 / 4 : Real))).symm
    _ = Real.rpow ((K : Real) + 1) (-(15 / 4 : Real)) := by norm_num

/-- The deterministic envelope for the ridge contribution to the normalized
Newton defect tends to zero. -/
theorem prespecifiedBatchSampleScale_mul_ridge_mul_delta_tendsto_zero :
    Tendsto
      (fun K => prespecifiedBatchSampleScale K * prespecifiedBatchRidge K *
        prespecifiedBatchPilotDelta K)
      atTop (nhds 0) := by
  let upper : Nat -> Real := fun K =>
    27 * Real.rpow ((K : Real) + 1) (-(3 / 4 : Real))
  have hUpper : Tendsto upper atTop (nhds 0) := by
    have hbase : Tendsto (fun K : Nat => (K : Real) + 1) atTop atTop := by
      rw [tendsto_atTop]
      intro a
      filter_upwards
        [(tendsto_atTop.1 tendsto_natCast_atTop_atTop) a] with K hK
      linarith
    have hp : Tendsto
        (fun K : Nat => Real.rpow ((K : Real) + 1) (-(3 / 4 : Real)))
        atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop
        (by norm_num : (0 : Real) < 3 / 4)).comp hbase
    simpa [upper] using
      (tendsto_const_nhds.mul hp : Tendsto
        (fun K : Nat => 27 *
          Real.rpow ((K : Real) + 1) (-(3 / 4 : Real)))
        atTop (nhds (27 * 0)))
  apply squeeze_zero' ?_ ?_ hUpper
  · filter_upwards with K
    exact mul_nonneg
      (mul_nonneg
        (by rw [prespecifiedBatchSampleScale_eq]; positivity)
        (prespecifiedBatchRidge_pos K).le)
      (prespecifiedBatchPilotDelta_pos K).le
  · filter_upwards with K
    rw [mul_assoc, prespecifiedBatchRidge_mul_pilotDelta,
      prespecifiedBatchSampleScale_eq]
    have hx : 0 < (K : Real) + 1 := by positivity
    have hKpow : (K : Real) ^ 3 <= ((K : Real) + 1) ^ 3 := by
      gcongr
      linarith
    have hneg : 0 <= Real.rpow ((K : Real) + 1) (-(15 / 4 : Real)) :=
      Real.rpow_nonneg hx.le _
    calc
      27 * (K : Real) ^ 3 *
          Real.rpow ((K : Real) + 1) (-(15 / 4 : Real)) <=
        27 * (((K : Real) + 1) ^ 3) *
          Real.rpow ((K : Real) + 1) (-(15 / 4 : Real)) := by
            gcongr
      _ = 27 * Real.rpow ((K : Real) + 1) (-(3 / 4 : Real)) := by
        rw [← Real.rpow_natCast ((K : Real) + 1) 3]
        calc
          27 * Real.rpow ((K : Real) + 1) (3 : Real) *
              Real.rpow ((K : Real) + 1) (-(15 / 4 : Real)) =
            27 * (Real.rpow ((K : Real) + 1) (3 : Real) *
              Real.rpow ((K : Real) + 1) (-(15 / 4 : Real))) := by ring
          _ = 27 * Real.rpow ((K : Real) + 1)
              ((3 : Real) + (-(15 / 4 : Real))) := by
            congr 1
            exact (Real.rpow_add hx (3 : Real) (-(15 / 4 : Real))).symm
          _ = 27 * Real.rpow ((K : Real) + 1) (-(3 / 4 : Real)) := by
            norm_num
      _ = upper K := rfl

/-- On the coordinate-good event, the Euclidean Bloch pilot error is at most
`3 delta_K`; this deliberately uses a simple rational constant. -/
theorem prespecifiedBatchPooledPilot_sqrtBlochError_le_three_delta
    (K : Nat) (theta : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K)
    (hcoord : forall j : Fin 3,
      |prespecifiedBatchPooledPilot K omega j - theta j| <=
        prespecifiedBatchPilotDelta K) :
    Real.sqrt (QubitOracle.blochNormSq
      (fun j => prespecifiedBatchPooledPilot K omega j - theta j)) <=
      3 * prespecifiedBatchPilotDelta K := by
  have hq0 : 0 <= QubitOracle.blochNormSq
      (fun j => prespecifiedBatchPooledPilot K omega j - theta j) := by
    unfold QubitOracle.blochNormSq
    exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hq := prespecifiedBatchPooledPilot_blochError_le_three_delta_sq
    K theta omega hcoord
  have hsqrt := Real.sq_sqrt hq0
  have hdelta := (prespecifiedBatchPilotDelta_pos K).le
  have hsqrt0 := Real.sqrt_nonneg (QubitOracle.blochNormSq
    (fun j => prespecifiedBatchPooledPilot K omega j - theta j))
  nlinarith

/-- Pathwise good-event bound for the revised ridge contribution. -/
theorem prespecifiedBatchPooledPilot_scaledRidgeError_le
    (K : Nat) (theta : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K)
    (hcoord : forall j : Fin 3,
      |prespecifiedBatchPooledPilot K omega j - theta j| <=
        prespecifiedBatchPilotDelta K) :
    prespecifiedBatchSampleScale K * prespecifiedBatchRidge K *
        Real.sqrt (QubitOracle.blochNormSq
          (fun j => prespecifiedBatchPooledPilot K omega j - theta j)) <=
      3 * (prespecifiedBatchSampleScale K * prespecifiedBatchRidge K *
        prespecifiedBatchPilotDelta K) := by
  have hscale : 0 <=
      prespecifiedBatchSampleScale K * prespecifiedBatchRidge K :=
    mul_nonneg
      (by rw [prespecifiedBatchSampleScale_eq]; positivity)
      (prespecifiedBatchRidge_pos K).le
  have h := mul_le_mul_of_nonneg_left
    (prespecifiedBatchPooledPilot_sqrtBlochError_le_three_delta
      K theta omega hcoord) hscale
  nlinarith

/-- Along any eventually coordinate-good trajectory, the implemented ridge
times the root-sample-size Euclidean pilot error tends to zero. -/
theorem prespecifiedBatchPooledPilot_scaledRidgeError_tendsto_zero
    (theta : RLSVector 3)
    (omega : forall K : Nat, ExactConcretePredeterminedBatchPrefix K)
    (hcoord : ∀ᶠ K : Nat in atTop, forall j : Fin 3,
      |prespecifiedBatchPooledPilot K (omega K) j - theta j| <=
        prespecifiedBatchPilotDelta K) :
    Tendsto
      (fun K => prespecifiedBatchSampleScale K * prespecifiedBatchRidge K *
        Real.sqrt (QubitOracle.blochNormSq
          (fun j => prespecifiedBatchPooledPilot K (omega K) j - theta j)))
      atTop (nhds 0) := by
  have hUpper := (tendsto_const_nhds : Tendsto
      (fun _ : Nat => (3 : Real)) atTop (nhds 3)).mul
    prespecifiedBatchSampleScale_mul_ridge_mul_delta_tendsto_zero
  apply squeeze_zero' ?_ ?_ (by simpa [mul_assoc] using hUpper)
  · filter_upwards with K
    exact mul_nonneg
      (mul_nonneg
        (by rw [prespecifiedBatchSampleScale_eq]; positivity)
        (prespecifiedBatchRidge_pos K).le)
      (Real.sqrt_nonneg _)
  · filter_upwards [hcoord] with K hK
    simpa [mul_assoc] using
      (prespecifiedBatchPooledPilot_scaledRidgeError_le
        K theta (omega K) hK)

/-- A coordinatewise pilot event forces strict interiority whenever its
deterministic threshold is below the displayed truth margin. -/
theorem prespecifiedBatchPooledPilot_strictInterior_of_coordinate_bound
    (K : Nat) (theta : RLSVector 3)
    (hphysical : PauliPilotPhysicalBloch theta)
    (omega : ExactConcretePredeterminedBatchPrefix K)
    (hcoord : forall j : Fin 3,
      |prespecifiedBatchPooledPilot K omega j - theta j| <=
        prespecifiedBatchPilotDelta K)
    (hmargin : QubitOracle.blochNormSq theta +
        6 * prespecifiedBatchPilotDelta K +
        3 * prespecifiedBatchPilotDelta K ^ 2 < 1) :
    QubitOracle.blochNormSq (prespecifiedBatchPooledPilot K omega) < 1 := by
  have hdelta := (prespecifiedBatchPilotDelta_pos K).le
  have hsq (j : Fin 3) :
      prespecifiedBatchPooledPilot K omega j ^ 2 <=
        theta j ^ 2 + 2 * prespecifiedBatchPilotDelta K +
          prespecifiedBatchPilotDelta K ^ 2 := by
    have habs := hcoord j
    have ht := pauliPilotPhysicalBloch_coordinate_bounds theta hphysical j
    have hlower :
        -prespecifiedBatchPilotDelta K <=
          prespecifiedBatchPooledPilot K omega j - theta j :=
      (neg_le_of_abs_le habs)
    have hupper :
        prespecifiedBatchPooledPilot K omega j - theta j <=
          prespecifiedBatchPilotDelta K :=
      (le_of_abs_le habs)
    nlinarith [sq_nonneg
      (prespecifiedBatchPooledPilot K omega j - theta j),
      sq_nonneg (theta j + 1), sq_nonneg (theta j - 1)]
  unfold QubitOracle.blochNormSq at hmargin ⊢
  simp only [Fin.sum_univ_three] at hmargin ⊢
  nlinarith [hsq 0, hsq 1, hsq 2]

/-- For every strict-interior truth, the deterministic pilot threshold is
eventually small enough to trigger the preceding interiority theorem. -/
theorem prespecifiedBatchPilot_interiorMargin_eventually
    (theta : RLSVector 3) (hInterior : QubitOracle.blochNormSq theta < 1) :
    ∀ᶠ K : Nat in atTop,
      QubitOracle.blochNormSq theta +
          6 * prespecifiedBatchPilotDelta K +
          3 * prespecifiedBatchPilotDelta K ^ 2 < 1 := by
  have hpoly : Tendsto
      (fun K => 6 * prespecifiedBatchPilotDelta K +
        3 * prespecifiedBatchPilotDelta K ^ 2)
      atTop (nhds 0) := by
    have hdelta := prespecifiedBatchPilotDelta_tendsto_zero
    convert (tendsto_const_nhds.mul hdelta).add
      (tendsto_const_nhds.mul (hdelta.pow 2)) using 1 <;> norm_num
  have hsum : Tendsto
      (fun K => QubitOracle.blochNormSq theta +
        (6 * prespecifiedBatchPilotDelta K +
          3 * prespecifiedBatchPilotDelta K ^ 2))
      atTop (nhds (QubitOracle.blochNormSq theta)) := by
    simpa using tendsto_const_nhds.add hpoly
  simpa [add_assoc] using (tendsto_order.1 hsum).2 (1 : Real) hInterior

/-! ## Summable pilot/interiority rejection envelope -/

/-- The union-bound envelope for all three pooled-pilot coordinates at the
chosen threshold. -/
noncomputable def prespecifiedBatchPooledPilotVectorTail (K : Nat) : Real :=
  6 * Real.exp
    (-(prespecifiedBatchPooledPilotBlocks K : Real) *
      prespecifiedBatchPilotDelta K ^ 2 / 2)

/-- The exact Hoeffding exponent dominates a positive constant times
`sqrt(K+1)`. -/
theorem prespecifiedBatchPooledPilot_exponent_ge_sqrt
    (K : Nat) (hK : 1 <= K) :
    (prespecifiedBatchPooledPilotBlocks K : Real) *
        prespecifiedBatchPilotDelta K ^ 2 / 2 >=
      (27 / 32 : Real) *
        Real.rpow ((K : Real) + 1) (1 / 2 : Real) := by
  rw [prespecifiedBatchPooledPilotBlocks_eq,
    prespecifiedBatchPilotDelta_sq]
  push_cast
  have hx : 0 < (K : Real) + 1 := by positivity
  have hk : (1 : Real) <= K := by exact_mod_cast hK
  have hxle : (K : Real) + 1 <= 2 * (K : Real) := by linarith
  have hpow : ((K : Real) + 1) ^ 4 <= 16 * (K : Real) ^ 4 := by
    calc
      ((K : Real) + 1) ^ 4 <= (2 * (K : Real)) ^ 4 := by gcongr
      _ = 16 * (K : Real) ^ 4 := by ring
  have hrnonneg : 0 <=
      Real.rpow ((K : Real) + 1) (-(7 / 2 : Real)) :=
    Real.rpow_nonneg hx.le _
  calc
    (27 * K ^ 4 : Real) *
          Real.rpow ((K : Real) + 1) (-(7 / 2 : Real)) / 2 =
        (27 / 2 : Real) * (K : Real) ^ 4 *
          Real.rpow ((K : Real) + 1) (-(7 / 2 : Real)) := by ring
    _ >= (27 / 32 : Real) * (((K : Real) + 1) ^ 4) *
          Real.rpow ((K : Real) + 1) (-(7 / 2 : Real)) := by
      have hk4 : ((K : Real) + 1) ^ 4 / 16 <= (K : Real) ^ 4 := by
        linarith
      have hm := mul_le_mul_of_nonneg_right hk4 hrnonneg
      calc
        (27 / 32 : Real) * (((K : Real) + 1) ^ 4) *
            Real.rpow ((K : Real) + 1) (-(7 / 2 : Real)) =
          (27 / 2 : Real) * ((((K : Real) + 1) ^ 4 / 16) *
            Real.rpow ((K : Real) + 1) (-(7 / 2 : Real))) := by ring
        _ <= (27 / 2 : Real) * ((K : Real) ^ 4 *
            Real.rpow ((K : Real) + 1) (-(7 / 2 : Real))) :=
          mul_le_mul_of_nonneg_left hm (by norm_num)
        _ = (27 / 2 : Real) * (K : Real) ^ 4 *
            Real.rpow ((K : Real) + 1) (-(7 / 2 : Real)) := by ring
    _ = (27 / 32 : Real) *
          Real.rpow ((K : Real) + 1) (1 / 2 : Real) := by
      rw [← Real.rpow_natCast ((K : Real) + 1) 4]
      calc
        (27 / 32 : Real) *
            Real.rpow ((K : Real) + 1) (4 : Real) *
              Real.rpow ((K : Real) + 1) (-(7 / 2 : Real)) =
          (27 / 32 : Real) *
            (Real.rpow ((K : Real) + 1) (4 : Real) *
              Real.rpow ((K : Real) + 1) (-(7 / 2 : Real))) := by ring
        _ = (27 / 32 : Real) *
            Real.rpow ((K : Real) + 1)
              ((4 : Real) + (-(7 / 2 : Real))) := by
          congr 1
          exact (Real.rpow_add hx (4 : Real) (-(7 / 2 : Real))).symm
        _ = (27 / 32 : Real) *
            Real.rpow ((K : Real) + 1) (1 / 2 : Real) := by norm_num

/-- The exact three-coordinate Hoeffding envelopes are summable. -/
theorem prespecifiedBatchPooledPilotVectorTail_summable :
    Summable prespecifiedBatchPooledPilotVectorTail := by
  have hpSeries : Summable (fun K : Nat =>
      6 * (1 / |(K : Real) + 1| ^ (2 : Real))) :=
    ((Real.summable_one_div_nat_add_rpow 1 2).2 (by norm_num)).mul_left 6
  apply hpSeries.of_norm_bounded_eventually_nat
  have hbase : Tendsto (fun K : Nat => (K : Real) + 1) atTop atTop := by
    rw [tendsto_atTop]
    intro a
    filter_upwards
      [(tendsto_atTop.1 tendsto_natCast_atTop_atTop) a] with K hK
    linarith
  have hlogReal :=
    ((isLittleO_log_rpow_atTop
      (by norm_num : (0 : Real) < 1 / 2)).def
        (by norm_num : (0 : Real) < 27 / 64))
  have hlogNat := hbase.eventually hlogReal
  filter_upwards [hlogNat, eventually_ge_atTop (1 : Nat)] with K hlog hK
  have hx : 0 < (K : Real) + 1 := by positivity
  have hkReal : (1 : Real) <= K := by exact_mod_cast hK
  have hlog0 : 0 <= Real.log ((K : Real) + 1) :=
    Real.log_nonneg (by linarith)
  have hr0 : 0 <= Real.rpow ((K : Real) + 1) (1 / 2 : Real) :=
    Real.rpow_nonneg hx.le _
  have hlogBound :
      2 * Real.log ((K : Real) + 1) <=
        (27 / 32 : Real) *
          Real.rpow ((K : Real) + 1) (1 / 2 : Real) := by
    have hlog' : Real.log ((K : Real) + 1) <=
        (27 / 64 : Real) *
          Real.rpow ((K : Real) + 1) (1 / 2 : Real) := by
      change ‖Real.log ((K : Real) + 1)‖ <=
        (27 / 64 : Real) *
          ‖Real.rpow ((K : Real) + 1) (1 / 2 : Real)‖ at hlog
      simpa only [Real.norm_of_nonneg hlog0, Real.norm_of_nonneg hr0] using hlog
    nlinarith
  have hexponent := prespecifiedBatchPooledPilot_exponent_ge_sqrt K hK
  have hExpLe :
      Real.exp
          (-(prespecifiedBatchPooledPilotBlocks K : Real) *
            prespecifiedBatchPilotDelta K ^ 2 / 2) <=
        Real.rpow ((K : Real) + 1) (-(2 : Real)) := by
    calc
      Real.exp
          (-(prespecifiedBatchPooledPilotBlocks K : Real) *
            prespecifiedBatchPilotDelta K ^ 2 / 2) <=
        Real.exp (-2 * Real.log ((K : Real) + 1)) := by
          apply Real.exp_le_exp.mpr
          linarith
      _ = Real.rpow ((K : Real) + 1) (-(2 : Real)) := by
        calc
          Real.exp (-2 * Real.log ((K : Real) + 1)) =
              Real.exp (Real.log ((K : Real) + 1) * (-(2 : Real))) := by
            congr 1
            ring
          _ = Real.rpow ((K : Real) + 1) (-(2 : Real)) :=
            (Real.rpow_def_of_pos hx (-(2 : Real))).symm
  change |prespecifiedBatchPooledPilotVectorTail K| <=
    6 * (1 / |(K : Real) + 1| ^ (2 : Real))
  rw [abs_of_nonneg (by unfold prespecifiedBatchPooledPilotVectorTail; positivity)]
  unfold prespecifiedBatchPooledPilotVectorTail
  have habsx : |(K : Real) + 1| = (K : Real) + 1 := abs_of_pos hx
  have hcomp : 1 / |(K : Real) + 1| ^ (2 : Real) =
      Real.rpow ((K : Real) + 1) (-(2 : Real)) := by
    rw [habsx]
    calc
      1 / Real.rpow ((K : Real) + 1) (2 : Real) =
          (Real.rpow ((K : Real) + 1) (2 : Real))⁻¹ := by rw [one_div]
      _ = Real.rpow ((K : Real) + 1) (-(2 : Real)) :=
        (Real.rpow_neg hx.le (2 : Real)).symm
  rw [hcomp]
  gcongr

/-- Failure of at least one of the three pooled-pilot coordinate bounds. -/
def prespecifiedBatchPooledPilotBadEvent
    (K : Nat) (theta : RLSVector 3) :
    Set (ExactConcretePredeterminedBatchPrefix K) :=
  {omega | exists j : Fin 3,
    prespecifiedBatchPilotDelta K <=
      |prespecifiedBatchPooledPilot K omega j - theta j|}

/-- Under the exact finite-prefix Born product law, the three-coordinate bad
event has the summable union-bound envelope above. -/
theorem prespecifiedBatchPooledPilotBadEvent_measure_le
    (theta b : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (K : Nat) :
    prespecifiedBatchEstimatorPrefixMeasure theta b K
        (prespecifiedBatchPooledPilotBadEvent K theta) <=
      ENNReal.ofReal (prespecifiedBatchPooledPilotVectorTail K) := by
  by_cases hK : K = 0
  · subst K
    letI : IsProbabilityMeasure
        (prespecifiedBatchEstimatorPrefixMeasure theta b 0) :=
      prespecifiedBatchEstimatorPrefixMeasure_isProbability
        theta b hphysical 0
    calc
      prespecifiedBatchEstimatorPrefixMeasure theta b 0
          (prespecifiedBatchPooledPilotBadEvent 0 theta) <=
          prespecifiedBatchEstimatorPrefixMeasure theta b 0 Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ <= ENNReal.ofReal (prespecifiedBatchPooledPilotVectorTail 0) := by
        simp [prespecifiedBatchPooledPilotVectorTail,
          prespecifiedBatchPooledPilotBlocks]
  · have hKpos : 0 < K := Nat.pos_of_ne_zero hK
    let event : Fin 3 -> Set (ExactConcretePredeterminedBatchPrefix K) :=
      fun j => {omega |
        prespecifiedBatchPilotDelta K <=
          |prespecifiedBatchPooledPilot K omega j - theta j|}
    have hEvent : prespecifiedBatchPooledPilotBadEvent K theta =
        Set.iUnion event := by
      ext omega
      simp [prespecifiedBatchPooledPilotBadEvent, event]
    rw [hEvent]
    calc
      prespecifiedBatchEstimatorPrefixMeasure theta b K (Set.iUnion event) <=
          ∑' j : Fin 3,
            prespecifiedBatchEstimatorPrefixMeasure theta b K (event j) :=
        measure_iUnion_le _
      _ <= ∑' _j : Fin 3,
          2 * ENNReal.ofReal
            (Real.exp (-(prespecifiedBatchPooledPilotBlocks K : Real) *
              prespecifiedBatchPilotDelta K ^ 2 / 2)) := by
        gcongr with j
        exact prespecifiedBatchPooledPilot_coordinate_tail
          theta b hphysical K hKpos j (prespecifiedBatchPilotDelta K)
            (prespecifiedBatchPilotDelta_pos K)
      _ = ENNReal.ofReal (prespecifiedBatchPooledPilotVectorTail K) := by
        rw [show (∑' _j : Fin 3,
            2 * ENNReal.ofReal
              (Real.exp (-(prespecifiedBatchPooledPilotBlocks K : Real) *
                prespecifiedBatchPilotDelta K ^ 2 / 2))) =
              6 * ENNReal.ofReal
                (Real.exp (-(prespecifiedBatchPooledPilotBlocks K : Real) *
                  prespecifiedBatchPilotDelta K ^ 2 / 2)) by simp; ring]
        unfold prespecifiedBatchPooledPilotVectorTail
        rw [ENNReal.ofReal_mul (by norm_num : (0 : Real) <= 6)]
        norm_num

/-- The exact finite-prefix probabilities of pooled-pilot coordinate failure
have finite total mass. -/
theorem prespecifiedBatchPooledPilotBadEvent_tsum_ne_top
    (theta b : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta) :
    (∑' K : Nat, prespecifiedBatchEstimatorPrefixMeasure theta b K
      (prespecifiedBatchPooledPilotBadEvent K theta)) ≠ (⊤ : ENNReal) := by
  have htail :
      (∑' K : Nat, ENNReal.ofReal
        (prespecifiedBatchPooledPilotVectorTail K)) ≠ (⊤ : ENNReal) :=
    prespecifiedBatchPooledPilotVectorTail_summable.tsum_ofReal_ne_top
  exact ne_top_of_le_ne_top htail
    (ENNReal.tsum_le_tsum (fun K =>
      prespecifiedBatchPooledPilotBadEvent_measure_le
        theta b hphysical K))

/-- Pilot-side rejection of strict Bloch-ball interiority. -/
def prespecifiedBatchPilotInteriorityRejectionEvent
    (K : Nat) (theta : RLSVector 3) :
    Set (ExactConcretePredeterminedBatchPrefix K) :=
  {omega | ¬
    (QubitOracle.blochNormSq (prespecifiedBatchPooledPilot K omega) < 1)}

/-- For a strict-interior truth, pilot interiority rejection is eventually
contained in the three-coordinate Hoeffding bad event. -/
theorem prespecifiedBatchPilotInteriorityRejection_subset_eventually
    (theta : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (hInterior : QubitOracle.blochNormSq theta < 1) :
    ∀ᶠ K : Nat in atTop,
      prespecifiedBatchPilotInteriorityRejectionEvent K theta <=
        prespecifiedBatchPooledPilotBadEvent K theta := by
  filter_upwards
    [prespecifiedBatchPilot_interiorMargin_eventually theta hInterior]
      with K hmargin
  intro omega hreject
  change ¬ QubitOracle.blochNormSq
    (prespecifiedBatchPooledPilot K omega) < 1 at hreject
  by_contra hbad
  have hcoord : forall j : Fin 3,
      |prespecifiedBatchPooledPilot K omega j - theta j| <=
        prespecifiedBatchPilotDelta K := by
    intro j
    have hj : ¬ (prespecifiedBatchPilotDelta K <=
        |prespecifiedBatchPooledPilot K omega j - theta j|) := by
      intro hj
      exact hbad (by
        exact ⟨j, hj⟩)
    exact (lt_of_not_ge hj).le
  exact hreject
    (prespecifiedBatchPooledPilot_strictInterior_of_coordinate_bound
      K theta hphysical omega hcoord hmargin)

/-- Exact-law probability of pilot interiority rejection is eventually bounded
by the same summable Hoeffding envelope. -/
theorem prespecifiedBatchPilotInteriorityRejection_measure_le_eventually
    (theta b : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (hInterior : QubitOracle.blochNormSq theta < 1) :
    ∀ᶠ K : Nat in atTop,
      prespecifiedBatchEstimatorPrefixMeasure theta b K
          (prespecifiedBatchPilotInteriorityRejectionEvent K theta) <=
        ENNReal.ofReal (prespecifiedBatchPooledPilotVectorTail K) := by
  filter_upwards
    [prespecifiedBatchPilotInteriorityRejection_subset_eventually
      theta hphysical hInterior] with K hsubset
  exact le_trans (measure_mono hsubset)
    (prespecifiedBatchPooledPilotBadEvent_measure_le
      theta b hphysical K)

/-- The real probabilities of pilot interiority rejection are summable. -/
theorem prespecifiedBatchPilotInteriorityRejection_measureReal_summable
    (theta b : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (hInterior : QubitOracle.blochNormSq theta < 1) :
    Summable (fun K : Nat =>
      (prespecifiedBatchEstimatorPrefixMeasure theta b K
        (prespecifiedBatchPilotInteriorityRejectionEvent K theta)).toReal) := by
  apply prespecifiedBatchPooledPilotVectorTail_summable.of_norm_bounded_eventually_nat
  filter_upwards
    [prespecifiedBatchPilotInteriorityRejection_measure_le_eventually
      theta b hphysical hInterior] with K hle
  calc
    ‖(prespecifiedBatchEstimatorPrefixMeasure theta b K
        (prespecifiedBatchPilotInteriorityRejectionEvent K theta)).toReal‖ =
      (prespecifiedBatchEstimatorPrefixMeasure theta b K
        (prespecifiedBatchPilotInteriorityRejectionEvent K theta)).toReal :=
        Real.norm_of_nonneg ENNReal.toReal_nonneg
    _ <=
      (ENNReal.ofReal (prespecifiedBatchPooledPilotVectorTail K)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    _ = prespecifiedBatchPooledPilotVectorTail K :=
      ENNReal.toReal_ofReal (by
        unfold prespecifiedBatchPooledPilotVectorTail
        positivity)

/-- Multiplying pilot/interiority rejection probabilities by any fixed bounded
fallback-loss envelope preserves summability. -/
theorem prespecifiedBatchBoundedFallbackEnvelope_summable
    (theta b : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (hInterior : QubitOracle.blochNormSq theta < 1) (C : Real) :
    Summable (fun K : Nat => C *
      (prespecifiedBatchEstimatorPrefixMeasure theta b K
        (prespecifiedBatchPilotInteriorityRejectionEvent K theta)).toReal) :=
  (prespecifiedBatchPilotInteriorityRejection_measureReal_summable
    theta b hphysical hInterior).mul_left C

/-! ## One-shot score calculus for the final estimator bridge -/

/-- One coordinate of the binary score, written as a function of the scalar
axis overlap.  For `z = a dot x` this is the coordinate form of
`a * (y - a dot x) / (1 - (a dot x)^2)`. -/
def prespecifiedBatchBernoulliOverlapScore
    (z : Real) (axis : RLSVector 3) (outcome : Bool) (i : Fin 3) : Real :=
  pauliOutcomeSign outcome * axis i /
    (1 + pauliOutcomeSign outcome * z)

/-- The literal quotient-rule derivative produced by Mathlib. -/
def prespecifiedBatchBernoulliOverlapScoreDerivativeRaw
    (z : Real) (axis : RLSVector 3) (outcome : Bool) (i : Fin 3) : Real :=
  (0 * (1 + pauliOutcomeSign outcome * z) -
      pauliOutcomeSign outcome * axis i * pauliOutcomeSign outcome) /
    (1 + pauliOutcomeSign outcome * z) ^ 2

/-- Direct one-shot differentiability of every score coordinate. -/
theorem prespecifiedBatchBernoulliOverlapScore_hasDerivAt
    (z : Real) (axis : RLSVector 3) (outcome : Bool) (i : Fin 3)
    (hden : 1 + pauliOutcomeSign outcome * z ≠ 0) :
    HasDerivAt
      (fun q : Real =>
        prespecifiedBatchBernoulliOverlapScore q axis outcome i)
      (prespecifiedBatchBernoulliOverlapScoreDerivativeRaw
        z axis outcome i) z := by
  unfold prespecifiedBatchBernoulliOverlapScore
    prespecifiedBatchBernoulliOverlapScoreDerivativeRaw
  change HasDerivAt
    ((fun _q : Real => pauliOutcomeSign outcome * axis i) /
      (fun q : Real => 1 + pauliOutcomeSign outcome * q))
    ((0 * (1 + pauliOutcomeSign outcome * z) -
      pauliOutcomeSign outcome * axis i * pauliOutcomeSign outcome) /
      (1 + pauliOutcomeSign outcome * z) ^ 2) z
  have hnum : HasDerivAt
      (fun _q : Real => pauliOutcomeSign outcome * axis i) 0 z :=
    hasDerivAt_const z _
  have hden' : HasDerivAt
      (fun q : Real => 1 + pauliOutcomeSign outcome * q)
      (pauliOutcomeSign outcome) z := by
    simpa only [id_eq, mul_one] using
      (((hasDerivAt_id (x := z)).const_mul
        (pauliOutcomeSign outcome)).const_add 1)
  exact hnum.div hden' hden

/-- The derivative is exactly minus the observed score-outer-information
coefficient before multiplication by the perturbation-axis coordinate. -/
theorem prespecifiedBatchBernoulliOverlapScoreDerivativeRaw_eq
    (z : Real) (axis : RLSVector 3) (outcome : Bool) (i : Fin 3) :
    prespecifiedBatchBernoulliOverlapScoreDerivativeRaw z axis outcome i =
      -(axis i) / (1 + pauliOutcomeSign outcome * z) ^ 2 := by
  unfold prespecifiedBatchBernoulliOverlapScoreDerivativeRaw
  have hs : pauliOutcomeSign outcome * pauliOutcomeSign outcome = 1 :=
    pauliOutcomeSign_mul_self outcome
  have hprod : pauliOutcomeSign outcome * axis i *
      pauliOutcomeSign outcome = axis i := by
    calc
      pauliOutcomeSign outcome * axis i * pauliOutcomeSign outcome =
          (pauliOutcomeSign outcome * pauliOutcomeSign outcome) * axis i := by
        ring
      _ = axis i := by rw [hs, one_mul]
  rw [hprod]
  ring

/-- One observed score-outer-information matrix entry. -/
def prespecifiedBatchBernoulliObservedOuterEntry
    (z : Real) (axis : RLSVector 3) (outcome : Bool)
    (i j : Fin 3) : Real :=
  axis i * axis j /
    (1 + pauliOutcomeSign outcome * z) ^ 2

/-- Chain rule in a coordinate direction: the score derivative is minus the
observed score-outer-information entry. -/
theorem prespecifiedBatchBernoulliScoreDerivative_eq_neg_observedOuter
    (z : Real) (axis : RLSVector 3) (outcome : Bool) (i j : Fin 3) :
    prespecifiedBatchBernoulliOverlapScoreDerivativeRaw
        z axis outcome i * axis j =
      -prespecifiedBatchBernoulliObservedOuterEntry
        z axis outcome i j := by
  rw [prespecifiedBatchBernoulliOverlapScoreDerivativeRaw_eq]
  unfold prespecifiedBatchBernoulliObservedOuterEntry
  ring

/-- Raw quotient-rule value for the second overlap derivative. -/
def prespecifiedBatchBernoulliOverlapScoreSecondDerivativeRaw
    (z : Real) (axis : RLSVector 3) (outcome : Bool) (i : Fin 3) : Real :=
  (0 * (1 + pauliOutcomeSign outcome * z) ^ 2 -
      (-(axis i)) *
        ((2 : Real) * (1 + pauliOutcomeSign outcome * z) ^ (2 - 1) *
          pauliOutcomeSign outcome)) /
    ((1 + pauliOutcomeSign outcome * z) ^ 2) ^ 2

/-- Direct second differentiability of the one-shot score. -/
theorem prespecifiedBatchBernoulliOverlapScore_firstDerivative_hasDerivAt
    (z : Real) (axis : RLSVector 3) (outcome : Bool) (i : Fin 3)
    (hden : 1 + pauliOutcomeSign outcome * z ≠ 0) :
    HasDerivAt
      ((fun _q : Real => -(axis i)) /
        (fun q : Real => 1 + pauliOutcomeSign outcome * q) ^ 2)
      (prespecifiedBatchBernoulliOverlapScoreSecondDerivativeRaw
        z axis outcome i) z := by
  unfold prespecifiedBatchBernoulliOverlapScoreSecondDerivativeRaw
  have hn : HasDerivAt (fun _q : Real => -(axis i)) 0 z :=
    hasDerivAt_const z _
  have hd : HasDerivAt
      (fun q : Real => 1 + pauliOutcomeSign outcome * q)
      (pauliOutcomeSign outcome) z := by
    simpa only [id_eq, mul_one] using
      (((hasDerivAt_id (x := z)).const_mul
        (pauliOutcomeSign outcome)).const_add 1)
  exact hn.div (hd.pow 2) (pow_ne_zero 2 hden)

/-- Closed form of the second overlap derivative. -/
theorem prespecifiedBatchBernoulliOverlapScoreSecondDerivativeRaw_eq
    (z : Real) (axis : RLSVector 3) (outcome : Bool) (i : Fin 3)
    (hden : 1 + pauliOutcomeSign outcome * z ≠ 0) :
    prespecifiedBatchBernoulliOverlapScoreSecondDerivativeRaw
        z axis outcome i =
      2 * pauliOutcomeSign outcome * axis i /
        (1 + pauliOutcomeSign outcome * z) ^ 3 := by
  unfold prespecifiedBatchBernoulliOverlapScoreSecondDerivativeRaw
  field_simp [hden]
  ring

/-- Uniform second-derivative envelope over every unit axis and Bool outcome
whenever a common positive denominator floor is available. -/
theorem prespecifiedBatchBernoulliOverlapScoreSecondDerivative_abs_le
    (z floor : Real) (axis : RLSVector 3) (outcome : Bool) (i : Fin 3)
    (hfloor : 0 < floor)
    (hdenFloor : floor <= 1 + pauliOutcomeSign outcome * z)
    (haxis : QubitOracle.blochNormSq axis = 1) :
    |2 * pauliOutcomeSign outcome * axis i /
        (1 + pauliOutcomeSign outcome * z) ^ 3| <=
      2 / floor ^ 3 := by
  have hden : 0 < 1 + pauliOutcomeSign outcome * z :=
    lt_of_lt_of_le hfloor hdenFloor
  have hai := unitBlochAxis_coordinate_abs_le_one axis haxis i
  have hsign : |pauliOutcomeSign outcome| = 1 := by
    cases outcome <;> norm_num [pauliOutcomeSign]
  have htwo : |(2 : Real)| = 2 := abs_of_pos (by norm_num)
  rw [abs_div, abs_mul, abs_mul, hsign, htwo, abs_pow, abs_of_pos hden]
  simp only [mul_one]
  calc
    2 * |axis i| / (1 + pauliOutcomeSign outcome * z) ^ 3 <=
        2 * 1 / (1 + pauliOutcomeSign outcome * z) ^ 3 := by
      gcongr
    _ <= 2 / floor ^ 3 := by
      gcongr <;> norm_num

/-- Exact one-shot quadratic score remainder.  This identity is stronger than
a Taylor existence statement and is the form summed over the finite prefix. -/
theorem prespecifiedBatchBernoulliOverlapScore_exact_quadratic_remainder
    (z d : Real) (axis : RLSVector 3) (outcome : Bool) (i : Fin 3)
    (hden : 1 + pauliOutcomeSign outcome * z ≠ 0)
    (hden' : 1 + pauliOutcomeSign outcome * (z + d) ≠ 0) :
    prespecifiedBatchBernoulliOverlapScore (z + d) axis outcome i -
        prespecifiedBatchBernoulliOverlapScore z axis outcome i +
        axis i * d / (1 + pauliOutcomeSign outcome * z) ^ 2 =
      pauliOutcomeSign outcome * axis i * d ^ 2 /
        ((1 + pauliOutcomeSign outcome * (z + d)) *
          (1 + pauliOutcomeSign outcome * z) ^ 2) := by
  unfold prespecifiedBatchBernoulliOverlapScore
  have hs : pauliOutcomeSign outcome ^ 2 = 1 := by
    cases outcome <;> norm_num [pauliOutcomeSign]
  have hs3 : pauliOutcomeSign outcome ^ 3 =
      pauliOutcomeSign outcome := by
    calc
      pauliOutcomeSign outcome ^ 3 =
          pauliOutcomeSign outcome * pauliOutcomeSign outcome ^ 2 := by ring
      _ = pauliOutcomeSign outcome := by rw [hs, mul_one]
  field_simp [hden, hden']
  ring_nf
  rw [hs, hs3]
  ring

/-! ## Exact finite dependent shot sum -/

/-- Every pilot shot and exploitation shot in the first `K` batches, with the
row-dependent shot counts retained in the type. -/
abbrev PrespecifiedBatchEstimatorShotIndex (K : Nat) :=
  (Sigma fun k : Fin K =>
    Fin (exactConcreteBatchPilotBlocks k) × Fin 3) ⊕
  (Sigma fun k : Fin K =>
    Fin (3 * exactConcreteBatchFinalBlocks k))

/-- The literal axis used by a finite-prefix shot. -/
def prespecifiedBatchEstimatorShotAxis
    (K : Nat) (b : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K) :
    PrespecifiedBatchEstimatorShotIndex K -> RLSVector 3
  | Sum.inl ⟨_k, shot⟩ => prespecifiedBatchPauliAxis shot.2
  | Sum.inr ⟨k, t⟩ =>
      mixedTwoStageFinalAxis
        (exactConcreteBatchSelectedFrame k b) (omega k).1 t

/-- The literal Bool outcome attached to a finite-prefix shot. -/
def prespecifiedBatchEstimatorShotOutcome
    (K : Nat) (omega : ExactConcretePredeterminedBatchPrefix K) :
    PrespecifiedBatchEstimatorShotIndex K -> Bool
  | Sum.inl ⟨k, shot⟩ => (omega k).1 shot.1 shot.2
  | Sum.inr ⟨k, t⟩ => (omega k).2 t

/-- Every axis in the flattened exact prefix is a unit Bloch axis. -/
theorem prespecifiedBatchEstimatorShotAxis_unit
    (K : Nat) (b : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K)
    (s : PrespecifiedBatchEstimatorShotIndex K) :
    QubitOracle.blochNormSq
      (prespecifiedBatchEstimatorShotAxis K b omega s) = 1 := by
  cases s with
  | inl s =>
      rcases s with ⟨k, shot⟩
      rcases shot with ⟨r, j⟩
      fin_cases j <;>
        simp [prespecifiedBatchEstimatorShotAxis,
          prespecifiedBatchPauliAxis, QubitOracle.blochNormSq,
          Fin.sum_univ_succ]
  | inr s =>
      simpa [prespecifiedBatchEstimatorShotAxis] using
        (mixedTwoStageFinalAxis_unit
          (exactConcreteBatchSelectedFrame s.1 b) (omega s.1).1 s.2)

theorem prespecifiedBatchPauliAxis_blochDot
    (i : Fin 3) (axis : RLSVector 3) :
    QubitOracle.blochDot (prespecifiedBatchPauliAxis i) axis = axis i := by
  unfold QubitOracle.blochDot prespecifiedBatchPauliAxis
  fin_cases i <;> simp

/-- A flattened score summand is exactly the existing directional-score
summand in the corresponding standard coordinate. -/
theorem prespecifiedBatchEstimatorShotScore_eq_directional
    (K : Nat) (b x : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K)
    (s : PrespecifiedBatchEstimatorShotIndex K) (i : Fin 3) :
    prespecifiedBatchBernoulliOverlapScore
        (QubitOracle.blochDot x
          (prespecifiedBatchEstimatorShotAxis K b omega s))
        (prespecifiedBatchEstimatorShotAxis K b omega s)
        (prespecifiedBatchEstimatorShotOutcome K omega s) i =
      mixedTwoStageAxisDirectionalScore x
        (prespecifiedBatchPauliAxis i)
        (prespecifiedBatchEstimatorShotAxis K b omega s)
        (prespecifiedBatchEstimatorShotOutcome K omega s) := by
  unfold prespecifiedBatchBernoulliOverlapScore
    mixedTwoStageAxisDirectionalScore
  rw [prespecifiedBatchPauliAxis_blochDot]

/-- The flattened finite sum is definitionally the pilot score plus the final
score used by the implemented estimator. -/
theorem prespecifiedBatchEstimatorShotScore_sum_eq
    (K : Nat) (b x : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K) (i : Fin 3) :
    (∑ s : PrespecifiedBatchEstimatorShotIndex K,
      prespecifiedBatchBernoulliOverlapScore
        (QubitOracle.blochDot x
          (prespecifiedBatchEstimatorShotAxis K b omega s))
        (prespecifiedBatchEstimatorShotAxis K b omega s)
        (prespecifiedBatchEstimatorShotOutcome K omega s) i) =
      prespecifiedBatchPilotScoreCoordinate K x omega i +
        prespecifiedBatchFinalScoreCoordinate K b x omega i := by
  classical
  unfold prespecifiedBatchPilotScoreCoordinate
    prespecifiedBatchFinalScoreCoordinate
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type]
  simp_rw [prespecifiedBatchEstimatorShotScore_eq_directional]
  unfold mixedTwoStageFinalPathDirectionalScoreSum
    mixedTwoStageFinalPathDirectionalScore
    prespecifiedBatchEstimatorShotAxis
    prespecifiedBatchEstimatorShotOutcome
  rfl

/-- Consequently the exact flattened score sum is the coordinate of the
implemented unnormalized prefix score. -/
theorem prespecifiedBatchEstimatorShotScore_sum_eq_score
    (K : Nat) (b x : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K) (i : Fin 3) :
    (∑ s : PrespecifiedBatchEstimatorShotIndex K,
      prespecifiedBatchBernoulliOverlapScore
        (QubitOracle.blochDot x
          (prespecifiedBatchEstimatorShotAxis K b omega s))
        (prespecifiedBatchEstimatorShotAxis K b omega s)
        (prespecifiedBatchEstimatorShotOutcome K omega s) i) =
      prespecifiedBatchScore K b x omega i := by
  rw [prespecifiedBatchEstimatorShotScore_sum_eq]
  rfl

/-- The exact quadratic score identity summed over an arbitrary finite row.
This is the deterministic finite-sample bridge used below with the dependent
prespecified-batch shot type. -/
theorem prespecifiedBatchBernoulliOverlapScore_sum_exact_quadratic_remainder
    {Shot : Type} [Fintype Shot]
    (z d : Shot -> Real) (axis : Shot -> RLSVector 3)
    (outcome : Shot -> Bool) (i : Fin 3)
    (hden : forall s, 1 + pauliOutcomeSign (outcome s) * z s ≠ 0)
    (hden' : forall s,
      1 + pauliOutcomeSign (outcome s) * (z s + d s) ≠ 0) :
    (∑ s : Shot,
      (prespecifiedBatchBernoulliOverlapScore
          (z s + d s) (axis s) (outcome s) i -
        prespecifiedBatchBernoulliOverlapScore
          (z s) (axis s) (outcome s) i +
        axis s i * d s /
          (1 + pauliOutcomeSign (outcome s) * z s) ^ 2)) =
      ∑ s : Shot,
        pauliOutcomeSign (outcome s) * axis s i * d s ^ 2 /
          ((1 + pauliOutcomeSign (outcome s) * (z s + d s)) *
            (1 + pauliOutcomeSign (outcome s) * z s) ^ 2) := by
  apply Finset.sum_congr rfl
  intro s _hs
  exact prespecifiedBatchBernoulliOverlapScore_exact_quadratic_remainder
    (z s) (d s) (axis s) (outcome s) i (hden s) (hden' s)

/-- Exact all-shot Taylor identity for the concrete prespecified prefix.  The
only hypotheses are strict interiority of the truth and evaluation point. -/
theorem prespecifiedBatchEstimatorShotScore_sum_exact_quadratic_remainder
    (K : Nat) (theta b x : RLSVector 3)
    (omega : ExactConcretePredeterminedBatchPrefix K) (i : Fin 3)
    (hTheta : QubitOracle.blochNormSq theta < 1)
    (hX : QubitOracle.blochNormSq x < 1) :
    (∑ s : PrespecifiedBatchEstimatorShotIndex K,
      (prespecifiedBatchBernoulliOverlapScore
          (QubitOracle.blochDot theta
            (prespecifiedBatchEstimatorShotAxis K b omega s) +
            QubitOracle.blochDot (fun j => x j - theta j)
              (prespecifiedBatchEstimatorShotAxis K b omega s))
          (prespecifiedBatchEstimatorShotAxis K b omega s)
          (prespecifiedBatchEstimatorShotOutcome K omega s) i -
        prespecifiedBatchBernoulliOverlapScore
          (QubitOracle.blochDot theta
            (prespecifiedBatchEstimatorShotAxis K b omega s))
          (prespecifiedBatchEstimatorShotAxis K b omega s)
          (prespecifiedBatchEstimatorShotOutcome K omega s) i +
        prespecifiedBatchEstimatorShotAxis K b omega s i *
            QubitOracle.blochDot (fun j => x j - theta j)
              (prespecifiedBatchEstimatorShotAxis K b omega s) /
          (1 + pauliOutcomeSign
              (prespecifiedBatchEstimatorShotOutcome K omega s) *
            QubitOracle.blochDot theta
              (prespecifiedBatchEstimatorShotAxis K b omega s)) ^ 2)) =
      ∑ s : PrespecifiedBatchEstimatorShotIndex K,
        pauliOutcomeSign
            (prespecifiedBatchEstimatorShotOutcome K omega s) *
          prespecifiedBatchEstimatorShotAxis K b omega s i *
          QubitOracle.blochDot (fun j => x j - theta j)
              (prespecifiedBatchEstimatorShotAxis K b omega s) ^ 2 /
        ((1 + pauliOutcomeSign
              (prespecifiedBatchEstimatorShotOutcome K omega s) *
            (QubitOracle.blochDot theta
                (prespecifiedBatchEstimatorShotAxis K b omega s) +
              QubitOracle.blochDot (fun j => x j - theta j)
                (prespecifiedBatchEstimatorShotAxis K b omega s))) *
          (1 + pauliOutcomeSign
              (prespecifiedBatchEstimatorShotOutcome K omega s) *
            QubitOracle.blochDot theta
              (prespecifiedBatchEstimatorShotAxis K b omega s)) ^ 2) := by
  apply prespecifiedBatchBernoulliOverlapScore_sum_exact_quadratic_remainder
  · intro s
    have hz := mixedTwoStageAxisOverlap_mem_Ioo theta
      (prespecifiedBatchEstimatorShotAxis K b omega s) hTheta
      (prespecifiedBatchEstimatorShotAxis_unit K b omega s)
    cases hOutcome : prespecifiedBatchEstimatorShotOutcome K omega s <;>
      simp [hOutcome, pauliOutcomeSign] <;> linarith
  · intro s
    have hdot :
        QubitOracle.blochDot theta
              (prespecifiedBatchEstimatorShotAxis K b omega s) +
            QubitOracle.blochDot (fun j => x j - theta j)
              (prespecifiedBatchEstimatorShotAxis K b omega s) =
          QubitOracle.blochDot x
            (prespecifiedBatchEstimatorShotAxis K b omega s) := by
      unfold QubitOracle.blochDot
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib]
      ring
    rw [hdot]
    have hz := mixedTwoStageAxisOverlap_mem_Ioo x
      (prespecifiedBatchEstimatorShotAxis K b omega s) hX
      (prespecifiedBatchEstimatorShotAxis_unit K b omega s)
    cases hOutcome : prespecifiedBatchEstimatorShotOutcome K omega s <;>
      simp [hOutcome, pauliOutcomeSign] <;> linarith

/-! ## Truth observed matrix and finite-dimensional polarization -/

def prespecifiedBatchPolarizationMatrix
    (Q : RLSVector 3 -> Real) : Matrix (Fin 3) (Fin 3) Real :=
  fun i j =>
    if i = j then Q (prespecifiedBatchCoordinateDirection i)
    else
      (Q (fun k => prespecifiedBatchCoordinateDirection i k +
          prespecifiedBatchCoordinateDirection j k) -
        Q (prespecifiedBatchCoordinateDirection i) -
        Q (prespecifiedBatchCoordinateDirection j)) / 2

def prespecifiedBatchPolarizedTruthFrameInformationMatrix
    (theta b : RLSVector 3) : Matrix (Fin 3) (Fin 3) Real :=
  prespecifiedBatchPolarizationMatrix
    (fun h => mixedPolynomialTruthFrameDirectionalInformation theta h b)

theorem prespecifiedBatchPolarizedTruthFrameInformationMatrix_eq
    (theta b : RLSVector 3) :
    prespecifiedBatchPolarizedTruthFrameInformationMatrix theta b =
      mixedPolynomialTruthFrameInformationMatrix theta b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [prespecifiedBatchPolarizedTruthFrameInformationMatrix,
      prespecifiedBatchPolarizationMatrix,
      prespecifiedBatchCoordinateDirection,
      mixedPolynomialTruthFrameInformationMatrix,
      mixedPolynomialTruthFrameDirectionalInformation,
      mixedPolynomialFrameDirectionalInformation,
      QubitOracle.blochDot, Fin.sum_univ_succ] <;> ring

/-- The normalized truth-evaluated observed information matrix reconstructed
from the exact directional observed-information statistic. -/
def prespecifiedBatchTruthObservedInformationMatrix
    (theta b : RLSVector 3) (K : Nat)
    (x : PrespecifiedBatchFinitePrefix K) :
    Matrix (Fin 3) (Fin 3) Real :=
  prespecifiedBatchPolarizationMatrix
    (fun h => prespecifiedBatchCumulativeObservedDirectionalInformation
      theta h b K x)

/-- Directional observed-information error relative to the limiting truth
frame information. -/
def prespecifiedBatchObservedDirectionalInformationError
    (theta b h : RLSVector 3) (K : Nat)
    (x : PrespecifiedBatchFinitePrefix K) : Real :=
  prespecifiedBatchCumulativeObservedDirectionalInformation theta h b K x -
    mixedPolynomialTruthFrameDirectionalInformation theta h b

theorem prespecifiedBatchTruthObservedInformationMatrix_diagonal_error
    (theta b : RLSVector 3) (K : Nat)
    (x : PrespecifiedBatchFinitePrefix K) (i : Fin 3) :
    prespecifiedBatchTruthObservedInformationMatrix theta b K x i i -
        mixedPolynomialTruthFrameInformationMatrix theta b i i =
      prespecifiedBatchObservedDirectionalInformationError theta b
        (prespecifiedBatchCoordinateDirection i) K x := by
  rw [← prespecifiedBatchPolarizedTruthFrameInformationMatrix_eq theta b]
  simp [prespecifiedBatchTruthObservedInformationMatrix,
    prespecifiedBatchPolarizedTruthFrameInformationMatrix,
    prespecifiedBatchPolarizationMatrix,
    prespecifiedBatchObservedDirectionalInformationError]

theorem prespecifiedBatchTruthObservedInformationMatrix_offDiagonal_error
    (theta b : RLSVector 3) (K : Nat)
    (x : PrespecifiedBatchFinitePrefix K)
    (i j : Fin 3) (hij : i ≠ j) :
    prespecifiedBatchTruthObservedInformationMatrix theta b K x i j -
        mixedPolynomialTruthFrameInformationMatrix theta b i j =
      (prespecifiedBatchObservedDirectionalInformationError theta b
          (fun k => prespecifiedBatchCoordinateDirection i k +
            prespecifiedBatchCoordinateDirection j k) K x -
        prespecifiedBatchObservedDirectionalInformationError theta b
          (prespecifiedBatchCoordinateDirection i) K x -
      prespecifiedBatchObservedDirectionalInformationError theta b
          (prespecifiedBatchCoordinateDirection j) K x) / 2 := by
  rw [← prespecifiedBatchPolarizedTruthFrameInformationMatrix_eq theta b]
  simp [prespecifiedBatchTruthObservedInformationMatrix,
    prespecifiedBatchPolarizedTruthFrameInformationMatrix,
    prespecifiedBatchPolarizationMatrix,
    prespecifiedBatchObservedDirectionalInformationError, hij]
  ring

/-- Entrywise convergence in probability for the truth observed matrix under
the row-dependent exact finite-prefix laws. -/
def PrespecifiedBatchTruthObservedMatrixConvergesEntrywiseInProbability
    (theta b : RLSVector 3) : Prop :=
  forall i j : Fin 3, forall epsilon : Real, 0 < epsilon ->
    Tendsto
      (fun K => prespecifiedBatchPrefixMeasure theta b K
        {x | epsilon <=
          |prespecifiedBatchTruthObservedInformationMatrix theta b K x i j -
            mixedPolynomialTruthFrameInformationMatrix theta b i j|})
      atTop (nhds 0)

/-- Gauss's closed all-direction theorem implies every entry of the exact
truth observed matrix converges to the Bures truth-frame matrix. -/
theorem prespecifiedBatchTruthObservedMatrix_convergesEntrywise_closed
    (theta b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    PrespecifiedBatchTruthObservedMatrixConvergesEntrywiseInProbability
      theta b := by
  intro i j epsilon hepsilon
  have hDirectional :=
    prespecifiedBatchObservedInformationConvergesInProbability_closed
      theta b hTruth hSeed
  by_cases hij : i = j
  · subst j
    simpa only
      [prespecifiedBatchTruthObservedInformationMatrix_diagonal_error,
        prespecifiedBatchObservedDirectionalInformationError] using
      hDirectional (prespecifiedBatchCoordinateDirection i) epsilon hepsilon
  · let ei := prespecifiedBatchCoordinateDirection i
    let ej := prespecifiedBatchCoordinateDirection j
    let eij : RLSVector 3 := fun k => ei k + ej k
    have hepsilonHalf : 0 < epsilon / 2 := by positivity
    have hA : Tendsto
        (fun K => prespecifiedBatchPrefixMeasure theta b K
          {x | epsilon / 2 <=
            |prespecifiedBatchObservedDirectionalInformationError
              theta b eij K x|}) atTop (nhds 0) := by
      simpa only [prespecifiedBatchObservedDirectionalInformationError] using
        hDirectional eij (epsilon / 2) hepsilonHalf
    have hI : Tendsto
        (fun K => prespecifiedBatchPrefixMeasure theta b K
          {x | epsilon / 2 <=
            |prespecifiedBatchObservedDirectionalInformationError
              theta b ei K x|}) atTop (nhds 0) := by
      simpa only [prespecifiedBatchObservedDirectionalInformationError] using
        hDirectional ei (epsilon / 2) hepsilonHalf
    have hJ : Tendsto
        (fun K => prespecifiedBatchPrefixMeasure theta b K
          {x | epsilon / 2 <=
            |prespecifiedBatchObservedDirectionalInformationError
              theta b ej K x|}) atTop (nhds 0) := by
      simpa only [prespecifiedBatchObservedDirectionalInformationError] using
        hDirectional ej (epsilon / 2) hepsilonHalf
    have hUpper : Tendsto
        (fun K =>
          prespecifiedBatchPrefixMeasure theta b K
              {x | epsilon / 2 <=
                |prespecifiedBatchObservedDirectionalInformationError
                  theta b eij K x|} +
            (prespecifiedBatchPrefixMeasure theta b K
                {x | epsilon / 2 <=
                  |prespecifiedBatchObservedDirectionalInformationError
                    theta b ei K x|} +
              prespecifiedBatchPrefixMeasure theta b K
                {x | epsilon / 2 <=
                  |prespecifiedBatchObservedDirectionalInformationError
                    theta b ej K x|})) atTop (nhds 0) := by
      simpa only [zero_add] using hA.add (hI.add hJ)
    apply Tendsto.squeeze tendsto_const_nhds hUpper
    · intro K
      exact bot_le
    · intro K
      let mu := prespecifiedBatchPrefixMeasure theta b K
      let EA : Set (PrespecifiedBatchFinitePrefix K) :=
        {x | epsilon / 2 <=
          |prespecifiedBatchObservedDirectionalInformationError
            theta b eij K x|}
      let EI : Set (PrespecifiedBatchFinitePrefix K) :=
        {x | epsilon / 2 <=
          |prespecifiedBatchObservedDirectionalInformationError
            theta b ei K x|}
      let EJ : Set (PrespecifiedBatchFinitePrefix K) :=
        {x | epsilon / 2 <=
          |prespecifiedBatchObservedDirectionalInformationError
            theta b ej K x|}
      calc
        mu {x | epsilon <=
              |prespecifiedBatchTruthObservedInformationMatrix
                  theta b K x i j -
                mixedPolynomialTruthFrameInformationMatrix theta b i j|} <=
            mu (EA ∪ (EI ∪ EJ)) := by
          apply measure_mono
          intro x hLarge
          by_cases hEA : x ∈ EA
          · exact Or.inl hEA
          by_cases hEI : x ∈ EI
          · exact Or.inr (Or.inl hEI)
          by_cases hEJ : x ∈ EJ
          · exact Or.inr (Or.inr hEJ)
          exfalso
          have hAabs :
              |prespecifiedBatchObservedDirectionalInformationError
                theta b eij K x| < epsilon / 2 := by
            exact lt_of_not_ge (by simpa [EA] using hEA)
          have hIabs :
              |prespecifiedBatchObservedDirectionalInformationError
                theta b ei K x| < epsilon / 2 := by
            exact lt_of_not_ge (by simpa [EI] using hEI)
          have hJabs :
              |prespecifiedBatchObservedDirectionalInformationError
                theta b ej K x| < epsilon / 2 := by
            exact lt_of_not_ge (by simpa [EJ] using hEJ)
          have hErrorEq :=
            prespecifiedBatchTruthObservedInformationMatrix_offDiagonal_error
              theta b K x i j hij
          change epsilon <=
            |prespecifiedBatchTruthObservedInformationMatrix theta b K x i j -
              mixedPolynomialTruthFrameInformationMatrix theta b i j| at hLarge
          rw [hErrorEq] at hLarge
          have hTriangle :
              |prespecifiedBatchObservedDirectionalInformationError
                    theta b eij K x -
                  prespecifiedBatchObservedDirectionalInformationError
                    theta b ei K x -
                  prespecifiedBatchObservedDirectionalInformationError
                    theta b ej K x| <=
                |prespecifiedBatchObservedDirectionalInformationError
                    theta b eij K x| +
                  |prespecifiedBatchObservedDirectionalInformationError
                    theta b ei K x| +
                  |prespecifiedBatchObservedDirectionalInformationError
                    theta b ej K x| := by
            calc
              |_ - _ - _| <=
                  |prespecifiedBatchObservedDirectionalInformationError
                    theta b eij K x -
                    prespecifiedBatchObservedDirectionalInformationError
                      theta b ei K x| +
                  |prespecifiedBatchObservedDirectionalInformationError
                    theta b ej K x| := abs_sub _ _
              _ <=
                  (|prespecifiedBatchObservedDirectionalInformationError
                    theta b eij K x| +
                    |prespecifiedBatchObservedDirectionalInformationError
                      theta b ei K x|) +
                  |prespecifiedBatchObservedDirectionalInformationError
                    theta b ej K x| :=
                add_le_add (abs_sub _ _) le_rfl
          have hSmall :
              |(prespecifiedBatchObservedDirectionalInformationError
                    theta b eij K x -
                  prespecifiedBatchObservedDirectionalInformationError
                    theta b ei K x -
                  prespecifiedBatchObservedDirectionalInformationError
                    theta b ej K x) / 2| < epsilon := by
            rw [abs_div, abs_of_pos (by norm_num : (0 : Real) < 2)]
            calc
              |_ - _ - _| / 2 <=
                  (|prespecifiedBatchObservedDirectionalInformationError
                      theta b eij K x| +
                    |prespecifiedBatchObservedDirectionalInformationError
                      theta b ei K x| +
                    |prespecifiedBatchObservedDirectionalInformationError
                      theta b ej K x|) / 2 := by
                gcongr
              _ < ((epsilon / 2) + (epsilon / 2) + (epsilon / 2)) / 2 := by
                gcongr
              _ < epsilon := by linarith
          exact (not_lt_of_ge hLarge) hSmall
        _ <= mu EA + mu (EI ∪ EJ) := measure_union_le _ _
        _ <= mu EA + (mu EI + mu EJ) :=
          add_le_add le_rfl (measure_union_le _ _)
        _ =
            prespecifiedBatchPrefixMeasure theta b K
                {x | epsilon / 2 <=
                  |prespecifiedBatchObservedDirectionalInformationError
                    theta b eij K x|} +
              (prespecifiedBatchPrefixMeasure theta b K
                  {x | epsilon / 2 <=
                    |prespecifiedBatchObservedDirectionalInformationError
                      theta b ei K x|} +
                prespecifiedBatchPrefixMeasure theta b K
                  {x | epsilon / 2 <=
                    |prespecifiedBatchObservedDirectionalInformationError
                      theta b ej K x|}) := rfl
/-- Every concrete asymptotic input currently available for the implemented
prespecified-batch estimator.  All fields are discharged below; there is no
protocol certificate field hidden in this record. -/
structure PrespecifiedBatchSafeguardedEstimatorAvailableInputs
    (theta b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) : Prop where
  pooledPilotBlocks_exact :
    ∀ K, prespecifiedBatchPooledPilotBlocks K = 27 * K ^ 4
  sampleScale_diverges :
    Tendsto prespecifiedBatchSampleScale atTop atTop
  ridge_vanishes :
    Tendsto prespecifiedBatchRidge atTop (nhds 0)
  cumulativeFisher_converges :
    forall h : RLSVector 3,
      PrespecifiedBatchCumulativeFisherConvergesInProbability theta h b
        (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)
        (mixedPolynomialTruthFrameDirectionalInformation theta h b)
  truthFrameInformation_eq_bures :
    mixedPolynomialTruthFrameInformationMatrix theta b =
      mixedBuresTarget theta
  truthFrameInformation_inverse_eq_bures :
    (mixedPolynomialTruthFrameInformationMatrix theta b)⁻¹ =
      (mixedBuresTarget theta)⁻¹
  buresTarget_continuous :
    ContinuousAt mixedBuresTarget theta
  buresTarget_radialTangent :
    mixedBuresTarget theta =
      (1 / 3 : Real) • mixedTangentProjector theta +
        ((1 / 3 : Real) / (1 - QubitOracle.blochNormSq theta)) •
          mixedRadialProjector theta

/-- Concrete closure of every currently imported estimator-asymptotic input.
The theorem has no Hall--Heyde certificate, Newton-defect, safeguard, moment,
or risk assumption as an argument. -/
theorem prespecifiedBatchSafeguardedEstimator_availableInputs_closed
    (theta b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    PrespecifiedBatchSafeguardedEstimatorAvailableInputs
      theta b hTruth hSeed where
  pooledPilotBlocks_exact := prespecifiedBatchPooledPilotBlocks_eq
  sampleScale_diverges := prespecifiedBatchSampleScale_tendsto_atTop
  ridge_vanishes := prespecifiedBatchRidge_tendsto_zero
  cumulativeFisher_converges := fun h =>
    prespecifiedBatchCumulativeFisherConvergesInProbability_closed
      theta h b hTruth hSeed
  truthFrameInformation_eq_bures :=
    mixedPolynomialTruthFrameInformationMatrix_eq_mixedBuresTarget
      theta b hTruth hSeed
  truthFrameInformation_inverse_eq_bures :=
    mixedPolynomialTruthFrameInformationMatrix_inv_eq_mixedBuresTarget_inv
      theta b hTruth hSeed
  buresTarget_continuous :=
    continuousAt_mixedBuresTarget theta hTruth.2
  buresTarget_radialTangent :=
    mixedBuresTarget_eq_radialTangent theta hTruth.1 hTruth.2

#print axioms prespecifiedBatchPooledPilotBlocks_eq
#print axioms prespecifiedBatchRidge_tendsto_zero
#print axioms prespecifiedBatchRidge_mul_pilotDelta
#print axioms prespecifiedBatchSampleScale_mul_ridge_mul_delta_tendsto_zero
#print axioms prespecifiedBatchPooledPilot_sqrtBlochError_le_three_delta
#print axioms prespecifiedBatchPooledPilot_scaledRidgeError_le
#print axioms prespecifiedBatchPooledPilot_scaledRidgeError_tendsto_zero
#print axioms prespecifiedBatchPooledPilotCoordinate_iIndepFun
#print axioms prespecifiedBatchPooledPilot_coordinate_tail
#print axioms prespecifiedBatchSampleScale_mul_delta_sq_tendsto_zero
#print axioms prespecifiedBatchPooledPilot_blochError_le_three_delta_sq
#print axioms prespecifiedBatchSampleScale_mul_three_delta_sq_tendsto_zero
#print axioms prespecifiedBatchPooledPilot_scaledBlochError_le
#print axioms prespecifiedBatchPooledPilot_scaledBlochError_tendsto_zero
#print axioms prespecifiedBatchPooledPilot_strictInterior_of_coordinate_bound
#print axioms prespecifiedBatchPooledPilotVectorTail_summable
#print axioms prespecifiedBatchPooledPilotBadEvent_measure_le
#print axioms prespecifiedBatchPooledPilotBadEvent_tsum_ne_top
#print axioms prespecifiedBatchPilotInteriorityRejection_subset_eventually
#print axioms prespecifiedBatchPilotInteriorityRejection_measureReal_summable
#print axioms prespecifiedBatchBoundedFallbackEnvelope_summable
#print axioms prespecifiedBatchSafeguardedEstimator_availableInputs_closed

end

end QubitOracle.Paper
