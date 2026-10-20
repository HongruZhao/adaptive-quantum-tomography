import QubitOracle.Paper.OneQubitHoeffding1963ContractCore
import Mathlib.Probability.Moments.SubGaussian

namespace QubitOracle.Paper

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

noncomputable section

/-- Rectangle factorization for the full finite family implies Mathlib independence. -/
theorem finiteIndependentRealFamily_iIndepFun
    {Omega : Type*}
    [MeasurableSpace Omega]
    {n : ℕ}
    {mu : Measure Omega}
    {X : Fin n → Omega → ℝ}
    (hProbability : mu Set.univ = 1)
    (hIndependent : FiniteIndependentRealFamily mu X) :
    iIndepFun X mu := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hSets
  let events : Fin n → Set ℝ := fun i => if i ∈ S then sets i else Set.univ
  have hAll := hIndependent events (fun i => by
    by_cases hi : i ∈ S
    · simpa [events, hi] using hSets i hi
    · simp [events, hi])
  have hLeft :
      (⋂ i, X i ⁻¹' events i) = (⋂ i ∈ S, X i ⁻¹' sets i) := by
    ext omega
    simp only [Set.mem_iInter, Set.mem_preimage]
    constructor
    · intro h i hi
      simpa [events, hi] using h i
    · intro h i
      by_cases hi : i ∈ S
      · simpa [events, hi] using h i hi
      · simp [events, hi]
  have hSubset :
      (∏ i ∈ S, mu (X i ⁻¹' events i)) =
        ∏ i ∈ (Finset.univ : Finset (Fin n)), mu (X i ⁻¹' events i) := by
    apply Finset.prod_subset (Finset.subset_univ S)
    intro i hiUniv hiNot
    simp [events, hiNot, hProbability]
  have hRight :
      (∏ i, mu (X i ⁻¹' events i)) =
        ∏ i ∈ S, mu (X i ⁻¹' sets i) := by
    rw [show (∏ i, mu (X i ⁻¹' events i)) =
      ∏ i ∈ (Finset.univ : Finset (Fin n)), mu (X i ⁻¹' events i) by rfl]
    rw [← hSubset]
    apply Finset.prod_congr rfl
    intro i hi
    simp [events, hi]
  rw [hLeft, hRight] at hAll
  exact hAll


/-- The exact project Hoeffding contract follows from Mathlib's proved Hoeffding lemma. -/
theorem hoeffding1963Theorem2_of_mathlib
    {Omega : Type*}
    [MeasurableSpace Omega]
    {n : ℕ}
    (data : HoeffdingTheorem2Data (Ω := Omega) n) :
    Hoeffding1963Theorem2Contract data := by
  letI : IsProbabilityMeasure data.μ := ⟨data.probabilityMeasure⟩
  intro t ht
  have hIndependentX : iIndepFun data.X data.μ :=
    finiteIndependentRealFamily_iIndepFun data.probabilityMeasure data.independent
  let centered : Fin n → Omega → ℝ :=
    fun i omega => data.X i omega - ∫ x, data.X i x ∂data.μ
  have hIndependentCentered : iIndepFun centered data.μ := by
    exact hIndependentX.comp
      (fun i x => x - ∫ omega, data.X i omega ∂data.μ)
      (fun _ => measurable_id.sub measurable_const)
  let varianceProxy : Fin n → NNReal :=
    fun i => ((‖data.upper i - data.lower i‖₊ / 2) ^ (2 : ℕ) : NNReal)
  have hSubGaussian : ∀ i, HasSubgaussianMGF (centered i) (varianceProxy i) data.μ := by
    intro i
    exact hasSubgaussianMGF_of_mem_Icc
      (data.measurableVariable i).aemeasurable (data.boundedAlmostEverywhere i)
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast data.nonemptyFamily
  have hTail := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    hIndependentCentered
    (s := Finset.univ)
    (c := varianceProxy)
    (fun i _ => hSubGaussian i)
    (ε := (n : ℝ) * t)
    (mul_nonneg (le_of_lt hnReal) (le_of_lt ht))
  have hEvent :
      {omega |
        hoeffdingMeanAverage data.μ data.X + t ≤
          hoeffdingSampleAverage data.X omega} =
      {omega | (n : ℝ) * t ≤ ∑ i, centered i omega} := by
    ext omega
    have hnNe : (n : ℝ) ≠ 0 := ne_of_gt hnReal
    simp only [Set.mem_setOf_eq, hoeffdingMeanAverage, hoeffdingSampleAverage,
      centered, Finset.sum_sub_distrib]
    constructor
    · intro h
      have hMul := (mul_le_mul_iff_of_pos_left hnReal).2 h
      field_simp [hnNe] at hMul
      linarith
    · intro h
      apply (mul_le_mul_iff_of_pos_left hnReal).1
      field_simp [hnNe]
      linarith
  have hTailTarget :
      data.μ.real
          {omega |
            hoeffdingMeanAverage data.μ data.X + t ≤
              hoeffdingSampleAverage data.X omega} ≤
        Real.exp
          (-((n : ℝ) * t) ^ 2 /
            (2 * (↑(∑ i, varianceProxy i) : ℝ))) := by
    rw [hEvent]
    exact hTail
  have hVarianceProxy :
      (↑(∑ i, varianceProxy i) : ℝ) =
        hoeffdingRangeSquareSum data.lower data.upper / 4 := by
    unfold varianceProxy hoeffdingRangeSquareSum
    simp only [NNReal.coe_sum, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat,
      coe_nnnorm, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr (data.orderedBounds _))]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hExponent :
      -((n : ℝ) * t) ^ 2 /
          (2 * (↑(∑ i, varianceProxy i) : ℝ)) =
        -2 * (n : ℝ) ^ 2 * t ^ 2 /
          hoeffdingRangeSquareSum data.lower data.upper := by
    rw [hVarianceProxy]
    by_cases hRange : hoeffdingRangeSquareSum data.lower data.upper = 0
    · simp [hRange]
    · field_simp
      ring
  unfold HoeffdingTheorem2Conclusion
  rw [← hExponent]
  have hMeasureNeTop :
      data.μ
          {omega |
            hoeffdingMeanAverage data.μ data.X + t ≤
              hoeffdingSampleAverage data.X omega} ≠ ⊤ :=
    measure_ne_top _ _
  rw [← ENNReal.ofReal_toReal hMeasureNeTop]
  exact ENNReal.ofReal_le_ofReal hTailTarget

/-- Universal form of the exact project contract, now proved from Mathlib. -/
theorem hoeffding1963UniversalTheorem2_of_mathlib :
    Hoeffding1963UniversalTheorem2Contract := by
  unfold Hoeffding1963UniversalTheorem2Contract
  intro Omega m n data
  exact hoeffding1963Theorem2_of_mathlib data

/-- All finite polynomial-pilot Hoeffding contracts follow without an
external concentration axiom. -/
theorem mixedPolynomialFinitePilotHoeffdingContracts_mathlib
    (theta : RLSVector 3) (hPhysical : PauliPilotPhysicalBloch theta) :
    MixedPolynomialFinitePilotHoeffdingContracts theta hPhysical :=
  mixedPolynomialFinitePilotHoeffdingContracts_of_hoeffding1963
    theta hPhysical hoeffding1963UniversalTheorem2_of_mathlib

/-- The countable pilot-consistency contracts follow from the same proved
universal theorem. -/
theorem pauliPilotConsistencyHoeffdingContracts_mathlib
    (theta : RLSVector 3) (hPhysical : PauliPilotPhysicalBloch theta) :
    PauliPilotConsistencyHoeffdingContracts theta hPhysical :=
  pauliPilotConsistencyHoeffdingContracts_of_hoeffding1963
    theta hPhysical hoeffding1963UniversalTheorem2_of_mathlib

/-- The finite exact-cycle concentration certificate is kernel-derived from
Mathlib's Hoeffding lemma and independent-sum theorem. -/
theorem mixedExactCycleUniformFiniteHoeffdingContract_mathlib
    (theta : RLSVector 3) (H : ℝ)
    (hInterior : QubitOracle.blochNormSq theta < 1) :
    MixedExactCycleUniformFiniteHoeffdingContract theta H :=
  mixedExactCycleUniformFiniteHoeffdingContract_of_hoeffding1963
    theta H hInterior hoeffding1963UniversalTheorem2_of_mathlib

/-- Closed mixed-qubit exact-cycle probability envelope, with Hoeffding
discharged inside Lean rather than cited as an axiom. -/
theorem mixedUniformLocalProbabilityEnvelope_exactCycle_mathlib
    (theta b : RLSVector 3) (H : ℝ)
    (hH : 0 ≤ H)
    (hPositive : 0 < QubitOracle.blochNormSq theta)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    MixedUniformLocalProbabilityEnvelope theta b
      mixedUniformLocalExactCycleN H mixedUniformLocalExactCycleQFinal :=
  mixedUniformLocalProbabilityEnvelope_exactCycle_of_hoeffding1963
    theta b H hH hPositive hInterior hSeed
      hoeffding1963UniversalTheorem2_of_mathlib

/-- Closed directional Fisher-information convergence for the concrete
polynomial mixed-qubit protocol.  Hoeffding is discharged by Mathlib, so this
endpoint has no scientific concentration axiom. -/
theorem mixedPolynomialNormalizedDirectionalInformation_convergesInProbability_mathlib
    (b theta h : Fin 3 -> Real)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    MixedPolynomialDirectionalInformationConvergesInProbability theta h b :=
  mixedPolynomialNormalizedDirectionalInformation_convergesInProbability
    b theta h hTruth hSeed
      (mixedPolynomialFinitePilotHoeffdingContracts_mathlib theta
        (mixedNonzeroInterior_pauliPilotPhysical theta hTruth))

end

end QubitOracle.Paper
