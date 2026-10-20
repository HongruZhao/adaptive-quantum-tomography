import QubitOracle.Paper.OneQubitMixedCyclicPauliIIDCLT
import QubitOracle.Paper.OneQubitPureCyclicPauliLAN
import Mathlib.Probability.StrongLaw

open scoped BigOperators ENNReal NNReal Topology ProbabilityTheory
open MeasureTheory Filter Finset
open ProbabilityTheory

namespace QubitOracle.Paper

/- Keep the exact measurable-space instance used by the finite Born-product law. -/
local instance mixedCyclicPauliLANPathMeasurableSpace :
    MeasurableSpace (PauliPilotPath 1) :=
  pauliPilotBornPathMeasurableSpace 1

/-- The local mixed-state alternative after `q` complete `X,Y,Z` cycles. -/
noncomputable def mixedCyclicPauliLocalBloch
    (theta h : RLSVector 3) (q : ℕ) : RLSVector 3 :=
  fun j => theta j + (Real.sqrt q)⁻¹ * (Real.sqrt 3)⁻¹ * h j

/-- Every fixed local direction remains inside the mixed-state Bloch ball eventually. -/
theorem mixedCyclicPauliLocalBloch_eventually_strictInterior
    (theta h : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta) :
    ∀ᶠ q : ℕ in atTop, MixedCyclicPauliStrictInterior
      (mixedCyclicPauliLocalBloch theta h q) := by
  have hsqrt : Tendsto (fun q : ℕ => Real.sqrt (q : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun q : ℕ => (Real.sqrt (q : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  have hcoord (j : Fin 3) :
      Tendsto (fun q => mixedCyclicPauliLocalBloch theta h q j) atTop (𝓝 (theta j)) := by
    have hconst : Tendsto (fun _ : ℕ => theta j) atTop (𝓝 (theta j)) :=
      tendsto_const_nhds
    simpa [mixedCyclicPauliLocalBloch, mul_assoc] using
      hconst.add (hinv.mul_const ((Real.sqrt 3)⁻¹ * h j))
  have hnorm : Tendsto
      (fun q => QubitOracle.blochNormSq (mixedCyclicPauliLocalBloch theta h q))
      atTop (𝓝 (QubitOracle.blochNormSq theta)) := by
    unfold QubitOracle.blochNormSq
    apply tendsto_finset_sum
    intro j _
    simpa using (hcoord j).pow 2
  exact (tendsto_order.1 hnorm).2 1 hInterior

/-- The random observed quadratic term in one complete `X,Y,Z` cycle. -/
noncomputable def mixedCyclicPauliObservedInformationBlock
    (theta h : RLSVector 3) (block : PauliPilotPath 1) : ℝ :=
  mixedCyclicPauliScoreCoefficient theta h 0 ^ 2 *
      mixedCyclicPauliCenteredCoordinate theta 0 block ^ 2 +
  mixedCyclicPauliScoreCoefficient theta h 1 ^ 2 *
      mixedCyclicPauliCenteredCoordinate theta 1 block ^ 2 +
  mixedCyclicPauliScoreCoefficient theta h 2 ^ 2 *
      mixedCyclicPauliCenteredCoordinate theta 2 block ^ 2

/-- The expected observed quadratic term is exactly the directional Fisher information. -/
theorem mixedCyclicPauliObservedInformationBlock_mean
    (theta h : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta) :
    ∫ block, mixedCyclicPauliObservedInformationBlock theta h block
      ∂mixedCyclicPauliBlockMeasure theta = mixedCyclicPauliFisherQuadratic theta h := by
  letI : IsProbabilityMeasure (mixedCyclicPauliBlockMeasure theta) :=
    ⟨pauliPilotBornProductMeasure_univ theta
      (mixedCyclicPauliStrictInterior_physical theta hInterior)⟩
  let f0 : PauliPilotPath 1 → ℝ := fun block =>
    mixedCyclicPauliScoreCoefficient theta h 0 ^ 2 *
      mixedCyclicPauliCenteredCoordinate theta 0 block ^ 2
  let f1 : PauliPilotPath 1 → ℝ := fun block =>
    mixedCyclicPauliScoreCoefficient theta h 1 ^ 2 *
      mixedCyclicPauliCenteredCoordinate theta 1 block ^ 2
  let f2 : PauliPilotPath 1 → ℝ := fun block =>
    mixedCyclicPauliScoreCoefficient theta h 2 ^ 2 *
      mixedCyclicPauliCenteredCoordinate theta 2 block ^ 2
  have h0i : Integrable f0 (mixedCyclicPauliBlockMeasure theta) := Integrable.of_finite
  have h1i : Integrable f1 (mixedCyclicPauliBlockMeasure theta) := Integrable.of_finite
  have h2i : Integrable f2 (mixedCyclicPauliBlockMeasure theta) := Integrable.of_finite
  change ∫ block, ((f0 + f1) + f2) block ∂mixedCyclicPauliBlockMeasure theta = _
  calc
    (∫ block, ((f0 + f1) + f2) block ∂mixedCyclicPauliBlockMeasure theta) =
        (∫ block, (f0 + f1) block ∂mixedCyclicPauliBlockMeasure theta) +
        ∫ block, f2 block ∂mixedCyclicPauliBlockMeasure theta :=
      integral_add (h0i.add h1i) h2i
    _ = ((∫ block, f0 block ∂mixedCyclicPauliBlockMeasure theta) +
          ∫ block, f1 block ∂mixedCyclicPauliBlockMeasure theta) +
        ∫ block, f2 block ∂mixedCyclicPauliBlockMeasure theta := by
      have hsplit01 :
          (∫ block, (f0 + f1) block ∂mixedCyclicPauliBlockMeasure theta) =
            (∫ block, f0 block ∂mixedCyclicPauliBlockMeasure theta) +
            ∫ block, f1 block ∂mixedCyclicPauliBlockMeasure theta := by
        simpa only [Pi.add_apply] using integral_add h0i h1i
      rw [hsplit01]
    _ = mixedCyclicPauliFisherQuadratic theta h := by
      simp only [f0, f1, f2, integral_const_mul]
      rw [mixedCyclicPauliCenteredCoordinate_secondMoment theta hInterior 0,
        mixedCyclicPauliCenteredCoordinate_secondMoment theta hInterior 1,
        mixedCyclicPauliCenteredCoordinate_secondMoment theta hInterior 2]
      rfl

/-- Observed-information block `k` on the common iid product space. -/
noncomputable def mixedCyclicPauliObservedInformationIncrement
    (theta h : RLSVector 3) (k : ℕ) (omega : MixedCyclicPauliOmega) : ℝ :=
  mixedCyclicPauliObservedInformationBlock theta h (omega k)

/-- Observed information per physical shot after `q` complete cycles. -/
noncomputable def mixedCyclicPauliObservedInformation
    (theta h : RLSVector 3) (q : ℕ) (omega : MixedCyclicPauliOmega) : ℝ :=
  (q : ℝ)⁻¹ * ∑ k ∈ Finset.range q,
    mixedCyclicPauliObservedInformationIncrement theta h k omega

private theorem mixedCyclicPauliObservedInformationIncrement_hasLaw
    (theta h : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta) (k : ℕ) :
    HasLaw (mixedCyclicPauliObservedInformationIncrement theta h k)
      (Measure.map (mixedCyclicPauliObservedInformationBlock theta h)
        (mixedCyclicPauliBlockMeasure theta))
      (mixedCyclicPauliMeasure theta) := by
  letI : IsProbabilityMeasure (mixedCyclicPauliBlockMeasure theta) :=
    ⟨pauliPilotBornProductMeasure_univ theta
      (mixedCyclicPauliStrictInterior_physical theta hInterior)⟩
  letI : ∀ _ : ℕ, IsProbabilityMeasure (mixedCyclicPauliBlockMeasure theta) :=
    fun _ => inferInstance
  refine ⟨((measurable_of_finite _).comp (measurable_pi_apply k)).aemeasurable, ?_⟩
  change Measure.map
      (mixedCyclicPauliObservedInformationBlock theta h ∘
        fun omega : MixedCyclicPauliOmega => omega k)
      (mixedCyclicPauliMeasure theta) = _
  calc
    Measure.map
        (mixedCyclicPauliObservedInformationBlock theta h ∘
          fun omega : MixedCyclicPauliOmega => omega k)
        (mixedCyclicPauliMeasure theta) =
        Measure.map (mixedCyclicPauliObservedInformationBlock theta h)
          (Measure.map (fun omega : MixedCyclicPauliOmega => omega k)
            (mixedCyclicPauliMeasure theta)) := by
      symm
      exact Measure.map_map Measurable.of_discrete (measurable_pi_apply k)
    _ = Measure.map (mixedCyclicPauliObservedInformationBlock theta h)
        (mixedCyclicPauliBlockMeasure theta) := by
      rw [Measure.infinitePi_map_eval]

private theorem mixedCyclicPauliObservedInformationIncrement_iIndepFun
    (theta h : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta) :
    iIndepFun (mixedCyclicPauliObservedInformationIncrement theta h)
      (mixedCyclicPauliMeasure theta) := by
  letI : IsProbabilityMeasure (mixedCyclicPauliBlockMeasure theta) :=
    ⟨pauliPilotBornProductMeasure_univ theta
      (mixedCyclicPauliStrictInterior_physical theta hInterior)⟩
  letI : ∀ _ : ℕ, IsProbabilityMeasure (mixedCyclicPauliBlockMeasure theta) :=
    fun _ => inferInstance
  exact iIndepFun_infinitePi (fun _ => measurable_of_finite _)

private theorem mixedCyclicPauliObservedInformationIncrement_identDistrib
    (theta h : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta) (k : ℕ) :
    IdentDistrib (mixedCyclicPauliObservedInformationIncrement theta h k)
      (mixedCyclicPauliObservedInformationIncrement theta h 0)
      (mixedCyclicPauliMeasure theta) (mixedCyclicPauliMeasure theta) :=
  HasLaw.identDistrib
    (mixedCyclicPauliObservedInformationIncrement_hasLaw theta h hInterior k)
    (mixedCyclicPauliObservedInformationIncrement_hasLaw theta h hInterior 0)

private theorem mixedCyclicPauliObservedInformationIncrement_integrable
    (theta h : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta) :
    Integrable (mixedCyclicPauliObservedInformationIncrement theta h 0)
      (mixedCyclicPauliMeasure theta) := by
  letI : IsProbabilityMeasure (mixedCyclicPauliBlockMeasure theta) :=
    ⟨pauliPilotBornProductMeasure_univ theta
      (mixedCyclicPauliStrictInterior_physical theta hInterior)⟩
  letI : ∀ _ : ℕ, IsProbabilityMeasure (mixedCyclicPauliBlockMeasure theta) :=
    fun _ => inferInstance
  let hSelf : HasLaw (mixedCyclicPauliObservedInformationBlock theta h)
      (Measure.map (mixedCyclicPauliObservedInformationBlock theta h)
        (mixedCyclicPauliBlockMeasure theta))
      (mixedCyclicPauliBlockMeasure theta) :=
    ⟨(measurable_of_finite _).aemeasurable, rfl⟩
  have hIdent := HasLaw.identDistrib
    (mixedCyclicPauliObservedInformationIncrement_hasLaw theta h hInterior 0) hSelf
  exact hIdent.integrable_iff.mpr Integrable.of_finite

private theorem mixedCyclicPauliObservedInformationIncrement_mean
    (theta h : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta) :
    ∫ omega, mixedCyclicPauliObservedInformationIncrement theta h 0 omega
      ∂mixedCyclicPauliMeasure theta = mixedCyclicPauliFisherQuadratic theta h := by
  let hSelf : HasLaw (mixedCyclicPauliObservedInformationBlock theta h)
      (Measure.map (mixedCyclicPauliObservedInformationBlock theta h)
        (mixedCyclicPauliBlockMeasure theta))
      (mixedCyclicPauliBlockMeasure theta) :=
    ⟨(measurable_of_finite _).aemeasurable, rfl⟩
  have hIdent := HasLaw.identDistrib
    (mixedCyclicPauliObservedInformationIncrement_hasLaw theta h hInterior 0) hSelf
  rw [IdentDistrib.integral_eq hIdent]
  exact mixedCyclicPauliObservedInformationBlock_mean theta h hInterior

/-- Kernel-proved strong law for the random observed Fisher information. -/
theorem mixedCyclicPauliObservedInformation_tendsto_ae
    (theta h : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta) :
    ∀ᵐ omega ∂mixedCyclicPauliMeasure theta,
      Tendsto (fun q => mixedCyclicPauliObservedInformation theta h q omega)
        atTop (𝓝 (mixedCyclicPauliFisherQuadratic theta h)) := by
  letI : IsProbabilityMeasure (mixedCyclicPauliBlockMeasure theta) :=
    ⟨pauliPilotBornProductMeasure_univ theta
      (mixedCyclicPauliStrictInterior_physical theta hInterior)⟩
  letI : ∀ _ : ℕ, IsProbabilityMeasure (mixedCyclicPauliBlockMeasure theta) :=
    fun _ => inferInstance
  let hIndep := mixedCyclicPauliObservedInformationIncrement_iIndepFun theta h hInterior
  have hSLLN := strong_law_ae
    (mixedCyclicPauliObservedInformationIncrement theta h)
    (mixedCyclicPauliObservedInformationIncrement_integrable theta h hInterior)
    (fun _ _ hij => hIndep.indepFun hij)
    (mixedCyclicPauliObservedInformationIncrement_identDistrib theta h hInterior)
  filter_upwards [hSLLN] with omega homega
  simpa [mixedCyclicPauliObservedInformation, smul_eq_mul,
    mixedCyclicPauliObservedInformationIncrement_mean theta h hInterior] using homega

/-- Observed information also converges in measure. -/
theorem mixedCyclicPauliObservedInformation_tendstoInMeasure
    (theta h : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta) :
    TendstoInMeasure (mixedCyclicPauliMeasure theta)
      (mixedCyclicPauliObservedInformation theta h) atTop
      (fun _ => mixedCyclicPauliFisherQuadratic theta h) := by
  letI : IsProbabilityMeasure (mixedCyclicPauliBlockMeasure theta) :=
    ⟨pauliPilotBornProductMeasure_univ theta
      (mixedCyclicPauliStrictInterior_physical theta hInterior)⟩
  letI : ∀ _ : ℕ, IsProbabilityMeasure (mixedCyclicPauliBlockMeasure theta) :=
    fun _ => inferInstance
  apply tendstoInMeasure_of_tendsto_ae
  · intro q
    have hinc (k : ℕ) :
        Measurable (mixedCyclicPauliObservedInformationIncrement theta h k) :=
      (measurable_of_finite _).comp (measurable_pi_apply k)
    exact ((Finset.measurable_sum (Finset.range q) (fun k _ => hinc k)).const_mul
      (q : ℝ)⁻¹).aestronglyMeasurable
  · exact mixedCyclicPauliObservedInformation_tendsto_ae theta h hInterior

/-- Relative Bernoulli perturbation for one Pauli outcome under the local alternative. -/
noncomputable def mixedCyclicPauliOutcomeLikelihoodPerturbation
    (theta h : RLSVector 3) (q : ℕ) (j : Fin 3) (outcome : Bool) : ℝ :=
  (Real.sqrt q)⁻¹ * mixedCyclicPauliScoreCoefficient theta h j *
    (pauliOutcomeSign outcome - theta j)

/-- Relative likelihood perturbation read from a block. -/
noncomputable def mixedCyclicPauliLikelihoodPerturbation
    (theta h : RLSVector 3) (q : ℕ) (j : Fin 3) (block : PauliPilotPath 1) : ℝ :=
  mixedCyclicPauliOutcomeLikelihoodPerturbation theta h q j (block 0 j)

/-- Exact factorization of the local Born probability by the true Born probability. -/
theorem mixedCyclicPauliLocalBornProbability_factor
    (theta h : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta)
    (q : ℕ) (j : Fin 3) (outcome : Bool) :
    pauliBornProbability (mixedCyclicPauliLocalBloch theta h q) j outcome =
      pauliBornProbability theta j outcome *
        (1 + mixedCyclicPauliOutcomeLikelihoodPerturbation theta h q j outcome) := by
  have hd := ne_of_gt (mixedCyclicPauli_varianceDenominator_pos theta hInterior j)
  cases outcome <;>
    simp [pauliBornProbability,
      pauliOutcomeSign, mixedCyclicPauliLocalBloch,
      mixedCyclicPauliOutcomeLikelihoodPerturbation,
      mixedCyclicPauliScoreCoefficient] <;>
    field_simp [hd] <;> ring

/-- Sum of the three local score perturbations in one cycle. -/
theorem mixedCyclicPauliLikelihoodPerturbation_sum_eq_score
    (theta h : RLSVector 3) (q : ℕ) (block : PauliPilotPath 1) :
    mixedCyclicPauliLikelihoodPerturbation theta h q 0 block +
      mixedCyclicPauliLikelihoodPerturbation theta h q 1 block +
      mixedCyclicPauliLikelihoodPerturbation theta h q 2 block =
        (Real.sqrt q)⁻¹ * mixedCyclicPauliBlockScore theta h block := by
  simp only [mixedCyclicPauliLikelihoodPerturbation,
    mixedCyclicPauliOutcomeLikelihoodPerturbation,
    mixedCyclicPauliBlockScore, mixedCyclicPauliCenteredCoordinate,
    mixedCyclicPauliBlockCoordinate]
  ring

/-- Sum of squared local perturbations in one cycle. -/
theorem mixedCyclicPauliLikelihoodPerturbation_sq_sum_eq_information
    (theta h : RLSVector 3) (q : ℕ) (block : PauliPilotPath 1) :
    mixedCyclicPauliLikelihoodPerturbation theta h q 0 block ^ 2 +
      mixedCyclicPauliLikelihoodPerturbation theta h q 1 block ^ 2 +
      mixedCyclicPauliLikelihoodPerturbation theta h q 2 block ^ 2 =
        (q : ℝ)⁻¹ * mixedCyclicPauliObservedInformationBlock theta h block := by
  have hsqrt : (Real.sqrt (q : ℝ)) ^ 2 = (q : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg q)
  have hinv : (Real.sqrt (q : ℝ))⁻¹ ^ 2 = (q : ℝ)⁻¹ := by
    rw [inv_pow, hsqrt]
  simp only [mixedCyclicPauliLikelihoodPerturbation,
    mixedCyclicPauliOutcomeLikelihoodPerturbation,
    mixedCyclicPauliCenteredCoordinate, mixedCyclicPauliBlockCoordinate,
    mixedCyclicPauliObservedInformationBlock]
  repeat' rw [mul_pow]
  rw [hinv]
  ring

/-- Exact log-likelihood ratio of `q` complete cycles in direction `h`. -/
noncomputable def mixedCyclicPauliLogLikelihoodRatio
    (theta h : RLSVector 3) (q : ℕ) (omega : MixedCyclicPauliOmega) : ℝ :=
  ∑ k ∈ Finset.range q,
    (Real.log (1 + mixedCyclicPauliLikelihoodPerturbation theta h q 0 (omega k)) +
     Real.log (1 + mixedCyclicPauliLikelihoodPerturbation theta h q 1 (omega k)) +
     Real.log (1 + mixedCyclicPauliLikelihoodPerturbation theta h q 2 (omega k)))

/-- Sum of the cubic-and-higher scalar log remainders. -/
noncomputable def mixedCyclicPauliLikelihoodRemainder
    (theta h : RLSVector 3) (q : ℕ) (omega : MixedCyclicPauliOmega) : ℝ :=
  ∑ k ∈ Finset.range q,
    (pureCyclicPauliLogRemainder
        (mixedCyclicPauliLikelihoodPerturbation theta h q 0 (omega k)) +
     pureCyclicPauliLogRemainder
        (mixedCyclicPauliLikelihoodPerturbation theta h q 1 (omega k)) +
     pureCyclicPauliLogRemainder
        (mixedCyclicPauliLikelihoodPerturbation theta h q 2 (omega k)))

/-- Exact finite-sample expansion with the random observed-information term. -/
theorem mixedCyclicPauliLogLikelihoodRatio_exact_observed
    (theta h : RLSVector 3) (q : ℕ) (omega : MixedCyclicPauliOmega) :
    mixedCyclicPauliLogLikelihoodRatio theta h q omega =
      mixedCyclicPauliNormalizedScore theta h q omega -
        mixedCyclicPauliObservedInformation theta h q omega / 2 +
      mixedCyclicPauliLikelihoodRemainder theta h q omega := by
  have hscalar (x : ℝ) :
      Real.log (1 + x) = x - x ^ 2 / 2 + pureCyclicPauliLogRemainder x := by
    unfold pureCyclicPauliLogRemainder
    ring
  have hblock (k : ℕ) :
      Real.log (1 + mixedCyclicPauliLikelihoodPerturbation theta h q 0 (omega k)) +
          Real.log (1 + mixedCyclicPauliLikelihoodPerturbation theta h q 1 (omega k)) +
          Real.log (1 + mixedCyclicPauliLikelihoodPerturbation theta h q 2 (omega k)) =
        (mixedCyclicPauliLikelihoodPerturbation theta h q 0 (omega k) +
          mixedCyclicPauliLikelihoodPerturbation theta h q 1 (omega k) +
          mixedCyclicPauliLikelihoodPerturbation theta h q 2 (omega k)) -
        (mixedCyclicPauliLikelihoodPerturbation theta h q 0 (omega k) ^ 2 +
          mixedCyclicPauliLikelihoodPerturbation theta h q 1 (omega k) ^ 2 +
          mixedCyclicPauliLikelihoodPerturbation theta h q 2 (omega k) ^ 2) / 2 +
        (pureCyclicPauliLogRemainder
            (mixedCyclicPauliLikelihoodPerturbation theta h q 0 (omega k)) +
          pureCyclicPauliLogRemainder
            (mixedCyclicPauliLikelihoodPerturbation theta h q 1 (omega k)) +
          pureCyclicPauliLogRemainder
            (mixedCyclicPauliLikelihoodPerturbation theta h q 2 (omega k))) := by
    rw [hscalar, hscalar, hscalar]
    ring
  have hlinear :
      (∑ k ∈ Finset.range q,
        (mixedCyclicPauliLikelihoodPerturbation theta h q 0 (omega k) +
         mixedCyclicPauliLikelihoodPerturbation theta h q 1 (omega k) +
         mixedCyclicPauliLikelihoodPerturbation theta h q 2 (omega k))) =
      mixedCyclicPauliNormalizedScore theta h q omega := by
    simp_rw [mixedCyclicPauliLikelihoodPerturbation_sum_eq_score]
    rw [← Finset.mul_sum]
    rfl
  have hquadratic :
      (∑ k ∈ Finset.range q,
        (mixedCyclicPauliLikelihoodPerturbation theta h q 0 (omega k) ^ 2 +
         mixedCyclicPauliLikelihoodPerturbation theta h q 1 (omega k) ^ 2 +
         mixedCyclicPauliLikelihoodPerturbation theta h q 2 (omega k) ^ 2)) =
      mixedCyclicPauliObservedInformation theta h q omega := by
    simp_rw [mixedCyclicPauliLikelihoodPerturbation_sq_sum_eq_information]
    rw [← Finset.mul_sum]
    rfl
  unfold mixedCyclicPauliLogLikelihoodRatio
  simp_rw [hblock]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hlinear]
  rw [← Finset.sum_div, hquadratic]
  unfold mixedCyclicPauliLikelihoodRemainder
  ring

/-- A deterministic bound for one unnormalized cyclic score block. -/
noncomputable def mixedCyclicPauliPerturbationConstant
    (theta h : RLSVector 3) : ℝ :=
  |mixedCyclicPauliScoreCoefficient theta h 0| * (1 + |theta 0|) +
  |mixedCyclicPauliScoreCoefficient theta h 1| * (1 + |theta 1|) +
  |mixedCyclicPauliScoreCoefficient theta h 2| * (1 + |theta 2|)

/-- Uniform bound for each local Bernoulli perturbation at cycle count `q`. -/
noncomputable def mixedCyclicPauliPerturbationEnvelope
    (theta h : RLSVector 3) (q : ℕ) : ℝ :=
  mixedCyclicPauliPerturbationConstant theta h / Real.sqrt q

private theorem mixedCyclicPauliOutcomeCentered_abs_le
    (theta : RLSVector 3) (j : Fin 3) (outcome : Bool) :
    |pauliOutcomeSign outcome - theta j| ≤ 1 + |theta j| := by
  calc
    |pauliOutcomeSign outcome - theta j| ≤
        |pauliOutcomeSign outcome| + |theta j| := abs_sub _ _
    _ = 1 + |theta j| := by
      cases outcome <;> simp [pauliOutcomeSign]

private theorem mixedCyclicPauliPerturbationConstant_nonneg
    (theta h : RLSVector 3) :
    0 ≤ mixedCyclicPauliPerturbationConstant theta h := by
  unfold mixedCyclicPauliPerturbationConstant
  positivity

/-- Every axis perturbation is bounded by the common deterministic envelope. -/
theorem mixedCyclicPauliOutcomeLikelihoodPerturbation_abs_le_envelope
    (theta h : RLSVector 3) (q : ℕ) (j : Fin 3) (outcome : Bool) :
    |mixedCyclicPauliOutcomeLikelihoodPerturbation theta h q j outcome| ≤
      mixedCyclicPauliPerturbationEnvelope theta h q := by
  have hsqrt : 0 ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
  have hinv : 0 ≤ (Real.sqrt (q : ℝ))⁻¹ := inv_nonneg.mpr hsqrt
  have hz := mixedCyclicPauliOutcomeCentered_abs_le theta j outcome
  have h0 : 0 ≤ |mixedCyclicPauliScoreCoefficient theta h 0| * (1 + |theta 0|) := by
    positivity
  have h1 : 0 ≤ |mixedCyclicPauliScoreCoefficient theta h 1| * (1 + |theta 1|) := by
    positivity
  have h2 : 0 ≤ |mixedCyclicPauliScoreCoefficient theta h 2| * (1 + |theta 2|) := by
    positivity
  have hterm :
      |mixedCyclicPauliScoreCoefficient theta h j| * (1 + |theta j|) ≤
        mixedCyclicPauliPerturbationConstant theta h := by
    fin_cases j <;> unfold mixedCyclicPauliPerturbationConstant <;> dsimp <;> nlinarith
  simp only [mixedCyclicPauliOutcomeLikelihoodPerturbation, abs_mul,
    abs_inv, abs_of_nonneg hsqrt]
  rw [mixedCyclicPauliPerturbationEnvelope, div_eq_mul_inv]
  have hcentered :
      |mixedCyclicPauliScoreCoefficient theta h j| *
          |pauliOutcomeSign outcome - theta j| ≤
        |mixedCyclicPauliScoreCoefficient theta h j| * (1 + |theta j|) :=
    mul_le_mul_of_nonneg_left hz (abs_nonneg _)
  calc
    (Real.sqrt (q : ℝ))⁻¹ * |mixedCyclicPauliScoreCoefficient theta h j| *
        |pauliOutcomeSign outcome - theta j| ≤
      (Real.sqrt (q : ℝ))⁻¹ *
        (|mixedCyclicPauliScoreCoefficient theta h j| * (1 + |theta j|)) := by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hcentered hinv
    _ ≤ (Real.sqrt (q : ℝ))⁻¹ * mixedCyclicPauliPerturbationConstant theta h := by
      exact mul_le_mul_of_nonneg_left hterm hinv
    _ = mixedCyclicPauliPerturbationConstant theta h * (Real.sqrt (q : ℝ))⁻¹ :=
      mul_comm _ _

/-- The perturbation envelope tends to zero. -/
theorem mixedCyclicPauliPerturbationEnvelope_tendsto_zero
    (theta h : RLSVector 3) :
    Tendsto (mixedCyclicPauliPerturbationEnvelope theta h) atTop (𝓝 0) := by
  have hsqrt : Tendsto (fun q : ℕ => Real.sqrt (q : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun q : ℕ => (Real.sqrt (q : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  change Tendsto
    (fun q : ℕ => mixedCyclicPauliPerturbationConstant theta h *
      (Real.sqrt (q : ℝ))⁻¹) atTop (𝓝 0)
  simpa using hinv.const_mul (mixedCyclicPauliPerturbationConstant theta h)

/-- Eventually every local perturbation lies in the uniform Taylor region. -/
theorem mixedCyclicPauliPerturbationEnvelope_eventually_le_half
    (theta h : RLSVector 3) :
    ∀ᶠ q : ℕ in atTop, mixedCyclicPauliPerturbationEnvelope theta h q ≤ 1 / 2 := by
  have hlt := (tendsto_order.1
    (mixedCyclicPauliPerturbationEnvelope_tendsto_zero theta h)).2 (1 / 2 : ℝ) (by norm_num)
  exact hlt.mono (fun _ hq => le_of_lt hq)

/-- Eventually all three local Born factors are strictly positive. -/
theorem mixedCyclicPauliLikelihoodFactors_eventually_pos
    (theta h : RLSVector 3) :
    ∀ᶠ q : ℕ in atTop, ∀ j : Fin 3, ∀ block : PauliPilotPath 1,
      0 < 1 + mixedCyclicPauliLikelihoodPerturbation theta h q j block := by
  filter_upwards [mixedCyclicPauliPerturbationEnvelope_eventually_le_half theta h]
    with q hsmall
  intro j block
  have hu := mixedCyclicPauliOutcomeLikelihoodPerturbation_abs_le_envelope
    theta h q j (block 0 j)
  change |mixedCyclicPauliLikelihoodPerturbation theta h q j block| ≤ _ at hu
  have : |mixedCyclicPauliLikelihoodPerturbation theta h q j block| ≤ 1 / 2 :=
    hu.trans hsmall
  have hneg := neg_abs_le (mixedCyclicPauliLikelihoodPerturbation theta h q j block)
  linarith

/-- Deterministic `q^{-1/2}` envelope for the full cyclic log remainder. -/
noncomputable def mixedCyclicPauliLikelihoodRemainderEnvelope
    (theta h : RLSVector 3) (q : ℕ) : ℝ :=
  6 * mixedCyclicPauliPerturbationConstant theta h ^ 3 / Real.sqrt q

private theorem mixedCyclicPauliLogRemainder_abs_le_two_cube
    (theta h : RLSVector 3) {q : ℕ}
    (hsmall : mixedCyclicPauliPerturbationEnvelope theta h q ≤ 1 / 2)
    (j : Fin 3) (block : PauliPilotPath 1) :
    |pureCyclicPauliLogRemainder
        (mixedCyclicPauliLikelihoodPerturbation theta h q j block)| ≤
      2 * mixedCyclicPauliPerturbationEnvelope theta h q ^ 3 := by
  let u := mixedCyclicPauliLikelihoodPerturbation theta h q j block
  let E := mixedCyclicPauliPerturbationEnvelope theta h q
  have hu : |u| ≤ E := by
    exact mixedCyclicPauliOutcomeLikelihoodPerturbation_abs_le_envelope
      theta h q j (block 0 j)
  have huhalf : |u| ≤ 1 / 2 := hu.trans hsmall
  have huone : |u| < 1 := lt_of_le_of_lt huhalf (by norm_num)
  have hden : 0 < 1 - |u| := by linarith
  have hpow : |u| ^ 3 ≤ E ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg u) hu 3
  calc
    |pureCyclicPauliLogRemainder u| ≤ |u| ^ 3 / (1 - |u|) :=
      pureCyclicPauliLogRemainder_abs_le huone
    _ ≤ 2 * |u| ^ 3 := by
      rw [div_le_iff₀ hden]
      nlinarith [pow_nonneg (abs_nonneg u) 3]
    _ ≤ 2 * E ^ 3 := by nlinarith

/-- Uniform finite-sample bound for the full mixed cyclic likelihood remainder. -/
theorem mixedCyclicPauliLikelihoodRemainder_abs_le_envelope
    (theta h : RLSVector 3) {q : ℕ} (hq : 0 < q)
    (hsmall : mixedCyclicPauliPerturbationEnvelope theta h q ≤ 1 / 2)
    (omega : MixedCyclicPauliOmega) :
    |mixedCyclicPauliLikelihoodRemainder theta h q omega| ≤
      mixedCyclicPauliLikelihoodRemainderEnvelope theta h q := by
  let E := mixedCyclicPauliPerturbationEnvelope theta h q
  have hblock (k : ℕ) :
      |pureCyclicPauliLogRemainder
          (mixedCyclicPauliLikelihoodPerturbation theta h q 0 (omega k)) +
        pureCyclicPauliLogRemainder
          (mixedCyclicPauliLikelihoodPerturbation theta h q 1 (omega k)) +
        pureCyclicPauliLogRemainder
          (mixedCyclicPauliLikelihoodPerturbation theta h q 2 (omega k))| ≤
      6 * E ^ 3 := by
    have h0 := mixedCyclicPauliLogRemainder_abs_le_two_cube theta h hsmall 0 (omega k)
    have h1 := mixedCyclicPauliLogRemainder_abs_le_two_cube theta h hsmall 1 (omega k)
    have h2 := mixedCyclicPauliLogRemainder_abs_le_two_cube theta h hsmall 2 (omega k)
    calc
      |_ + _ + _| ≤ (|_| + |_|) + |_| := by
        exact (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
      _ ≤ (2 * E ^ 3 + 2 * E ^ 3) + 2 * E ^ 3 := by gcongr
      _ = 6 * E ^ 3 := by ring
  have hsum := Finset.abs_sum_le_sum_abs
    (fun k =>
      pureCyclicPauliLogRemainder
          (mixedCyclicPauliLikelihoodPerturbation theta h q 0 (omega k)) +
        pureCyclicPauliLogRemainder
          (mixedCyclicPauliLikelihoodPerturbation theta h q 1 (omega k)) +
        pureCyclicPauliLogRemainder
          (mixedCyclicPauliLikelihoodPerturbation theta h q 2 (omega k)))
    (Finset.range q)
  calc
    |mixedCyclicPauliLikelihoodRemainder theta h q omega| ≤
        ∑ k ∈ Finset.range q,
          |pureCyclicPauliLogRemainder
              (mixedCyclicPauliLikelihoodPerturbation theta h q 0 (omega k)) +
            pureCyclicPauliLogRemainder
              (mixedCyclicPauliLikelihoodPerturbation theta h q 1 (omega k)) +
            pureCyclicPauliLogRemainder
              (mixedCyclicPauliLikelihoodPerturbation theta h q 2 (omega k))| := by
      simpa [mixedCyclicPauliLikelihoodRemainder] using hsum
    _ ≤ ∑ _k ∈ Finset.range q, 6 * E ^ 3 := by
      exact Finset.sum_le_sum fun k _ => hblock k
    _ = (q : ℝ) * (6 * E ^ 3) := by simp
    _ = mixedCyclicPauliLikelihoodRemainderEnvelope theta h q := by
      have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
      have hsqrt0 : Real.sqrt (q : ℝ) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hq))
      have hsqrt : Real.sqrt (q : ℝ) ^ 2 = (q : ℝ) :=
        Real.sq_sqrt (Nat.cast_nonneg q)
      simp only [E, mixedCyclicPauliPerturbationEnvelope,
        mixedCyclicPauliLikelihoodRemainderEnvelope]
      field_simp [hq0, hsqrt0]
      rw [hsqrt]
      ring

/-- The deterministic likelihood-remainder envelope tends to zero. -/
theorem mixedCyclicPauliLikelihoodRemainderEnvelope_tendsto_zero
    (theta h : RLSVector 3) :
    Tendsto (mixedCyclicPauliLikelihoodRemainderEnvelope theta h) atTop (𝓝 0) := by
  have hsqrt : Tendsto (fun q : ℕ => Real.sqrt (q : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun q : ℕ => (Real.sqrt (q : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  change Tendsto
    (fun q : ℕ => (6 * mixedCyclicPauliPerturbationConstant theta h ^ 3) *
      (Real.sqrt (q : ℝ))⁻¹) atTop (𝓝 0)
  simpa using hinv.const_mul (6 * mixedCyclicPauliPerturbationConstant theta h ^ 3)

/-- The cubic-and-higher likelihood remainder vanishes pathwise. -/
theorem mixedCyclicPauliLikelihoodRemainder_tendsto_zero
    (theta h : RLSVector 3) (omega : MixedCyclicPauliOmega) :
    Tendsto (fun q => mixedCyclicPauliLikelihoodRemainder theta h q omega)
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun q => norm_nonneg _
  · filter_upwards [eventually_ge_atTop 1,
      mixedCyclicPauliPerturbationEnvelope_eventually_le_half theta h]
      with q hq hsmall
    have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq
    simpa [Real.norm_eq_abs] using
      mixedCyclicPauliLikelihoodRemainder_abs_le_envelope
        theta h hqpos hsmall omega
  · exact mixedCyclicPauliLikelihoodRemainderEnvelope_tendsto_zero theta h

private theorem pureCyclicPauliLogRemainder_measurable :
    Measurable pureCyclicPauliLogRemainder := by
  unfold pureCyclicPauliLogRemainder
  fun_prop

private theorem mixedCyclicPauliLikelihoodRemainder_measurable
    (theta h : RLSVector 3) (q : ℕ) :
    Measurable (mixedCyclicPauliLikelihoodRemainder theta h q) := by
  unfold mixedCyclicPauliLikelihoodRemainder
  apply Finset.measurable_sum
  intro k _
  have hu (j : Fin 3) : Measurable
      (fun omega : MixedCyclicPauliOmega =>
        mixedCyclicPauliLikelihoodPerturbation theta h q j (omega k)) := by
    have hblock : Measurable
        (mixedCyclicPauliLikelihoodPerturbation theta h q j) :=
      measurable_of_finite _
    exact hblock.comp (measurable_pi_apply k)
  exact ((pureCyclicPauliLogRemainder_measurable.comp (hu 0)).add
    (pureCyclicPauliLogRemainder_measurable.comp (hu 1))).add
    (pureCyclicPauliLogRemainder_measurable.comp (hu 2))

/-- The likelihood Taylor remainder vanishes in measure. -/
theorem mixedCyclicPauliLikelihoodRemainder_tendstoInMeasure
    (theta h : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta) :
    TendstoInMeasure (mixedCyclicPauliMeasure theta)
      (mixedCyclicPauliLikelihoodRemainder theta h) atTop (fun _ => 0) := by
  letI : IsProbabilityMeasure (mixedCyclicPauliBlockMeasure theta) :=
    ⟨pauliPilotBornProductMeasure_univ theta
      (mixedCyclicPauliStrictInterior_physical theta hInterior)⟩
  letI : ∀ _ : ℕ, IsProbabilityMeasure (mixedCyclicPauliBlockMeasure theta) :=
    fun _ => inferInstance
  apply tendstoInMeasure_of_tendsto_ae
  · intro q
    exact (mixedCyclicPauliLikelihoodRemainder_measurable theta h q).aestronglyMeasurable
  · exact Filter.Eventually.of_forall
      (mixedCyclicPauliLikelihoodRemainder_tendsto_zero theta h)

/-- Remainder in the deterministic-information LAN expansion. -/
noncomputable def mixedCyclicPauliLANRemainder
    (theta h : RLSVector 3) (q : ℕ) (omega : MixedCyclicPauliOmega) : ℝ :=
  mixedCyclicPauliLikelihoodRemainder theta h q omega +
    (mixedCyclicPauliFisherQuadratic theta h -
      mixedCyclicPauliObservedInformation theta h q omega) / 2

/-- Exact finite-sample LAN identity with deterministic Fisher information. -/
theorem mixedCyclicPauliLogLikelihoodRatio_exact_LAN
    (theta h : RLSVector 3) (q : ℕ) (omega : MixedCyclicPauliOmega) :
    mixedCyclicPauliLogLikelihoodRatio theta h q omega =
      mixedCyclicPauliNormalizedScore theta h q omega -
        mixedCyclicPauliFisherQuadratic theta h / 2 +
      mixedCyclicPauliLANRemainder theta h q omega := by
  rw [mixedCyclicPauliLogLikelihoodRatio_exact_observed]
  unfold mixedCyclicPauliLANRemainder
  ring

private theorem mixedCyclicPauliObservedInformation_measurable
    (theta h : RLSVector 3) (q : ℕ) :
    Measurable (mixedCyclicPauliObservedInformation theta h q) := by
  unfold mixedCyclicPauliObservedInformation
  have hinc (k : ℕ) :
      Measurable (mixedCyclicPauliObservedInformationIncrement theta h k) :=
    (measurable_of_finite _).comp (measurable_pi_apply k)
  exact (Finset.measurable_sum (Finset.range q) (fun k _ => hinc k)).const_mul (q : ℝ)⁻¹

private theorem mixedCyclicPauliLANRemainder_measurable
    (theta h : RLSVector 3) (q : ℕ) :
    Measurable (mixedCyclicPauliLANRemainder theta h q) := by
  unfold mixedCyclicPauliLANRemainder
  exact (mixedCyclicPauliLikelihoodRemainder_measurable theta h q).add
    ((measurable_const.sub (mixedCyclicPauliObservedInformation_measurable theta h q)).div_const 2)

/-- The complete deterministic-information LAN remainder vanishes almost surely. -/
theorem mixedCyclicPauliLANRemainder_tendsto_ae
    (theta h : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta) :
    ∀ᵐ omega ∂mixedCyclicPauliMeasure theta,
      Tendsto (fun q => mixedCyclicPauliLANRemainder theta h q omega)
        atTop (𝓝 0) := by
  filter_upwards [mixedCyclicPauliObservedInformation_tendsto_ae theta h hInterior]
    with omega hobs
  have hcorr : Tendsto
      (fun q => (mixedCyclicPauliFisherQuadratic theta h -
        mixedCyclicPauliObservedInformation theta h q omega) / 2)
      atTop (𝓝 0) := by
    convert (tendsto_const_nhds.sub hobs).div_const 2 using 1 <;> ring
  simpa [mixedCyclicPauliLANRemainder] using
    (mixedCyclicPauliLikelihoodRemainder_tendsto_zero theta h omega).add hcorr

/-- The complete deterministic-information LAN remainder vanishes in measure. -/
theorem mixedCyclicPauliLANRemainder_tendstoInMeasure
    (theta h : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta) :
    TendstoInMeasure (mixedCyclicPauliMeasure theta)
      (mixedCyclicPauliLANRemainder theta h) atTop (fun _ => 0) := by
  letI : IsProbabilityMeasure (mixedCyclicPauliBlockMeasure theta) :=
    ⟨pauliPilotBornProductMeasure_univ theta
      (mixedCyclicPauliStrictInterior_physical theta hInterior)⟩
  letI : ∀ _ : ℕ, IsProbabilityMeasure (mixedCyclicPauliBlockMeasure theta) :=
    fun _ => inferInstance
  apply tendstoInMeasure_of_tendsto_ae
  · intro q
    exact (mixedCyclicPauliLANRemainder_measurable theta h q).aestronglyMeasurable
  · exact mixedCyclicPauliLANRemainder_tendsto_ae theta h hInterior

/-- Complete scalar LAN package for the strict-interior mixed one-qubit cyclic-Pauli design. -/
def MixedCyclicPauliLAN
    (theta h : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta) : Prop :=
  (let _ : IsProbabilityMeasure (mixedCyclicPauliBlockMeasure theta) :=
      ⟨pauliPilotBornProductMeasure_univ theta
        (mixedCyclicPauliStrictInterior_physical theta hInterior)⟩
   let _ : ∀ _ : ℕ, IsProbabilityMeasure (mixedCyclicPauliBlockMeasure theta) :=
      fun _ => inferInstance
   let _ : ∀ _ : ℕ, IsProbabilityMeasure (mixedCyclicPauliMeasure theta) :=
      fun _ => inferInstance
   TendstoInDistribution (mixedCyclicPauliNormalizedScore theta h) atTop id
      (fun _ => mixedCyclicPauliMeasure theta)
      (gaussianReal 0 (mixedCyclicPauliFisherQuadratic theta h).toNNReal)) ∧
  (∀ q omega,
    mixedCyclicPauliLogLikelihoodRatio theta h q omega =
      mixedCyclicPauliNormalizedScore theta h q omega -
        mixedCyclicPauliFisherQuadratic theta h / 2 +
      mixedCyclicPauliLANRemainder theta h q omega) ∧
  TendstoInMeasure (mixedCyclicPauliMeasure theta)
    (mixedCyclicPauliLANRemainder theta h) atTop (fun _ => 0)

/-- Kernel-proved mixed-state cyclic-Pauli LAN theorem. -/
theorem mixedCyclicPauli_LAN
    (theta h : RLSVector 3) (hInterior : MixedCyclicPauliStrictInterior theta) :
    MixedCyclicPauliLAN theta h hInterior := by
  unfold MixedCyclicPauliLAN
  refine ⟨?_, ?_, ?_⟩
  · exact mixedCyclicPauliNormalizedScore_CLT theta h hInterior
  · exact mixedCyclicPauliLogLikelihoodRatio_exact_LAN theta h
  · exact mixedCyclicPauliLANRemainder_tendstoInMeasure theta h hInterior

end QubitOracle.Paper
