import QubitOracle.Paper.InformationPathLabelStrengthening
import QubitOracle.Paper.AdaptivePolicyMixture
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

noncomputable section

namespace QubitOracle.Paper

open scoped BigOperators
open Filter MeasureTheory

/-- Normalized average of vectors multiplied by nonnegative scalar weights. -/
def normalizedWeightedAverage
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (weight : ℕ → ℝ) (value : ℕ → E) (n : ℕ) : E :=
  (n : ℝ)⁻¹ •
    ∑ k ∈ Finset.range n, weight k • value k

/-- A deterministic norm bound for a normalized weighted average. -/
theorem normalizedWeightedAverage_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (weight : ℕ → ℝ) (value : ℕ → E) (C : ℝ)
    (hweight : ∀ k, 0 ≤ weight k)
    (hvalue : ∀ k, ‖value k‖ ≤ C)
    (n : ℕ) :
    ‖normalizedWeightedAverage weight value n‖ ≤
      C * ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, weight k) := by
  have hninv : 0 ≤ ((n : ℝ)⁻¹) :=
    inv_nonneg.mpr (Nat.cast_nonneg n)
  unfold normalizedWeightedAverage
  calc
    ‖(n : ℝ)⁻¹ •
        ∑ k ∈ Finset.range n, weight k • value k‖ =
        (n : ℝ)⁻¹ *
          ‖∑ k ∈ Finset.range n, weight k • value k‖ := by
      rw [norm_smul, Real.norm_of_nonneg hninv]
    _ ≤ (n : ℝ)⁻¹ *
        ∑ k ∈ Finset.range n, ‖weight k • value k‖ :=
      mul_le_mul_of_nonneg_left
        (norm_sum_le (Finset.range n)
          (fun k => weight k • value k)) hninv
    _ = (n : ℝ)⁻¹ *
        ∑ k ∈ Finset.range n, weight k * ‖value k‖ := by
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [norm_smul, Real.norm_of_nonneg (hweight k)]
    _ ≤ (n : ℝ)⁻¹ *
        ∑ k ∈ Finset.range n, weight k * C := by
      apply mul_le_mul_of_nonneg_left _ hninv
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (hvalue k) (hweight k)
    _ = C * ((n : ℝ)⁻¹ *
        ∑ k ∈ Finset.range n, weight k) := by
      rw [← Finset.sum_mul]
      ring

/-- If nonnegative weights have vanishing empirical average and the vectors
are uniformly bounded, their normalized weighted sum tends to zero. -/
theorem normalizedWeightedAverage_tendsto_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (weight : ℕ → ℝ) (value : ℕ → E) (C : ℝ)
    (hC : 0 ≤ C)
    (hweight : ∀ k, 0 ≤ weight k)
    (hvalue : ∀ k, ‖value k‖ ≤ C)
    (haverage : Tendsto
      (fun n : ℕ =>
        (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, weight k)
      atTop (nhds 0)) :
    Tendsto (normalizedWeightedAverage weight value)
      atTop (nhds 0) := by
  have hupper : Tendsto
      (fun n : ℕ =>
        C * ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, weight k))
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul haverage)
  have hnorm : Tendsto
      (fun n : ℕ => ‖normalizedWeightedAverage weight value n‖)
      atTop (nhds 0) :=
    squeeze_zero'
      (Eventually.of_forall fun n => norm_nonneg _)
      (Eventually.of_forall fun n =>
        normalizedWeightedAverage_norm_le
          weight value C hweight hvalue n)
      hupper
  apply (tendsto_iff_norm_sub_tendsto_zero).2
  simpa only [sub_zero] using hnorm

/-- Pointwise convex mixture of exploitation and exploration information. -/
def informationMixture
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (epsilon : ℕ → ℝ) (exploit explore : ℕ → E) (k : ℕ) : E :=
  (1 - epsilon k) • exploit k + epsilon k • explore k

/-- A convex mixture is its exploitation term plus a weighted perturbation. -/
theorem informationMixture_eq_exploit_add_error
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (epsilon : ℕ → ℝ) (exploit explore : ℕ → E) (k : ℕ) :
    informationMixture epsilon exploit explore k =
      exploit k + epsilon k • (explore k - exploit k) := by
  unfold informationMixture
  module

/-- Weighted Cesaro assembly used in the mixed information proof.  Pointwise
convergence of exploitation information and a vanishing average exploration
weight force the average mixture information to have the exploitation
limit. -/
theorem informationMixture_cesaro_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (epsilon : ℕ → ℝ) (exploit explore : ℕ → E)
    (target : E) (C : ℝ)
    (hC : 0 ≤ C)
    (hepsilon : ∀ k, 0 ≤ epsilon k)
    (hexploit : Tendsto exploit atTop (nhds target))
    (hdifference : ∀ k, ‖explore k - exploit k‖ ≤ C)
    (hschedule : Tendsto
      (fun n : ℕ =>
        (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, epsilon k)
      atTop (nhds 0)) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ)⁻¹ •
          ∑ k ∈ Finset.range n,
            informationMixture epsilon exploit explore k)
      atTop (nhds target) := by
  have hmain := hexploit.cesaro_smul
  have herror := normalizedWeightedAverage_tendsto_zero
    epsilon (fun k => explore k - exploit k) C
    hC hepsilon hdifference hschedule
  have hdecompose :
      (fun n : ℕ =>
        (n : ℝ)⁻¹ •
          ∑ k ∈ Finset.range n,
            informationMixture epsilon exploit explore k) =
      (fun n : ℕ =>
        (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, exploit k +
          normalizedWeightedAverage epsilon
            (fun k => explore k - exploit k) n) := by
    funext n
    unfold normalizedWeightedAverage
    simp_rw [informationMixture_eq_exploit_add_error]
    rw [Finset.sum_add_distrib, smul_add]
  rw [hdecompose]
  simpa using hmain.add herror

/-- History available immediately before each zero-based shot. -/
def mixedPathHistoryAllShots
    {M Y : Type*}
    (omega : ℕ → M × Y) : ℕ → SequentialHistory M Y :=
  prependSequence []
    (fun k =>
      trajectoryPrefixHistory (Preorder.frestrictLe k omega))

/-- Realized mixed Fisher information at every path coordinate. -/
def mixedPathObservedInformationAllShots
    {M Y : Type*}
    (r : Fin 3 → ℝ) (axis : M → Fin 3 → ℝ)
    (omega : ℕ → M × Y) (k : ℕ) : OracleMatrix :=
  QubitOracle.mixedAxisFisher r (axis (omega k).1)

/-- Predictable mixed Fisher information immediately before every shot. -/
def mixedPathPredictableInformationAllShots
    {M Y : Type*} [Fintype M]
    (q : AdaptivePolicy M Y)
    (r : Fin 3 → ℝ) (axis : M → Fin 3 → ℝ)
    (omega : ℕ → M × Y) (k : ℕ) : OracleMatrix :=
  mixedPolicyMeanInformation q
    (mixedPathHistoryAllShots omega k) r axis

/-- Normalized observed information along a complete adaptive path. -/
def mixedPathObservedInformationAverage
    {M Y : Type*}
    (r : Fin 3 → ℝ) (axis : M → Fin 3 → ℝ)
    (omega : ℕ → M × Y) (n : ℕ) : OracleMatrix :=
  (n : ℝ)⁻¹ •
    ∑ k ∈ Finset.range n,
      mixedPathObservedInformationAllShots r axis omega k

/-- Normalized predictable information along a complete adaptive path. -/
def mixedPathPredictableInformationAverage
    {M Y : Type*} [Fintype M]
    (q : AdaptivePolicy M Y)
    (r : Fin 3 → ℝ) (axis : M → Fin 3 → ℝ)
    (omega : ℕ → M × Y) (n : ℕ) : OracleMatrix :=
  (n : ℝ)⁻¹ •
    ∑ k ∈ Finset.range n,
      mixedPathPredictableInformationAllShots q r axis omega k

/-- Normalized all-shot martingale innovation along a complete path. -/
def mixedPathInformationInnovationAverage
    {M Y : Type*} [Fintype M]
    (q : AdaptivePolicy M Y)
    (r : Fin 3 → ℝ) (axis : M → Fin 3 → ℝ)
    (omega : ℕ → M × Y) (n : ℕ) : OracleMatrix :=
  (n : ℝ)⁻¹ •
    ∑ k ∈ Finset.range n,
      mixedPathInformationInnovationAllShots q r axis omega k

/-- The all-shot innovation is observed information minus its predictable
conditional mean, including the initial shot. -/
theorem mixedPathInformationInnovationAllShots_eq
    {M Y : Type*} [Fintype M]
    (q : AdaptivePolicy M Y)
    (r : Fin 3 → ℝ) (axis : M → Fin 3 → ℝ)
    (omega : ℕ → M × Y) (k : ℕ) :
    mixedPathInformationInnovationAllShots q r axis omega k =
      mixedPathObservedInformationAllShots r axis omega k -
        mixedPathPredictableInformationAllShots q r axis omega k := by
  cases k <;> rfl

/-- Exact finite-sample observed = predictable + innovation decomposition. -/
theorem mixedPathObservedInformationAverage_decompose
    {M Y : Type*} [Fintype M]
    (q : AdaptivePolicy M Y)
    (r : Fin 3 → ℝ) (axis : M → Fin 3 → ℝ)
    (omega : ℕ → M × Y) (n : ℕ) :
    mixedPathObservedInformationAverage r axis omega n =
      mixedPathPredictableInformationAverage q r axis omega n +
        mixedPathInformationInnovationAverage q r axis omega n := by
  unfold mixedPathObservedInformationAverage
    mixedPathPredictableInformationAverage
    mixedPathInformationInnovationAverage
  have hterm : ∀ k,
      mixedPathObservedInformationAllShots r axis omega k =
        mixedPathPredictableInformationAllShots q r axis omega k +
          mixedPathInformationInnovationAllShots q r axis omega k := by
    intro k
    rw [mixedPathInformationInnovationAllShots_eq]
    abel
  simp_rw [hterm, Finset.sum_add_distrib, smul_add]

/-- Generic mixed branch of `thm:SI_information`: once the predictable
information average has the oracle limit, the verified path-space martingale
strong law gives the same limit for realized information. -/
theorem mixedPathObservedInformation_strongLaw_of_predictable
    {Theta M Y : Type*} [Fintype M] [Fintype Y]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [StandardBorelSpace M] [StandardBorelSpace Y]
    [Nonempty M] [Nonempty Y]
    (q : AdaptivePolicy M Y) (p : OutcomeKernel Theta M Y) (theta : Theta)
    (r : Fin 3 → ℝ) (axis : M → Fin 3 → ℝ)
    (hr : QubitOracle.blochNormSq r < 1)
    (haxis : ∀ m, QubitOracle.blochNormSq (axis m) = 1)
    (target : OracleMatrix)
    (hpredictable :
      ∀ᵐ omega : ℕ → M × Y ∂ adaptiveTrajectoryMeasure q p theta,
        Tendsto
          (mixedPathPredictableInformationAverage q r axis omega)
          atTop (nhds target)) :
    ∀ᵐ omega : ℕ → M × Y ∂ adaptiveTrajectoryMeasure q p theta,
      Tendsto
        (mixedPathObservedInformationAverage r axis omega)
        atTop (nhds target) := by
  have hslln := Label.eq_SI_info_martingale_SLLN
    q p theta r axis hr haxis
  filter_upwards [hpredictable, hslln] with omega hpredictableOmega hsllnOmega
  have hinnovation : Tendsto
      (mixedPathInformationInnovationAverage q r axis omega)
      atTop (nhds 0) := by
    unfold mixedPathInformationInnovationAverage
    have hsequence :
        mixedPathInformationInnovationAllShots q r axis omega =
          prependSequence
            (mixedInitialInformationInnovation q r axis omega)
            (mixedTailInformationInnovation q r axis omega) := rfl
    rw [hsequence]
    exact hsllnOmega
  have hsum := hpredictableOmega.add hinnovation
  have hdecompose :
      mixedPathObservedInformationAverage r axis omega =
        fun n =>
          mixedPathPredictableInformationAverage q r axis omega n +
            mixedPathInformationInnovationAverage q r axis omega n := by
    funext n
    exact mixedPathObservedInformationAverage_decompose
      q r axis omega n
  rw [hdecompose]
  simpa using hsum

namespace Label

/-- Kernel-checked martingale assembly for the mixed branch of
`thm:SI_information`. -/
theorem thm_SI_information_of_predictable
    {Theta M Y : Type*} [Fintype M] [Fintype Y]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [StandardBorelSpace M] [StandardBorelSpace Y]
    [Nonempty M] [Nonempty Y]
    (q : AdaptivePolicy M Y) (p : OutcomeKernel Theta M Y) (theta : Theta)
    (r : Fin 3 → ℝ) (axis : M → Fin 3 → ℝ)
    (hr : QubitOracle.blochNormSq r < 1)
    (haxis : ∀ m, QubitOracle.blochNormSq (axis m) = 1)
    (target : OracleMatrix)
    (hpredictable :
      ∀ᵐ omega : ℕ → M × Y ∂ adaptiveTrajectoryMeasure q p theta,
        Tendsto
          (mixedPathPredictableInformationAverage q r axis omega)
          atTop (nhds target)) :
    ∀ᵐ omega : ℕ → M × Y ∂ adaptiveTrajectoryMeasure q p theta,
      Tendsto
        (mixedPathObservedInformationAverage r axis omega)
        atTop (nhds target) := by
  exact mixedPathObservedInformation_strongLaw_of_predictable
    q p theta r axis hr haxis target hpredictable

end Label

end QubitOracle.Paper
