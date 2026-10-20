import QubitOracle.Paper.OneQubitMixedTwoStageFiniteScore
import QubitOracle.Paper.OneQubitBernoulliLANAlgebra
import QubitOracle.Paper.OneQubitLogTaylorBound
import QubitOracle.Paper.OneQubitMixedUniformScoreEnvelope

/-!
# Exact-cycle conditional Taylor remainder for the mixed qubit

Fix the completed pilot and its selected orthonormal final frame.  At final
horizon `N = 3 * r`, this file identifies every conditional Born-factor ratio
between `theta` and `theta + h / sqrt N` with `1 + x_t`, where `x_t` is the
directional score divided by `sqrt N`.  The existing scalar logarithm bound
then gives a deterministic, pathwise cubic remainder whose envelope tends to
zero.

No information convergence, martingale CLT, or probability limit is used.
In particular, the centered fluctuation of the observed quadratic score sum
around its conditional Fisher value is not controlled here.
-/

open scoped BigOperators

namespace QubitOracle.Paper

open Filter

noncomputable section

/-- Root-`N` local perturbation at the exact-cycle horizon `N = 3 * r`. -/
def mixedExactCycleLocalParameter
    (theta h : Fin 3 -> ℝ) (r : ℕ) : Fin 3 -> ℝ :=
  fun i => theta i + h i / Real.sqrt (3 * r : ℕ)

/-- Fixed-pilot base Bernoulli mean at one final time. -/
def mixedExactCycleBaseMean
    {q r : ℕ} (theta : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) :
    Fin (3 * r) -> (Fin (3 * r) -> Bool) -> ℝ :=
  fun t _path =>
    QubitOracle.blochDot theta
      (mixedTwoStageFinalAxis selected pilot t)

/-- Fixed-pilot directional derivative of the Bernoulli mean. -/
def mixedExactCycleLocalDirection
    {q r : ℕ} (h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) :
    Fin (3 * r) -> (Fin (3 * r) -> Bool) -> ℝ :=
  fun t _path =>
    QubitOracle.blochDot h
      (mixedTwoStageFinalAxis selected pilot t)

/-- The final directional score increment divided by `sqrt (3 * r)`. -/
def mixedExactCycleNormalizedDirectionalScore
    {q r : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) (t : Fin (3 * r))
    (finalPath : MixedTwoStageFinalPath (3 * r)) : ℝ :=
  mixedTwoStageFinalPathDirectionalScore
      theta h selected pilot t finalPath /
    Real.sqrt (3 * r : ℕ)

/-- Conditional final-path log likelihood, written as the equivalent finite
sum of logarithms of `1 +` the local Bernoulli ratios. -/
def mixedExactCycleConditionalLogLikelihoodRatio
    {q r : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q)
    (finalPath : MixedTwoStageFinalPath (3 * r)) : ℝ :=
  bernoulliLogLikelihoodRatio
    (mixedExactCycleBaseMean theta selected pilot)
    (mixedExactCycleLocalDirection h selected pilot)
    finalPath

/-- Root-`N` linear score term. -/
def mixedExactCycleLinearScoreTerm
    {q r : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q)
    (finalPath : MixedTwoStageFinalPath (3 * r)) : ℝ :=
  ∑ t : Fin (3 * r),
    mixedExactCycleNormalizedDirectionalScore
      theta h selected pilot t finalPath

/-- Observed quadratic term before centering by its conditional mean. -/
def mixedExactCycleObservedQuadraticTerm
    {q r : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q)
    (finalPath : MixedTwoStageFinalPath (3 * r)) : ℝ :=
  ∑ t : Fin (3 * r),
    mixedExactCycleNormalizedDirectionalScore
      theta h selected pilot t finalPath ^ 2

/-- Summed scalar third-order logarithm remainder. -/
def mixedExactCycleTaylorRemainder
    {q r : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q)
    (finalPath : MixedTwoStageFinalPath (3 * r)) : ℝ :=
  ∑ t : Fin (3 * r),
    logThirdOrderRemainder
      (mixedExactCycleNormalizedDirectionalScore
        theta h selected pilot t finalPath)

/-- Deterministic cubic envelope after cancellation of one factor of the
three-cycle horizon against `sqrt (3 * r) ^ 2`. -/
def mixedExactCycleCubicRemainderBound
    (theta h : Fin 3 -> ℝ) (r : ℕ) : ℝ :=
  (2 / 3 : ℝ) * mixedProjectedScoreEnvelope theta h ^ 3 /
    Real.sqrt (3 * r : ℕ)

@[simp]
theorem mixedExactCycle_bernoulliSign_eq_pauliOutcomeSign
    (outcome : Bool) :
    bernoulliSign outcome = pauliOutcomeSign outcome := by
  cases outcome <;> rfl

/-- The generic Bernoulli local ratio is exactly the normalized concrete
directional score increment. -/
theorem mixedExactCycle_bernoulliLocalRatio_eq_normalizedDirectionalScore
    {q r : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q)
    (finalPath : MixedTwoStageFinalPath (3 * r))
    (t : Fin (3 * r)) :
    bernoulliLocalRatio
        (mixedExactCycleBaseMean theta selected pilot)
        (mixedExactCycleLocalDirection h selected pilot)
        finalPath t =
      mixedExactCycleNormalizedDirectionalScore
        theta h selected pilot t finalPath := by
  unfold bernoulliLocalRatio mixedExactCycleBaseMean
    mixedExactCycleLocalDirection
    mixedExactCycleNormalizedDirectionalScore
    mixedTwoStageFinalPathDirectionalScore
    mixedTwoStageFinalShotDirectionalScore
    mixedTwoStageAxisDirectionalScore
  rw [mixedExactCycle_bernoulliSign_eq_pauliOutcomeSign]
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- Bloch linearity for the local alternative. -/
theorem mixedExactCycleLocalParameter_blochDot
    (theta h axis : Fin 3 -> ℝ) (r : ℕ) :
    QubitOracle.blochDot (mixedExactCycleLocalParameter theta h r) axis =
      QubitOracle.blochDot theta axis +
        QubitOracle.blochDot h axis / Real.sqrt (3 * r : ℕ) := by
  unfold mixedExactCycleLocalParameter QubitOracle.blochDot
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- The Boolean Born factor in signed Bernoulli notation. -/
theorem mixedExactCycleAxisBornProbability_eq_signed
    (theta axis : Fin 3 -> ℝ) (outcome : Bool) :
    mixedTwoStageAxisBornProbability theta axis outcome =
      (1 + pauliOutcomeSign outcome *
        QubitOracle.blochDot theta axis) / 2 := by
  have hcomm := mixedTwoStageScore_blochDot_comm axis theta
  cases outcome <;>
    simp [mixedTwoStageAxisBornProbability, pauliOutcomeSign, hcomm,
      sub_eq_add_neg]

/-- The interior gap uniformly bounds the realized Boolean score
denominator for every unit final axis. -/
theorem mixedExactCycleScoreDenominator_floor
    (theta axis : Fin 3 -> ℝ) (outcome : Bool)
    (hAxis : QubitOracle.blochNormSq axis = 1) :
    mixedInteriorGap theta ≤
      1 + pauliOutcomeSign outcome *
        QubitOracle.blochDot theta axis := by
  have hfloors := mixedAxisScoreDenominator_floors theta axis hAxis
  cases outcome
  · simpa [pauliOutcomeSign, sub_eq_add_neg] using hfloors.2
  · simpa [pauliOutcomeSign] using hfloors.1

/-- One local Born-factor ratio is exactly `1 +` the normalized directional
score. -/
theorem mixedExactCycleAxisBornRatio_eq_one_add_normalizedScore
    (theta h axis : Fin 3 -> ℝ) (outcome : Bool) (r : ℕ)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hAxis : QubitOracle.blochNormSq axis = 1)
    (hr : 0 < r) :
    mixedTwoStageAxisBornProbability
        (mixedExactCycleLocalParameter theta h r) axis outcome /
        mixedTwoStageAxisBornProbability theta axis outcome =
      1 + mixedTwoStageAxisDirectionalScore theta h axis outcome /
        Real.sqrt (3 * r : ℕ) := by
  have hN : 0 < 3 * r := Nat.mul_pos (by norm_num) hr
  have hsqrt : 0 < Real.sqrt (3 * r : ℕ) := by
    exact Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hgap : 0 < mixedInteriorGap theta :=
    mixedInteriorGap_pos theta hInterior
  have hfloor :=
    mixedExactCycleScoreDenominator_floor theta axis outcome hAxis
  have hden :
      0 < 1 + pauliOutcomeSign outcome *
        QubitOracle.blochDot theta axis :=
    hgap.trans_le hfloor
  rw [mixedExactCycleAxisBornProbability_eq_signed,
    mixedExactCycleAxisBornProbability_eq_signed,
    mixedExactCycleLocalParameter_blochDot]
  unfold mixedTwoStageAxisDirectionalScore
  field_simp [ne_of_gt hsqrt, ne_of_gt hden]
  <;> ring

/-- Final-shot specialization of the exact Born-factor ratio identity. -/
theorem mixedExactCycleFinalBornRatio_eq_one_add_normalizedScore
    {q r : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q)
    (finalPath : MixedTwoStageFinalPath (3 * r))
    (t : Fin (3 * r))
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hr : 0 < r) :
    mixedTwoStageFinalBornProbability
        (mixedExactCycleLocalParameter theta h r)
        selected pilot t (finalPath t) /
        mixedTwoStageFinalBornProbability
          theta selected pilot t (finalPath t) =
      1 + mixedExactCycleNormalizedDirectionalScore
        theta h selected pilot t finalPath := by
  rw [mixedTwoStageFinalBornProbability_eq_axisBornProbability,
    mixedTwoStageFinalBornProbability_eq_axisBornProbability]
  simpa [mixedExactCycleNormalizedDirectionalScore,
    mixedTwoStageFinalPathDirectionalScore,
    mixedTwoStageFinalShotDirectionalScore] using
    (mixedExactCycleAxisBornRatio_eq_one_add_normalizedScore
      theta h (mixedTwoStageFinalAxis selected pilot t)
      (finalPath t) r hInterior
      (mixedTwoStageFinalAxis_unit selected pilot t) hr)

/-- Item 1 and item 2: the conditional log likelihood is the sum of
`log (1 + x_t)`, with `x_t` the normalized concrete score increment. -/
theorem mixedExactCycleConditionalLogLikelihoodRatio_eq_sum_log_one_add
    {q r : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q)
    (finalPath : MixedTwoStageFinalPath (3 * r)) :
    mixedExactCycleConditionalLogLikelihoodRatio
        theta h selected pilot finalPath =
      ∑ t : Fin (3 * r),
        Real.log (1 + mixedExactCycleNormalizedDirectionalScore
          theta h selected pilot t finalPath) := by
  unfold mixedExactCycleConditionalLogLikelihoodRatio
    bernoulliLogLikelihoodRatio
  apply Finset.sum_congr rfl
  intro t _ht
  rw [mixedExactCycle_bernoulliLocalRatio_eq_normalizedDirectionalScore]

/-- The same conditional log likelihood written explicitly as the sum of
logarithms of perturbed-to-true Born-factor ratios. -/
theorem mixedExactCycleConditionalLogLikelihoodRatio_eq_sum_log_bornRatios
    {q r : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q)
    (finalPath : MixedTwoStageFinalPath (3 * r))
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hr : 0 < r) :
    mixedExactCycleConditionalLogLikelihoodRatio
        theta h selected pilot finalPath =
      ∑ t : Fin (3 * r),
        Real.log
          (mixedTwoStageFinalBornProbability
              (mixedExactCycleLocalParameter theta h r)
              selected pilot t (finalPath t) /
            mixedTwoStageFinalBornProbability
              theta selected pilot t (finalPath t)) := by
  rw [mixedExactCycleConditionalLogLikelihoodRatio_eq_sum_log_one_add]
  apply Finset.sum_congr rfl
  intro t _ht
  rw [mixedExactCycleFinalBornRatio_eq_one_add_normalizedScore
    theta h selected pilot finalPath t hInterior hr]

/-- Exact finite Taylor decomposition.  The observed quadratic term remains
path-dependent and is not replaced by Fisher information in this file. -/
theorem mixedExactCycleConditionalLogLikelihoodRatio_exactTaylor
    {q r : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q)
    (finalPath : MixedTwoStageFinalPath (3 * r)) :
    mixedExactCycleConditionalLogLikelihoodRatio
        theta h selected pilot finalPath =
      mixedExactCycleLinearScoreTerm
          theta h selected pilot finalPath -
        mixedExactCycleObservedQuadraticTerm
          theta h selected pilot finalPath / 2 +
        mixedExactCycleTaylorRemainder
          theta h selected pilot finalPath := by
  simpa [mixedExactCycleConditionalLogLikelihoodRatio,
    mixedExactCycleLinearScoreTerm,
    mixedExactCycleObservedQuadraticTerm,
    mixedExactCycleTaylorRemainder,
    bernoulliLocalScore, bernoulliObservedQuadratic,
    bernoulliLANRemainder,
    mixedExactCycle_bernoulliLocalRatio_eq_normalizedDirectionalScore] using
    (bernoulliLogLikelihoodRatio_exact_decomposition
      (mixedExactCycleBaseMean theta selected pilot)
      (mixedExactCycleLocalDirection h selected pilot)
      finalPath)

/-- Item 3: the existing scalar logarithm Taylor theorem applied to one
fixed-pilot final shot. -/
theorem mixedExactCyclePointwise_logTaylor_bound
    {q r : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q)
    (finalPath : MixedTwoStageFinalPath (3 * r))
    (t : Fin (3 * r))
    (hsmall :
      |mixedExactCycleNormalizedDirectionalScore
        theta h selected pilot t finalPath| ≤ 1 / 2) :
    |logThirdOrderRemainder
      (mixedExactCycleNormalizedDirectionalScore
        theta h selected pilot t finalPath)| ≤
      (2 / 3 : ℝ) *
        |mixedExactCycleNormalizedDirectionalScore
          theta h selected pilot t finalPath| ^ 3 :=
  logThirdOrderRemainder_le_twoThirds _ hsmall

/-- A unit final axis bounds the directional derivative by the finite
coordinate `l1` norm used by the interior score envelope. -/
theorem mixedExactCycleDirectionalDot_abs_le_l1
    (h axis : Fin 3 -> ℝ)
    (hAxis : QubitOracle.blochNormSq axis = 1) :
    |QubitOracle.blochDot h axis| ≤ mixedProjectionL1 h := by
  unfold QubitOracle.blochDot mixedProjectionL1
  calc
    |∑ i : Fin 3, h i * axis i| ≤
        ∑ i : Fin 3, |h i * axis i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, |h i| := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [abs_mul]
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left
          (unitBlochAxis_coordinate_abs_le_one axis hAxis i)
          (abs_nonneg (h i)))

/-- Interior, path-independent envelope for every normalized score
increment. -/
theorem mixedExactCycleNormalizedDirectionalScore_abs_le_envelope
    {q r : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q)
    (finalPath : MixedTwoStageFinalPath (3 * r))
    (t : Fin (3 * r))
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hr : 0 < r) :
    |mixedExactCycleNormalizedDirectionalScore
        theta h selected pilot t finalPath| ≤
      mixedProjectedScoreEnvelope theta h /
        Real.sqrt (3 * r : ℕ) := by
  have hN : 0 < 3 * r := Nat.mul_pos (by norm_num) hr
  have hsqrt : 0 < Real.sqrt (3 * r : ℕ) := by
    exact Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hgap : 0 < mixedInteriorGap theta :=
    mixedInteriorGap_pos theta hInterior
  have hL1 : 0 ≤ mixedProjectionL1 h := by
    unfold mixedProjectionL1
    exact Finset.sum_nonneg (fun i _hi => abs_nonneg (h i))
  have hratio := abs_bernoulliLocalRatio_le hN
    (mixedExactCycleBaseMean theta selected pilot)
    (mixedExactCycleLocalDirection h selected pilot)
    finalPath t (mixedInteriorGap theta) (mixedProjectionL1 h)
    hgap hL1
    (by
      simpa [mixedExactCycleBaseMean] using
        (mixedExactCycleScoreDenominator_floor theta
          (mixedTwoStageFinalAxis selected pilot t) (finalPath t)
          (mixedTwoStageFinalAxis_unit selected pilot t)))
    (by
      simpa [mixedExactCycleLocalDirection] using
        (mixedExactCycleDirectionalDot_abs_le_l1 h
          (mixedTwoStageFinalAxis selected pilot t)
          (mixedTwoStageFinalAxis_unit selected pilot t)))
  rw [mixedExactCycle_bernoulliLocalRatio_eq_normalizedDirectionalScore]
    at hratio
  calc
    |mixedExactCycleNormalizedDirectionalScore
        theta h selected pilot t finalPath| ≤
        mixedProjectionL1 h /
          (mixedInteriorGap theta * Real.sqrt (3 * r : ℕ)) :=
      hratio
    _ = mixedProjectedScoreEnvelope theta h /
        Real.sqrt (3 * r : ℕ) := by
      unfold mixedProjectedScoreEnvelope
      field_simp [ne_of_gt hgap, ne_of_gt hsqrt]
      <;> ring

/-- Elementary cancellation `N / (sqrt N)^3 = 1 / sqrt N` at a positive
exact-cycle horizon. -/
theorem mixedExactCycle_count_div_sqrt_cube
    (r : ℕ) (hr : 0 < r) :
    ((3 * r : ℕ) : ℝ) /
        Real.sqrt (3 * r : ℕ) ^ 3 =
      1 / Real.sqrt (3 * r : ℕ) := by
  let s : ℝ := Real.sqrt (3 * r : ℕ)
  have hN : 0 < 3 * r := Nat.mul_pos (by norm_num) hr
  have hs : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hsq : s ^ 2 = ((3 * r : ℕ) : ℝ) := by
    dsimp [s]
    exact Real.sq_sqrt (Nat.cast_nonneg _)
  change ((3 * r : ℕ) : ℝ) / s ^ 3 = 1 / s
  rw [← hsq]
  field_simp [ne_of_gt hs]
  <;> ring

/-- Item 4: deterministic pathwise bound for the summed cubic remainder. -/
theorem mixedExactCycleTaylorRemainder_abs_le_cubicBound
    {q r : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q)
    (finalPath : MixedTwoStageFinalPath (3 * r))
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hr : 0 < r)
    (hsmall : mixedProjectedScoreEnvelope theta h /
      Real.sqrt (3 * r : ℕ) ≤ 1 / 2) :
    |mixedExactCycleTaylorRemainder
        theta h selected pilot finalPath| ≤
      mixedExactCycleCubicRemainderBound theta h r := by
  have hratio : ∀ t : Fin (3 * r),
      |mixedExactCycleNormalizedDirectionalScore
        theta h selected pilot t finalPath| ≤
      mixedProjectedScoreEnvelope theta h /
        Real.sqrt (3 * r : ℕ) := by
    intro t
    exact mixedExactCycleNormalizedDirectionalScore_abs_le_envelope
      theta h selected pilot finalPath t hInterior hr
  calc
    |mixedExactCycleTaylorRemainder
        theta h selected pilot finalPath| ≤
        ∑ t : Fin (3 * r),
          |logThirdOrderRemainder
            (mixedExactCycleNormalizedDirectionalScore
              theta h selected pilot t finalPath)| := by
      unfold mixedExactCycleTaylorRemainder
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t : Fin (3 * r),
        (2 / 3 : ℝ) *
          (mixedProjectedScoreEnvelope theta h /
            Real.sqrt (3 * r : ℕ)) ^ 3 := by
      apply Finset.sum_le_sum
      intro t _ht
      calc
        |logThirdOrderRemainder
          (mixedExactCycleNormalizedDirectionalScore
            theta h selected pilot t finalPath)| ≤
            (2 / 3 : ℝ) *
              |mixedExactCycleNormalizedDirectionalScore
                theta h selected pilot t finalPath| ^ 3 :=
          mixedExactCyclePointwise_logTaylor_bound
            theta h selected pilot finalPath t ((hratio t).trans hsmall)
        _ ≤ (2 / 3 : ℝ) *
            (mixedProjectedScoreEnvelope theta h /
              Real.sqrt (3 * r : ℕ)) ^ 3 := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (abs_nonneg _) (hratio t) 3)
            (by norm_num)
    _ = ((3 * r : ℕ) : ℝ) * (2 / 3 : ℝ) *
        (mixedProjectedScoreEnvelope theta h /
          Real.sqrt (3 * r : ℕ)) ^ 3 := by
      simp
      ring
    _ = mixedExactCycleCubicRemainderBound theta h r := by
      unfold mixedExactCycleCubicRemainderBound
      rw [show
        ((3 * r : ℕ) : ℝ) * (2 / 3 : ℝ) *
            (mixedProjectedScoreEnvelope theta h /
              Real.sqrt (3 * r : ℕ)) ^ 3 =
          (2 / 3 : ℝ) * mixedProjectedScoreEnvelope theta h ^ 3 *
            (((3 * r : ℕ) : ℝ) /
              Real.sqrt (3 * r : ℕ) ^ 3) by ring]
      rw [mixedExactCycle_count_div_sqrt_cube r hr]
      ring

/-- The normalized score envelope itself tends to zero, so the pointwise
Taylor condition `|x_t| <= 1/2` holds eventually for fixed `theta` and `h`. -/
theorem mixedExactCycleNormalizedEnvelope_tendsto_zero
    (theta h : Fin 3 -> ℝ) :
    Tendsto
      (fun r : ℕ => mixedProjectedScoreEnvelope theta h /
        Real.sqrt (3 * r : ℕ))
      atTop (nhds 0) := by
  have hcast :
      Tendsto (fun r : ℕ => (3 : ℝ) * (r : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hsqrt :
      Tendsto (fun r : ℕ => Real.sqrt (3 * r : ℕ)) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_mul, Nat.cast_ofNat] using
      (Real.tendsto_sqrt_atTop.comp hcast)
  have hinv :
      Tendsto (fun r : ℕ => (Real.sqrt (3 * r : ℕ))⁻¹)
        atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  have hmul :=
    (tendsto_const_nhds (f := atTop)
      (x := mixedProjectedScoreEnvelope theta h)).mul hinv
  simpa [div_eq_mul_inv] using
    (hmul : Tendsto
      (fun r : ℕ => mixedProjectedScoreEnvelope theta h *
        (Real.sqrt (3 * r : ℕ))⁻¹)
      atTop (nhds (mixedProjectedScoreEnvelope theta h * 0)))

theorem mixedExactCycleNormalizedEnvelope_eventually_le_half
    (theta h : Fin 3 -> ℝ) :
    ∀ᶠ r : ℕ in atTop,
      mixedProjectedScoreEnvelope theta h /
        Real.sqrt (3 * r : ℕ) ≤ 1 / 2 := by
  have hlt := (tendsto_order.1
    (mixedExactCycleNormalizedEnvelope_tendsto_zero theta h)).2
      (1 / 2) (by norm_num)
  filter_upwards [hlt] with r hr
  exact le_of_lt hr

/-- Item 5: the deterministic cubic bound tends to zero. -/
theorem mixedExactCycleCubicRemainderBound_tendsto_zero
    (theta h : Fin 3 -> ℝ) :
    Tendsto (mixedExactCycleCubicRemainderBound theta h)
      atTop (nhds 0) := by
  have hcast :
      Tendsto (fun r : ℕ => (3 : ℝ) * (r : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hsqrt :
      Tendsto (fun r : ℕ => Real.sqrt (3 * r : ℕ)) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_mul, Nat.cast_ofNat] using
      (Real.tendsto_sqrt_atTop.comp hcast)
  have hinv :
      Tendsto (fun r : ℕ => (Real.sqrt (3 * r : ℕ))⁻¹)
        atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  unfold mixedExactCycleCubicRemainderBound
  have hmul :=
    (tendsto_const_nhds (f := atTop)
      (x := (2 / 3 : ℝ) * mixedProjectedScoreEnvelope theta h ^ 3)).mul hinv
  simpa [div_eq_mul_inv] using
    (hmul : Tendsto
      (fun r : ℕ =>
        ((2 / 3 : ℝ) * mixedProjectedScoreEnvelope theta h ^ 3) *
          (Real.sqrt (3 * r : ℕ))⁻¹)
      atTop
      (nhds (((2 / 3 : ℝ) *
        mixedProjectedScoreEnvelope theta h ^ 3) * 0)))

/-- Fully deterministic consequence: for a fixed completed pilot and any
choice of one final binary path at each cycle length, the summed cubic Taylor
remainder tends to zero. -/
theorem mixedExactCycleTaylorRemainder_tendsto_zero
    {q : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q)
    (finalPath : ∀ r : ℕ, MixedTwoStageFinalPath (3 * r))
    (hInterior : QubitOracle.blochNormSq theta < 1) :
    Tendsto
      (fun r : ℕ => mixedExactCycleTaylorRemainder
        theta h selected pilot (finalPath r))
      atTop (nhds 0) := by
  have hbound : ∀ᶠ r : ℕ in atTop,
      |mixedExactCycleTaylorRemainder
        theta h selected pilot (finalPath r)| ≤
      mixedExactCycleCubicRemainderBound theta h r := by
    filter_upwards
      [eventually_ge_atTop (1 : ℕ),
        mixedExactCycleNormalizedEnvelope_eventually_le_half theta h]
      with r hr hsmall
    exact mixedExactCycleTaylorRemainder_abs_le_cubicBound
      theta h selected pilot (finalPath r) hInterior hr hsmall
  have habs : Tendsto
      (fun r : ℕ =>
        |mixedExactCycleTaylorRemainder
          theta h selected pilot (finalPath r)|)
      atTop (nhds 0) :=
    squeeze_zero'
      (Eventually.of_forall fun r => abs_nonneg
        (mixedExactCycleTaylorRemainder
          theta h selected pilot (finalPath r)))
      hbound
      (mixedExactCycleCubicRemainderBound_tendsto_zero theta h)
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 habs

end

end QubitOracle.Paper
