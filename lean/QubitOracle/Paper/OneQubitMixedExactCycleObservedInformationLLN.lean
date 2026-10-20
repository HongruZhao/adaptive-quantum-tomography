import QubitOracle.Paper.OneQubitMixedExactCycleTaylorRemainder
import QubitOracle.Paper.OneQubitMixedTwoStageFiniteScore

/-!
# Exact-cycle observed-information law for the mixed qubit

This module keeps the completed pilot and its selected final frame fixed.  On
the varying finite final-path space of horizon `N = 3 * r`, it computes the
conditional mean of the observed directional quadratic score, expands its
centered second moment using the explicit product mass, and proves a direct
Chebyshev bound.  Distinct centered squared-score coordinates have exactly
zero cross moment under the finite product, so no general law of large
numbers is invoked.

The resulting envelope depends only on the interior truth and direction, not
on the pilot path or selected orthonormal frame.  This proves a uniform
fixed-pilot conditional convergence statement while making no claim about
pilot randomness, information-target convergence, or a score CLT.
-/

open scoped BigOperators

namespace QubitOracle.Paper

open Filter Set

noncomputable section

/-- Conditional mean contribution of one normalized squared directional
score at final time `t`. -/
def mixedExactCycleOneShotNormalizedDirectionalFisher
    {q r : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) (t : Fin (3 * r)) : ℝ :=
  (QubitOracle.blochDot h
      (mixedTwoStageFinalAxis selected pilot t) ^ 2 /
    (1 - QubitOracle.blochDot theta
      (mixedTwoStageFinalAxis selected pilot t) ^ 2)) /
    ((3 * r : ℕ) : ℝ)

/-- Normalized directional Fisher information of the complete exact-cycle
row, conditional on the completed pilot. -/
def mixedExactCycleNormalizedDirectionalFisher
    {q r : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) : ℝ :=
  ∑ t : Fin (3 * r),
    mixedExactCycleOneShotNormalizedDirectionalFisher
      theta h selected pilot t

/-- Explicit conditional expectation of the observed quadratic term under
the finite final product mass. -/
def mixedExactCycleObservedQuadraticConditionalExpectation
    {q r : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) : ℝ :=
  ∑ finalPath : MixedTwoStageFinalPath (3 * r),
    mixedTwoStageConditionalFinalPathMass
        theta selected pilot finalPath *
      mixedExactCycleObservedQuadraticTerm
        theta h selected pilot finalPath

/-- Centered normalized squared score as a function of one Boolean outcome. -/
def mixedExactCycleCenteredSquareOutcome
    {q r : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) (t : Fin (3 * r))
    (outcome : Bool) : ℝ :=
  (mixedTwoStageFinalShotDirectionalScore
      theta h selected pilot t outcome /
      Real.sqrt (3 * r : ℕ)) ^ 2 -
    mixedExactCycleOneShotNormalizedDirectionalFisher
      theta h selected pilot t

/-- Centered normalized squared score evaluated on a complete final path. -/
def mixedExactCycleCenteredObservedSquare
    {q r : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) (t : Fin (3 * r))
    (finalPath : MixedTwoStageFinalPath (3 * r)) : ℝ :=
  mixedExactCycleNormalizedDirectionalScore
      theta h selected pilot t finalPath ^ 2 -
    mixedExactCycleOneShotNormalizedDirectionalFisher
      theta h selected pilot t

/-- Conditional centered second moment of the full observed quadratic term. -/
def mixedExactCycleObservedQuadraticConditionalSecondMoment
    {q r : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) : ℝ :=
  ∑ finalPath : MixedTwoStageFinalPath (3 * r),
    mixedTwoStageConditionalFinalPathMass
        theta selected pilot finalPath *
        (mixedExactCycleObservedQuadraticTerm
            theta h selected pilot finalPath -
          mixedExactCycleObservedQuadraticConditionalExpectation
            (r := r) theta h selected pilot) ^ 2

/-- Pilot-independent numerator in the conditional variance bound. -/
def mixedExactCycleObservedInformationVarianceConstant
    (theta h : Fin 3 -> ℝ) : ℝ :=
  4 * mixedProjectedScoreEnvelope theta h ^ 4

/-- Explicit conditional probability of a deviation of at least `epsilon`. -/
def mixedExactCycleConditionalDeviationProbability
    {q r : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) (epsilon : ℝ) : ℝ :=
  mixedTwoStageConditionalFinalEventMass (T := 3 * r) theta selected pilot
    {finalPath : MixedTwoStageFinalPath (3 * r) |
      epsilon ≤
        |mixedExactCycleObservedQuadraticTerm
              theta h selected pilot finalPath -
            mixedExactCycleObservedQuadraticConditionalExpectation
              (r := r) theta h selected pilot|}

/-- Pilot-independent Chebyshev envelope for one exact-cycle row. -/
def mixedExactCycleConditionalChebyshevBound
    (theta h : Fin 3 -> ℝ) (epsilon : ℝ) (r : ℕ) : ℝ :=
  (mixedExactCycleObservedInformationVarianceConstant theta h /
      epsilon ^ 2) * (((3 * r : ℕ) : ℝ)⁻¹)

/-- Uniform conditional convergence on the varying finite row spaces.  The
same cutoff works for every pilot length, completed pilot path, and selected
orthonormal final frame. -/
def MixedExactCycleUniformPilotConditionalConvergenceInProbability
    (theta h : Fin 3 -> ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon ->
    ∀ delta : ℝ, 0 < delta ->
      ∃ R : ℕ, ∀ r : ℕ, R ≤ r ->
        ∀ (q : ℕ) (selected : PilotSelectedFinalFrame q)
            (pilot : PauliPilotPath q),
            mixedExactCycleConditionalDeviationProbability
              (r := r) theta h selected pilot epsilon ≤ delta

/-! ## Exact conditional expectation -/

/-- One normalized squared score has exactly its displayed one-shot Fisher
expectation under the two-point Born law. -/
theorem mixedExactCycleFinalShotNormalizedSquare_bornExpectation_eq_fisher
    {q r : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) (t : Fin (3 * r))
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hr : 0 < r) :
    (∑ outcome : Bool,
      mixedTwoStageFinalBornProbability
          theta selected pilot t outcome *
        (mixedTwoStageFinalShotDirectionalScore
            theta h selected pilot t outcome /
          Real.sqrt (3 * r : ℕ)) ^ 2) =
      mixedExactCycleOneShotNormalizedDirectionalFisher
        theta h selected pilot t := by
  have hN : 0 < 3 * r := Nat.mul_pos (by norm_num) hr
  have hsqrt : 0 < Real.sqrt (3 * r : ℕ) := by
    exact Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hscale : ∀ a : ℝ,
      (a / Real.sqrt (3 * r : ℕ)) ^ 2 =
        a ^ 2 / ((3 * r : ℕ) : ℝ) := by
    intro a
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  calc
    (∑ outcome : Bool,
      mixedTwoStageFinalBornProbability
          theta selected pilot t outcome *
        (mixedTwoStageFinalShotDirectionalScore
            theta h selected pilot t outcome /
          Real.sqrt (3 * r : ℕ)) ^ 2) =
        ∑ outcome : Bool,
          (mixedTwoStageFinalBornProbability
              theta selected pilot t outcome *
            mixedTwoStageFinalShotDirectionalScore
              theta h selected pilot t outcome ^ 2) /
            ((3 * r : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro outcome _houtcome
      rw [hscale]
      ring
    _ = (∑ outcome : Bool,
          mixedTwoStageFinalBornProbability
              theta selected pilot t outcome *
            mixedTwoStageFinalShotDirectionalScore
              theta h selected pilot t outcome ^ 2) /
          ((3 * r : ℕ) : ℝ) := by
      rw [Finset.sum_div]
    _ = mixedExactCycleOneShotNormalizedDirectionalFisher
        theta h selected pilot t := by
      rw [mixedTwoStageFinalShotDirectionalScore_bornSquare
        theta h selected hInterior pilot t]
      rfl

/-- The same one-shot expectation lifted through the complete conditional
finite product. -/
theorem mixedExactCycleConditionalOneShotNormalizedSquareExpectation_eq_fisher
    {q r : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) (t : Fin (3 * r))
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hr : 0 < r) :
    (∑ finalPath : MixedTwoStageFinalPath (3 * r),
      mixedTwoStageConditionalFinalPathMass
          theta selected pilot finalPath *
        mixedExactCycleNormalizedDirectionalScore
          theta h selected pilot t finalPath ^ 2) =
      mixedExactCycleOneShotNormalizedDirectionalFisher
        theta h selected pilot t := by
  calc
    (∑ finalPath : MixedTwoStageFinalPath (3 * r),
      mixedTwoStageConditionalFinalPathMass
          theta selected pilot finalPath *
        mixedExactCycleNormalizedDirectionalScore
          theta h selected pilot t finalPath ^ 2) =
        ∑ outcome : Bool,
          mixedTwoStageFinalBornProbability
              theta selected pilot t outcome *
            (mixedTwoStageFinalShotDirectionalScore
                theta h selected pilot t outcome /
              Real.sqrt (3 * r : ℕ)) ^ 2 := by
      simpa [mixedExactCycleNormalizedDirectionalScore,
        mixedTwoStageFinalPathDirectionalScore] using
        (mixedTwoStageConditionalFinal_singleShotExpectation
          theta selected pilot t
          (fun outcome =>
            (mixedTwoStageFinalShotDirectionalScore
                theta h selected pilot t outcome /
              Real.sqrt (3 * r : ℕ)) ^ 2))
    _ = mixedExactCycleOneShotNormalizedDirectionalFisher
        theta h selected pilot t :=
      mixedExactCycleFinalShotNormalizedSquare_bornExpectation_eq_fisher
        theta h selected pilot t hInterior hr

/-- Item 1 and item 2: the explicit conditional expectation of the observed
quadratic term is exactly the normalized exact-cycle directional Fisher
information. -/
theorem mixedExactCycleObservedQuadraticConditionalExpectation_eq_fisher
    {q r : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hr : 0 < r) :
      mixedExactCycleObservedQuadraticConditionalExpectation
          (r := r) theta h selected pilot =
        mixedExactCycleNormalizedDirectionalFisher
          (r := r) theta h selected pilot := by
  unfold mixedExactCycleObservedQuadraticConditionalExpectation
    mixedExactCycleObservedQuadraticTerm
    mixedExactCycleNormalizedDirectionalFisher
  calc
    (∑ finalPath : MixedTwoStageFinalPath (3 * r),
      mixedTwoStageConditionalFinalPathMass
          theta selected pilot finalPath *
        ∑ t : Fin (3 * r),
          mixedExactCycleNormalizedDirectionalScore
            theta h selected pilot t finalPath ^ 2) =
        ∑ finalPath : MixedTwoStageFinalPath (3 * r),
          ∑ t : Fin (3 * r),
            mixedTwoStageConditionalFinalPathMass
                theta selected pilot finalPath *
              mixedExactCycleNormalizedDirectionalScore
                theta h selected pilot t finalPath ^ 2 := by
      apply Finset.sum_congr rfl
      intro finalPath _hpath
      rw [Finset.mul_sum]
    _ = ∑ t : Fin (3 * r),
        ∑ finalPath : MixedTwoStageFinalPath (3 * r),
          mixedTwoStageConditionalFinalPathMass
              theta selected pilot finalPath *
            mixedExactCycleNormalizedDirectionalScore
              theta h selected pilot t finalPath ^ 2 := by
      rw [Finset.sum_comm]
    _ = ∑ t : Fin (3 * r),
        mixedExactCycleOneShotNormalizedDirectionalFisher
          theta h selected pilot t := by
      apply Finset.sum_congr rfl
      intro t _ht
      exact
        mixedExactCycleConditionalOneShotNormalizedSquareExpectation_eq_fisher
          theta h selected pilot t hInterior hr

/-! ## Centering and product cross moments -/

/-- Each one-shot centered squared score has exact Born mean zero. -/
theorem mixedExactCycleCenteredSquareOutcome_bornMean_zero
    {q r : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) (t : Fin (3 * r))
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hr : 0 < r) :
    (∑ outcome : Bool,
      mixedTwoStageFinalBornProbability
          theta selected pilot t outcome *
        mixedExactCycleCenteredSquareOutcome
          theta h selected pilot t outcome) = 0 := by
  unfold mixedExactCycleCenteredSquareOutcome
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul,
    mixedExactCycleFinalShotNormalizedSquare_bornExpectation_eq_fisher
      theta h selected pilot t hInterior hr,
    mixedTwoStageFinalBornProbability_sum_one]
  ring

/-- The centered full observed quadratic is the sum of its one-coordinate
centered squared scores. -/
theorem mixedExactCycleObservedQuadratic_sub_expectation_eq_sum_centered
    {q r : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q)
    (finalPath : MixedTwoStageFinalPath (3 * r))
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hr : 0 < r) :
      mixedExactCycleObservedQuadraticTerm
          theta h selected pilot finalPath -
        mixedExactCycleObservedQuadraticConditionalExpectation
          (r := r) theta h selected pilot =
      ∑ t : Fin (3 * r),
        mixedExactCycleCenteredObservedSquare
          theta h selected pilot t finalPath := by
  rw [mixedExactCycleObservedQuadraticConditionalExpectation_eq_fisher
    theta h selected pilot hInterior hr]
  unfold mixedExactCycleObservedQuadraticTerm
    mixedExactCycleNormalizedDirectionalFisher
    mixedExactCycleCenteredObservedSquare
  rw [Finset.sum_sub_distrib]

private def mixedExactCycleDoubleCenteredFactor
    {q r : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q)
    (s t current : Fin (3 * r)) (outcome : Bool) : ℝ :=
  mixedTwoStageFinalBornProbability
      theta selected pilot current outcome *
      (if current = s then
        mixedExactCycleCenteredSquareOutcome
          theta h selected pilot s outcome
      else 1) *
    (if current = t then
      mixedExactCycleCenteredSquareOutcome
        theta h selected pilot t outcome
    else 1)

private theorem mixedExactCycleDoubleCenteredFactor_prod
    {q r : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q)
    (s t : Fin (3 * r))
    (finalPath : MixedTwoStageFinalPath (3 * r)) :
    (∏ current : Fin (3 * r),
      mixedExactCycleDoubleCenteredFactor
        theta h selected pilot s t current (finalPath current)) =
      mixedTwoStageConditionalFinalPathMass
          theta selected pilot finalPath *
        (mixedExactCycleCenteredObservedSquare
            theta h selected pilot s finalPath *
          mixedExactCycleCenteredObservedSquare
            theta h selected pilot t finalPath) := by
  have hs :
      (∏ current : Fin (3 * r),
        if current = s then
          mixedExactCycleCenteredSquareOutcome
            theta h selected pilot s (finalPath current)
        else 1) =
        mixedExactCycleCenteredObservedSquare
          theta h selected pilot s finalPath := by
    rw [Finset.prod_eq_single s]
    · simp [mixedExactCycleCenteredObservedSquare,
        mixedExactCycleCenteredSquareOutcome,
        mixedExactCycleNormalizedDirectionalScore,
        mixedTwoStageFinalPathDirectionalScore]
    · intro current _hcurrent hne
      simp [hne]
    · simp
  have ht :
      (∏ current : Fin (3 * r),
        if current = t then
          mixedExactCycleCenteredSquareOutcome
            theta h selected pilot t (finalPath current)
        else 1) =
        mixedExactCycleCenteredObservedSquare
          theta h selected pilot t finalPath := by
    rw [Finset.prod_eq_single t]
    · simp [mixedExactCycleCenteredObservedSquare,
        mixedExactCycleCenteredSquareOutcome,
        mixedExactCycleNormalizedDirectionalScore,
        mixedTwoStageFinalPathDirectionalScore]
    · intro current _hcurrent hne
      simp [hne]
    · simp
  unfold mixedExactCycleDoubleCenteredFactor
    mixedTwoStageConditionalFinalPathMass
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, hs, ht]
  ring

/-- Distinct centered squared-score coordinates have exactly zero
conditional cross moment under the explicit finite product. -/
theorem mixedExactCycleCenteredObservedSquare_cross_zero
    {q r : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q)
    (s t : Fin (3 * r)) (hst : s ≠ t)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hr : 0 < r) :
    (∑ finalPath : MixedTwoStageFinalPath (3 * r),
      mixedTwoStageConditionalFinalPathMass
          theta selected pilot finalPath *
        (mixedExactCycleCenteredObservedSquare
            theta h selected pilot s finalPath *
          mixedExactCycleCenteredObservedSquare
            theta h selected pilot t finalPath)) = 0 := by
  calc
    (∑ finalPath : MixedTwoStageFinalPath (3 * r),
      mixedTwoStageConditionalFinalPathMass
          theta selected pilot finalPath *
        (mixedExactCycleCenteredObservedSquare
            theta h selected pilot s finalPath *
          mixedExactCycleCenteredObservedSquare
            theta h selected pilot t finalPath)) =
        ∑ finalPath : MixedTwoStageFinalPath (3 * r),
          ∏ current : Fin (3 * r),
            mixedExactCycleDoubleCenteredFactor
              theta h selected pilot s t current (finalPath current) := by
      apply Finset.sum_congr rfl
      intro finalPath _hpath
      exact (mixedExactCycleDoubleCenteredFactor_prod
        theta h selected pilot s t finalPath).symm
    _ = ∏ current : Fin (3 * r),
        ∑ outcome : Bool,
          mixedExactCycleDoubleCenteredFactor
            theta h selected pilot s t current outcome := by
      have hprod :=
        Finset.sum_prod_piFinset (Finset.univ : Finset Bool)
          (fun current outcome =>
            mixedExactCycleDoubleCenteredFactor
              theta h selected pilot s t current outcome)
      rw [Fintype.piFinset_univ] at hprod
      simpa using hprod
    _ = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ s) (by
        simpa [mixedExactCycleDoubleCenteredFactor, hst] using
          (mixedExactCycleCenteredSquareOutcome_bornMean_zero
            theta h selected pilot s hInterior hr))

/-! ## Pilot-independent diagonal and total second-moment bounds -/

theorem mixedExactCycleProjectedScoreEnvelope_nonnegative
    (theta h : Fin 3 -> ℝ)
    (hInterior : QubitOracle.blochNormSq theta < 1) :
    0 ≤ mixedProjectedScoreEnvelope theta h := by
  unfold mixedProjectedScoreEnvelope mixedProjectionL1
  exact mul_nonneg
    (Finset.sum_nonneg (fun i _hi => abs_nonneg (h i)))
    (inv_nonneg.mpr
      (le_of_lt (mixedInteriorGap_pos theta hInterior)))

/-- Every one-shot normalized Fisher term lies between zero and the square
of the common normalized score envelope. -/
theorem mixedExactCycleOneShotNormalizedDirectionalFisher_bounds
    {q r : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) (t : Fin (3 * r))
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hr : 0 < r) :
    0 ≤ mixedExactCycleOneShotNormalizedDirectionalFisher
        theta h selected pilot t ∧
    mixedExactCycleOneShotNormalizedDirectionalFisher
        theta h selected pilot t ≤
      (mixedProjectedScoreEnvelope theta h /
        Real.sqrt (3 * r : ℕ)) ^ 2 := by
  have hphysical : PauliPilotPhysicalBloch theta := by
    exact le_of_lt hInterior
  have hmean :=
    mixedExactCycleConditionalOneShotNormalizedSquareExpectation_eq_fisher
      theta h selected pilot t hInterior hr
  constructor
  · calc
      0 ≤ ∑ finalPath : MixedTwoStageFinalPath (3 * r),
          mixedTwoStageConditionalFinalPathMass
              theta selected pilot finalPath *
            mixedExactCycleNormalizedDirectionalScore
              theta h selected pilot t finalPath ^ 2 := by
        exact Finset.sum_nonneg fun finalPath _hpath =>
          mul_nonneg
            (mixedTwoStageConditionalFinalPathMass_nonnegative
              theta selected hphysical pilot finalPath)
            (sq_nonneg _)
      _ = mixedExactCycleOneShotNormalizedDirectionalFisher
          theta h selected pilot t := hmean
  · calc
      mixedExactCycleOneShotNormalizedDirectionalFisher
          theta h selected pilot t =
          ∑ finalPath : MixedTwoStageFinalPath (3 * r),
            mixedTwoStageConditionalFinalPathMass
                theta selected pilot finalPath *
              mixedExactCycleNormalizedDirectionalScore
                theta h selected pilot t finalPath ^ 2 := hmean.symm
      _ ≤ ∑ finalPath : MixedTwoStageFinalPath (3 * r),
          mixedTwoStageConditionalFinalPathMass
              theta selected pilot finalPath *
            (mixedProjectedScoreEnvelope theta h /
              Real.sqrt (3 * r : ℕ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro finalPath _hpath
        have hx :=
          mixedExactCycleNormalizedDirectionalScore_abs_le_envelope
            theta h selected pilot finalPath t hInterior hr
        have hxSq :=
          pow_le_pow_left₀ (abs_nonneg _) hx 2
        have hmass :=
          mixedTwoStageConditionalFinalPathMass_nonnegative
            theta selected hphysical pilot finalPath
        exact mul_le_mul_of_nonneg_left
          (by simpa [sq_abs] using hxSq) hmass
      _ = (mixedProjectedScoreEnvelope theta h /
          Real.sqrt (3 * r : ℕ)) ^ 2 := by
        rw [← Finset.sum_mul,
          mixedTwoStageConditionalFinalPathMass_sum_one]
        simp

/-- Pointwise centered-square envelope. -/
theorem mixedExactCycleCenteredObservedSquare_abs_le
    {q r : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) (t : Fin (3 * r))
    (finalPath : MixedTwoStageFinalPath (3 * r))
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hr : 0 < r) :
    |mixedExactCycleCenteredObservedSquare
        theta h selected pilot t finalPath| ≤
      2 * (mixedProjectedScoreEnvelope theta h /
        Real.sqrt (3 * r : ℕ)) ^ 2 := by
  have hx := mixedExactCycleNormalizedDirectionalScore_abs_le_envelope
    theta h selected pilot finalPath t hInterior hr
  have hxSq := pow_le_pow_left₀ (abs_nonneg _) hx 2
  have hm := mixedExactCycleOneShotNormalizedDirectionalFisher_bounds
    theta h selected pilot t hInterior hr
  unfold mixedExactCycleCenteredObservedSquare
  calc
    |mixedExactCycleNormalizedDirectionalScore
          theta h selected pilot t finalPath ^ 2 -
        mixedExactCycleOneShotNormalizedDirectionalFisher
          theta h selected pilot t| ≤
        |mixedExactCycleNormalizedDirectionalScore
          theta h selected pilot t finalPath ^ 2| +
        |mixedExactCycleOneShotNormalizedDirectionalFisher
          theta h selected pilot t| := abs_sub _ _
    _ = mixedExactCycleNormalizedDirectionalScore
          theta h selected pilot t finalPath ^ 2 +
        mixedExactCycleOneShotNormalizedDirectionalFisher
          theta h selected pilot t := by
      rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg hm.1]
    _ ≤ (mixedProjectedScoreEnvelope theta h /
          Real.sqrt (3 * r : ℕ)) ^ 2 +
        (mixedProjectedScoreEnvelope theta h /
          Real.sqrt (3 * r : ℕ)) ^ 2 := by
      exact add_le_add (by simpa [sq_abs] using hxSq) hm.2
    _ = 2 * (mixedProjectedScoreEnvelope theta h /
        Real.sqrt (3 * r : ℕ)) ^ 2 := by ring

/-- Uniform diagonal second-moment bound for one centered squared-score
coordinate. -/
theorem mixedExactCycleCenteredObservedSquare_secondMoment_le
    {q r : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) (t : Fin (3 * r))
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hr : 0 < r) :
    (∑ finalPath : MixedTwoStageFinalPath (3 * r),
      mixedTwoStageConditionalFinalPathMass
          theta selected pilot finalPath *
        mixedExactCycleCenteredObservedSquare
          theta h selected pilot t finalPath ^ 2) ≤
      4 * (mixedProjectedScoreEnvelope theta h /
        Real.sqrt (3 * r : ℕ)) ^ 4 := by
  have hphysical : PauliPilotPhysicalBloch theta := by
    exact le_of_lt hInterior
  calc
    (∑ finalPath : MixedTwoStageFinalPath (3 * r),
      mixedTwoStageConditionalFinalPathMass
          theta selected pilot finalPath *
        mixedExactCycleCenteredObservedSquare
          theta h selected pilot t finalPath ^ 2) ≤
        ∑ finalPath : MixedTwoStageFinalPath (3 * r),
          mixedTwoStageConditionalFinalPathMass
              theta selected pilot finalPath *
            (2 * (mixedProjectedScoreEnvelope theta h /
              Real.sqrt (3 * r : ℕ)) ^ 2) ^ 2 := by
      apply Finset.sum_le_sum
      intro finalPath _hpath
      have hz := mixedExactCycleCenteredObservedSquare_abs_le
        theta h selected pilot t finalPath hInterior hr
      have hzSq := pow_le_pow_left₀ (abs_nonneg _) hz 2
      have hmass := mixedTwoStageConditionalFinalPathMass_nonnegative
        theta selected hphysical pilot finalPath
      exact mul_le_mul_of_nonneg_left
        (by simpa [sq_abs] using hzSq) hmass
    _ = 4 * (mixedProjectedScoreEnvelope theta h /
        Real.sqrt (3 * r : ℕ)) ^ 4 := by
      rw [← Finset.sum_mul,
        mixedTwoStageConditionalFinalPathMass_sum_one]
      ring

/-- Exact arithmetic used to convert `N / (sqrt N)^4` into `1 / N`. -/
theorem mixedExactCycle_count_div_sqrt_fourth
    (r : ℕ) (hr : 0 < r) :
    ((3 * r : ℕ) : ℝ) /
        Real.sqrt (3 * r : ℕ) ^ 4 =
      1 / ((3 * r : ℕ) : ℝ) := by
  let s : ℝ := Real.sqrt (3 * r : ℕ)
  have hN : 0 < 3 * r := Nat.mul_pos (by norm_num) hr
  have hs : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hsq : s ^ 2 = ((3 * r : ℕ) : ℝ) := by
    dsimp [s]
    exact Real.sq_sqrt (Nat.cast_nonneg _)
  change ((3 * r : ℕ) : ℝ) / s ^ 4 =
    1 / ((3 * r : ℕ) : ℝ)
  calc
    ((3 * r : ℕ) : ℝ) / s ^ 4 = s ^ 2 / s ^ 4 := by rw [hsq]
    _ = 1 / s ^ 2 := by
      field_simp [ne_of_gt hs]
      <;> ring
    _ = 1 / ((3 * r : ℕ) : ℝ) := by rw [hsq]

/-- Item 3: the conditional centered second moment is bounded by
`C(theta,h) / (3*r)`, uniformly in the completed pilot and selected frame. -/
theorem mixedExactCycleObservedQuadraticConditionalSecondMoment_le
    {q r : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hr : 0 < r) :
      mixedExactCycleObservedQuadraticConditionalSecondMoment
          (r := r) theta h selected pilot ≤
      mixedExactCycleObservedInformationVarianceConstant theta h /
        ((3 * r : ℕ) : ℝ) := by
  unfold mixedExactCycleObservedQuadraticConditionalSecondMoment
  calc
    (∑ finalPath : MixedTwoStageFinalPath (3 * r),
      mixedTwoStageConditionalFinalPathMass
          theta selected pilot finalPath *
          (mixedExactCycleObservedQuadraticTerm
              theta h selected pilot finalPath -
            mixedExactCycleObservedQuadraticConditionalExpectation
              (r := r) theta h selected pilot) ^ 2) =
        ∑ finalPath : MixedTwoStageFinalPath (3 * r),
          ∑ s : Fin (3 * r), ∑ t : Fin (3 * r),
            mixedTwoStageConditionalFinalPathMass
                theta selected pilot finalPath *
              (mixedExactCycleCenteredObservedSquare
                  theta h selected pilot s finalPath *
                mixedExactCycleCenteredObservedSquare
                  theta h selected pilot t finalPath) := by
      apply Finset.sum_congr rfl
      intro finalPath _hpath
      rw [mixedExactCycleObservedQuadratic_sub_expectation_eq_sum_centered
        theta h selected pilot finalPath hInterior hr]
      rw [pow_two, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    _ = ∑ s : Fin (3 * r),
        ∑ finalPath : MixedTwoStageFinalPath (3 * r),
          ∑ t : Fin (3 * r),
            mixedTwoStageConditionalFinalPathMass
                theta selected pilot finalPath *
              (mixedExactCycleCenteredObservedSquare
                  theta h selected pilot s finalPath *
                mixedExactCycleCenteredObservedSquare
                  theta h selected pilot t finalPath) := by
      rw [Finset.sum_comm]
    _ = ∑ s : Fin (3 * r), ∑ t : Fin (3 * r),
        ∑ finalPath : MixedTwoStageFinalPath (3 * r),
          mixedTwoStageConditionalFinalPathMass
              theta selected pilot finalPath *
            (mixedExactCycleCenteredObservedSquare
                theta h selected pilot s finalPath *
              mixedExactCycleCenteredObservedSquare
                theta h selected pilot t finalPath) := by
      apply Finset.sum_congr rfl
      intro s _hs
      rw [Finset.sum_comm]
    _ = ∑ s : Fin (3 * r), ∑ t : Fin (3 * r),
        if s = t then
          ∑ finalPath : MixedTwoStageFinalPath (3 * r),
            mixedTwoStageConditionalFinalPathMass
                theta selected pilot finalPath *
              mixedExactCycleCenteredObservedSquare
                theta h selected pilot s finalPath ^ 2
        else 0 := by
      apply Finset.sum_congr rfl
      intro s _hs
      apply Finset.sum_congr rfl
      intro t _ht
      by_cases hst : s = t
      · subst t
        simp only [if_pos]
        simp [pow_two]
      · rw [if_neg hst]
        exact mixedExactCycleCenteredObservedSquare_cross_zero
          theta h selected pilot s t hst hInterior hr
    _ = ∑ s : Fin (3 * r),
        ∑ finalPath : MixedTwoStageFinalPath (3 * r),
          mixedTwoStageConditionalFinalPathMass
              theta selected pilot finalPath *
            mixedExactCycleCenteredObservedSquare
              theta h selected pilot s finalPath ^ 2 := by
      simp
    _ ≤ ∑ _s : Fin (3 * r),
        4 * (mixedProjectedScoreEnvelope theta h /
          Real.sqrt (3 * r : ℕ)) ^ 4 := by
      apply Finset.sum_le_sum
      intro s _hs
      exact mixedExactCycleCenteredObservedSquare_secondMoment_le
        theta h selected pilot s hInterior hr
    _ = ((3 * r : ℕ) : ℝ) * 4 *
        (mixedProjectedScoreEnvelope theta h /
          Real.sqrt (3 * r : ℕ)) ^ 4 := by
      simp
      ring
    _ = mixedExactCycleObservedInformationVarianceConstant theta h /
        ((3 * r : ℕ) : ℝ) := by
      unfold mixedExactCycleObservedInformationVarianceConstant
      rw [show
        ((3 * r : ℕ) : ℝ) * 4 *
            (mixedProjectedScoreEnvelope theta h /
              Real.sqrt (3 * r : ℕ)) ^ 4 =
          4 * mixedProjectedScoreEnvelope theta h ^ 4 *
            (((3 * r : ℕ) : ℝ) /
              Real.sqrt (3 * r : ℕ) ^ 4) by ring]
      rw [mixedExactCycle_count_div_sqrt_fourth r hr]
      ring

/-! ## Explicit finite-row Chebyshev bounds and uniform convergence -/

theorem mixedExactCycleConditionalDeviationProbability_nonnegative
    {q r : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) (epsilon : ℝ)
    (hInterior : QubitOracle.blochNormSq theta < 1) :
      0 ≤ mixedExactCycleConditionalDeviationProbability
        (r := r) theta h selected pilot epsilon := by
  have hphysical : PauliPilotPhysicalBloch theta := by
    exact le_of_lt hInterior
  unfold mixedExactCycleConditionalDeviationProbability
    mixedTwoStageConditionalFinalEventMass
  exact Finset.sum_nonneg fun finalPath _hpath => by
    by_cases hdev : epsilon ≤
          |mixedExactCycleObservedQuadraticTerm
              theta h selected pilot finalPath -
            mixedExactCycleObservedQuadraticConditionalExpectation
              (r := r) theta h selected pilot|
    · simp [hdev,
        mixedTwoStageConditionalFinalPathMass_nonnegative
          theta selected hphysical pilot finalPath]
    · simp [hdev]

/-- Item 4: direct finite-sum Chebyshev inequality on one varying row. -/
theorem mixedExactCycleConditionalDeviationProbability_le_secondMoment
    {q r : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) (epsilon : ℝ)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hepsilon : 0 < epsilon) :
      mixedExactCycleConditionalDeviationProbability
          (r := r) theta h selected pilot epsilon ≤
        mixedExactCycleObservedQuadraticConditionalSecondMoment
          (r := r) theta h selected pilot / epsilon ^ 2 := by
  have hphysical : PauliPilotPhysicalBloch theta := by
    exact le_of_lt hInterior
  apply (le_div_iff₀ (pow_pos hepsilon 2)).2
  unfold mixedExactCycleConditionalDeviationProbability
    mixedTwoStageConditionalFinalEventMass
    mixedExactCycleObservedQuadraticConditionalSecondMoment
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro finalPath _hpath
  let deviation : ℝ :=
      mixedExactCycleObservedQuadraticTerm
          theta h selected pilot finalPath -
        mixedExactCycleObservedQuadraticConditionalExpectation
          (r := r) theta h selected pilot
  have hmass := mixedTwoStageConditionalFinalPathMass_nonnegative
    theta selected hphysical pilot finalPath
  by_cases hdev : epsilon ≤ |deviation|
  · have hsq : epsilon ^ 2 ≤ deviation ^ 2 := by
      have hp := pow_le_pow_left₀ hepsilon.le hdev 2
      simpa [sq_abs] using hp
    simpa [deviation, hdev] using
      (mul_le_mul_of_nonneg_left hsq hmass)
  · simp [deviation, hdev, mul_nonneg hmass (sq_nonneg deviation)]

/-- Row-specific probability bound with a pilot-independent numerator. -/
theorem mixedExactCycleConditionalDeviationProbability_le_chebyshevBound
    {q r : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) (epsilon : ℝ)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hepsilon : 0 < epsilon)
    (hr : 0 < r) :
      mixedExactCycleConditionalDeviationProbability
          (r := r) theta h selected pilot epsilon ≤
      mixedExactCycleConditionalChebyshevBound theta h epsilon r := by
  calc
      mixedExactCycleConditionalDeviationProbability
          (r := r) theta h selected pilot epsilon ≤
          mixedExactCycleObservedQuadraticConditionalSecondMoment
            (r := r) theta h selected pilot / epsilon ^ 2 :=
      mixedExactCycleConditionalDeviationProbability_le_secondMoment
        theta h selected pilot epsilon hInterior hepsilon
    _ ≤ (mixedExactCycleObservedInformationVarianceConstant theta h /
          ((3 * r : ℕ) : ℝ)) / epsilon ^ 2 := by
      gcongr
      exact mixedExactCycleObservedQuadraticConditionalSecondMoment_le
        theta h selected pilot hInterior hr
    _ = mixedExactCycleConditionalChebyshevBound
        theta h epsilon r := by
      unfold mixedExactCycleConditionalChebyshevBound
      ring

theorem mixedExactCycleConditionalChebyshevBound_tendsto_zero
    (theta h : Fin 3 -> ℝ) (epsilon : ℝ) :
    Tendsto (mixedExactCycleConditionalChebyshevBound theta h epsilon)
      atTop (nhds 0) := by
  have hcast :
      Tendsto (fun r : ℕ => (3 : ℝ) * (r : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hinv :
      Tendsto (fun r : ℕ => (((3 * r : ℕ) : ℝ)⁻¹))
        atTop (nhds 0) := by
      simpa only [Function.comp_def, Nat.cast_mul, Nat.cast_ofNat] using
        (tendsto_inv_atTop_zero.comp hcast)
  have hconst : Tendsto
      (fun _r : ℕ =>
        mixedExactCycleObservedInformationVarianceConstant theta h /
          epsilon ^ 2)
      atTop
      (nhds (mixedExactCycleObservedInformationVarianceConstant theta h /
        epsilon ^ 2)) := tendsto_const_nhds
  change Tendsto
    (fun r : ℕ =>
      (mixedExactCycleObservedInformationVarianceConstant theta h /
        epsilon ^ 2) * (((3 * r : ℕ) : ℝ)⁻¹))
    atTop (nhds 0)
  simpa only [mul_zero] using hconst.mul hinv

/-- Fixed-pilot convergence in probability on the explicit varying finite
sample spaces. -/
theorem mixedExactCycleObservedQuadratic_convergesInConditionalProbability
    {q : ℕ} (theta h : Fin 3 -> ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) (epsilon : ℝ)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hepsilon : 0 < epsilon) :
      Tendsto
        (fun r : ℕ => mixedExactCycleConditionalDeviationProbability
          (r := r) theta h selected pilot epsilon)
      atTop (nhds 0) := by
  have hupper : ∀ᶠ r : ℕ in atTop,
        mixedExactCycleConditionalDeviationProbability
            (r := r) theta h selected pilot epsilon ≤
        mixedExactCycleConditionalChebyshevBound theta h epsilon r := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with r hr
    exact mixedExactCycleConditionalDeviationProbability_le_chebyshevBound
      theta h selected pilot epsilon hInterior hepsilon hr
  exact squeeze_zero'
    (Eventually.of_forall fun r =>
        mixedExactCycleConditionalDeviationProbability_nonnegative
          (r := r) theta h selected pilot epsilon hInterior)
    hupper
    (mixedExactCycleConditionalChebyshevBound_tendsto_zero
      theta h epsilon)

/-- Item 5: because the score envelope is pilot- and frame-independent, one
deterministic row cutoff proves conditional convergence uniformly over all
completed pilots and all pilot-selected orthonormal frames. -/
theorem mixedExactCycleObservedQuadratic_uniformPilotConditionalConvergence
    (theta h : Fin 3 -> ℝ)
    (hInterior : QubitOracle.blochNormSq theta < 1) :
      MixedExactCycleUniformPilotConditionalConvergenceInProbability
        theta h := by
  unfold MixedExactCycleUniformPilotConditionalConvergenceInProbability
  intro epsilon hepsilon delta hdelta
  have hsmall : ∀ᶠ r : ℕ in atTop,
      mixedExactCycleConditionalChebyshevBound theta h epsilon r < delta :=
    (tendsto_order.1
      (mixedExactCycleConditionalChebyshevBound_tendsto_zero
        theta h epsilon)).2 delta hdelta
  have hboth : ∀ᶠ r : ℕ in atTop,
      0 < r ∧
        mixedExactCycleConditionalChebyshevBound
          theta h epsilon r < delta := by
    filter_upwards [eventually_ge_atTop (1 : ℕ), hsmall] with r hr hbound
    exact ⟨hr, hbound⟩
  obtain ⟨R, hR⟩ := eventually_atTop.1 hboth
  refine ⟨R, ?_⟩
  intro r hRr q selected pilot
  have hr := hR r hRr
  exact (mixedExactCycleConditionalDeviationProbability_le_chebyshevBound
      (r := r) theta h selected pilot epsilon hInterior hepsilon hr.1).trans
    hr.2.le

end

end QubitOracle.Paper
