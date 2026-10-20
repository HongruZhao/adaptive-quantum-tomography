import QubitOracle.Paper.MomentRiskTransfer

/-!
# Source-faithful martingale moment bounds

This module isolates the moment inequality used by the supplement to pass from
bounded adaptive score increments to polynomial score moments and then, under
explicit coercivity estimates, to uniform estimator-error moments.

The sole scientific axiom is the integer-moment upper-bound specialization of
P. Hall and C. C. Heyde, *Martingale Limit Theory and Its Application*,
Academic Press, 1980, Theorem 2.12, pp. 23--24.

Primary source:
https://www.stat.yale.edu/~mjk56/MartingaleLimitTheoryAndItsApplication.pdf

With one-based source increments `X_i`, the theorem states, for finite
`p >= 2`,

`E |S_n|^p <= C_p [E (sum E(X_i^2 | F_{i-1}))^(p/2)
                    + sum E |X_i|^p]`.

The Lean statement below uses zero-based increments.  Its constant is chosen
before the probability space, martingale, and terminal time, so it depends
only on `p`, exactly as in the source.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

noncomputable section

namespace SourceFaithfulMartingaleMoments

/-- Zero-based scalar martingale partial sum. -/
def scalarPartialSum {Omega : Type*}
    (increment : Nat -> Omega -> Real) (n : Nat) (omega : Omega) : Real :=
  ∑ k ∈ Finset.range n, increment k omega

/-- Predictable quadratic variation through time `n`, using conditional
second moments with respect to the preceding sigma-field. -/
def conditionalVarianceSum
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (filtration : Filtration Nat (inferInstance : MeasurableSpace Omega))
    (increment : Nat -> Omega -> Real)
    (n : Nat) (omega : Omega) : Real :=
  ∑ k ∈ Finset.range n,
    MeasureTheory.condExp (filtration k) mu
      (fun omega' => |increment k omega'| ^ 2) omega

/-- The terminal absolute `p`-moment in extended-nonnegative form. -/
def terminalAbsoluteMoment
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (increment : Nat -> Omega -> Real)
    (p n : Nat) : ENNReal :=
  ∫⁻ omega,
    (ENNReal.ofReal |scalarPartialSum increment n omega|) ^ p ∂mu

/-- The first term on the right side of Hall--Heyde Theorem 2.12. -/
def predictableQuadraticMoment
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (filtration : Filtration Nat (inferInstance : MeasurableSpace Omega))
    (increment : Nat -> Omega -> Real)
    (p n : Nat) : ENNReal :=
  ∫⁻ omega,
    (ENNReal.ofReal (conditionalVarianceSum mu filtration increment n omega)) ^
      (p / 2) ∂mu

/-- The sum of increment `p`-moments in Hall--Heyde Theorem 2.12. -/
def incrementAbsoluteMomentSum
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (increment : Nat -> Omega -> Real)
    (p n : Nat) : ENNReal :=
  ∑ k ∈ Finset.range n,
    ∫⁻ omega, (ENNReal.ofReal |increment k omega|) ^ p ∂mu

/-- **Scientific axiom: Hall--Heyde (1980), Theorem 2.12, upper bound.**

This is the exact finite-integer-`p` specialization needed here.  The source
allows every real `p >= 2`; restricting to integer `p` is weaker.  The
partial-sum martingale condition is the zero-based formulation of the source
martingale-difference hypothesis.  `MemLp` assumptions explicitly record the
source's finite second and `p`th moments. -/
axiom hallHeyde1980_theorem2_12_martingaleRosenthal_upper
    (p : Nat) (hp : 2 ≤ p) :
    ∃ C_p : ENNReal, 0 < C_p ∧ C_p ≠ ∞ ∧
      ∀ {Omega : Type*} [MeasurableSpace Omega]
        (mu : Measure Omega) [IsProbabilityMeasure mu]
        (filtration : Filtration Nat
          (inferInstance : MeasurableSpace Omega))
        (increment : Nat -> Omega -> Real) (n : Nat),
        Martingale (scalarPartialSum increment) filtration mu ->
        (∀ k < n, MemLp (increment k) (p : ENNReal) mu) ->
        (∀ k < n, MemLp (increment k) 2 mu) ->
        terminalAbsoluteMoment mu increment p n ≤
          C_p *
            (predictableQuadraticMoment mu filtration increment p n +
              incrementAbsoluteMomentSum mu increment p n)

/-- A polynomial fourth-moment bound of the form used in the supplement. -/
def HasPolynomialFourthMomentBound
    (moment : Nat -> ENNReal) (constant : ENNReal) : Prop :=
  ∀ n, 0 < n -> moment n ≤ constant * (n : ENNReal) ^ 2

/-- Moment-level coercivity after the usual root-sample-size normalization.
The fourth power of the inverse sample size appears because an unnormalized
score has fourth moment of order `n^2`. -/
def HasNormalizedScoreCoercivity
    (scoreFourth errorFourth : Nat -> ENNReal)
    (coercivityConstant remainderBound : ENNReal) : Prop :=
  ∀ n, 0 < n ->
    errorFourth n ≤
      coercivityConstant * ((n : ENNReal) ^ 2)⁻¹ * scoreFourth n +
        remainderBound

/-- Stability transfer between two already normalized estimator errors. -/
def HasStableFourthMomentTransfer
    (inputFourth outputFourth : Nat -> ENNReal)
    (stabilityConstant remainderBound : ENNReal) : Prop :=
  ∀ n, 0 < n ->
    outputFourth n ≤ stabilityConstant * inputFourth n + remainderBound

private theorem natCast_le_square (n : Nat) (hn : 0 < n) :
    (n : ENNReal) ≤ (n : ENNReal) ^ 2 := by
  have h1 : (1 : ENNReal) <= (n : ENNReal) := by
    exact_mod_cast hn
  calc
    (n : ENNReal) = (n : ENNReal) * 1 := (mul_one _).symm
    _ <= (n : ENNReal) * (n : ENNReal) := mul_le_mul_right h1 _
    _ = (n : ENNReal) ^ 2 := (pow_two _).symm

private theorem inv_square_mul_square_cancel
    (a : ENNReal) (n : Nat) (hn : 0 < n) :
    ((n : ENNReal) ^ 2)⁻¹ * (a * (n : ENNReal) ^ 2) = a := by
  have hn0 : (n : ENNReal) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have hntop : (n : ENNReal) ≠ ∞ := ENNReal.natCast_ne_top n
  calc
    ((n : ENNReal) ^ 2)⁻¹ * (a * (n : ENNReal) ^ 2) =
        a * ((n : ENNReal) ^ 2 * ((n : ENNReal) ^ 2)⁻¹) := by
          ac_rfl
    _ = a * 1 := by
      rw [ENNReal.mul_inv_cancel
        (pow_ne_zero 2 hn0) (ENNReal.pow_ne_top hntop)]
    _ = a := mul_one a

/-- Bounded increments are in every finite `L^p`, once the partial sums are a
martingale.  This discharges the source theorem's integrability premises
without assuming any moment conclusion. -/
theorem increment_memLp_of_martingale_uniform_bound
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration Nat (inferInstance : MeasurableSpace Omega))
    (increment : Nat -> Omega -> Real)
    (hmartingale : Martingale (scalarPartialSum increment) filtration mu)
    (B : Real)
    (hbound : ∀ k, ∀ᵐ omega ∂mu,
      norm (increment k omega) ≤ B)
    (p : ENNReal) (k : Nat) :
    MemLp (increment k) p mu := by
  have hintegrable : Integrable (increment k) mu := by
    have hdifference :=
      (hmartingale.integrable (k + 1)).sub (hmartingale.integrable k)
    convert hdifference using 1
    funext omega
    simp [scalarPartialSum, Finset.sum_range_succ]
  apply MemLp.of_bound hintegrable.aestronglyMeasurable B
  exact hbound k

/-- A uniform increment bound gives the linear jump-moment term in the
fourth-moment Rosenthal inequality. -/
theorem incrementAbsoluteFourthMomentSum_le_of_uniform_bound
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (increment : Nat -> Omega -> Real)
    (B : Real) (hB : 0 ≤ B)
    (hbound : ∀ k, ∀ᵐ omega ∂mu,
      norm (increment k omega) ≤ B)
    (n : Nat) :
    incrementAbsoluteMomentSum mu increment 4 n ≤
      (n : ENNReal) * (ENNReal.ofReal B) ^ 4 := by
  calc
    incrementAbsoluteMomentSum mu increment 4 n ≤
        ∑ _k ∈ Finset.range n, (ENNReal.ofReal B) ^ 4 := by
      apply Finset.sum_le_sum
      intro k hk
      calc
        (∫⁻ omega, (ENNReal.ofReal |increment k omega|) ^ 4 ∂mu) ≤
            ∫⁻ _omega, (ENNReal.ofReal B) ^ 4 ∂mu := by
          apply lintegral_mono_ae
          filter_upwards [hbound k] with omega homega
          have habs : |increment k omega| ≤ B := by
            simpa only [Real.norm_eq_abs] using homega
          exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal habs) 4
        _ = (ENNReal.ofReal B) ^ 4 := by simp
    _ = (n : ENNReal) * (ENNReal.ofReal B) ^ 4 := by
      simp [nsmul_eq_mul]

/-- An explicit almost-sure predictable conditional-variance bound gives the
quadratic term in Hall--Heyde's fourth-moment inequality. -/
theorem predictableQuadraticFourthMoment_le
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration Nat (inferInstance : MeasurableSpace Omega))
    (increment : Nat -> Omega -> Real)
    (V : ENNReal) (n : Nat)
    (hpredictable : ∀ᵐ omega ∂mu,
      ENNReal.ofReal (conditionalVarianceSum mu filtration increment n omega) ≤
        (n : ENNReal) * V) :
    predictableQuadraticMoment mu filtration increment 4 n ≤
      V ^ 2 * (n : ENNReal) ^ 2 := by
  calc
    predictableQuadraticMoment mu filtration increment 4 n ≤
        ∫⁻ _omega, (((n : ENNReal) * V) ^ 2) ∂mu := by
      apply lintegral_mono_ae
      filter_upwards [hpredictable] with omega homega
      exact pow_le_pow_left' homega 2
    _ = ((n : ENNReal) * V) ^ 2 := by simp
    _ = V ^ 2 * (n : ENNReal) ^ 2 := by ring

/-- Hall--Heyde plus bounded increments and predictable conditional-variance
growth yields the supplement's polynomial fourth-moment score bound. -/
theorem polynomialScoreFourthMoment_of_hallHeyde
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration Nat (inferInstance : MeasurableSpace Omega))
    (increment : Nat -> Omega -> Real)
    (hmartingale : Martingale (scalarPartialSum increment) filtration mu)
    (B : Real) (hB : 0 ≤ B)
    (hbound : ∀ k, ∀ᵐ omega ∂mu,
      norm (increment k omega) ≤ B)
    (V : ENNReal)
    (hpredictable : ∀ n, ∀ᵐ omega ∂mu,
      ENNReal.ofReal (conditionalVarianceSum mu filtration increment n omega) ≤
        (n : ENNReal) * V) :
    ∃ C_4 : ENNReal, 0 < C_4 ∧ C_4 ≠ ∞ ∧
      HasPolynomialFourthMomentBound
        (fun n => terminalAbsoluteMoment mu increment 4 n)
        (C_4 * (V ^ 2 + (ENNReal.ofReal B) ^ 4)) := by
  obtain ⟨C_4, hC4, hC4top, hsource⟩ :=
    hallHeyde1980_theorem2_12_martingaleRosenthal_upper 4 (by omega)
  refine ⟨C_4, hC4, hC4top, ?_⟩
  intro n hn
  have hL4 : ∀ k, MemLp (increment k) 4 mu :=
    fun k => increment_memLp_of_martingale_uniform_bound
      mu filtration increment hmartingale B hbound 4 k
  have hL2 : ∀ k, MemLp (increment k) 2 mu :=
    fun k => increment_memLp_of_martingale_uniform_bound
      mu filtration increment hmartingale B hbound 2 k
  have hHH := hsource mu filtration increment n hmartingale
    (fun k _hk => hL4 k) (fun k _hk => hL2 k)
  have hpredictableMoment := predictableQuadraticFourthMoment_le
    mu filtration increment V n (hpredictable n)
  have hjumpMoment := incrementAbsoluteFourthMomentSum_le_of_uniform_bound
    mu increment B hB hbound n
  have hnSquare := natCast_le_square n hn
  calc
    terminalAbsoluteMoment mu increment 4 n ≤
        C_4 *
          (predictableQuadraticMoment mu filtration increment 4 n +
            incrementAbsoluteMomentSum mu increment 4 n) := hHH
    _ ≤ C_4 *
          (V ^ 2 * (n : ENNReal) ^ 2 +
            (n : ENNReal) * (ENNReal.ofReal B) ^ 4) := by
      gcongr
    _ ≤ C_4 *
          (V ^ 2 * (n : ENNReal) ^ 2 +
            (n : ENNReal) ^ 2 * (ENNReal.ofReal B) ^ 4) := by
      gcongr
    _ = (C_4 * (V ^ 2 + (ENNReal.ofReal B) ^ 4)) *
          (n : ENNReal) ^ 2 := by ring

/-- Dividing the polynomial score bound by `n^2` yields a uniform normalized
score fourth moment. -/
theorem normalizedScoreFourthMoment_le
    (scoreFourth : Nat -> ENNReal) (A : ENNReal)
    (hscore : HasPolynomialFourthMomentBound scoreFourth A)
    (n : Nat) (hn : 0 < n) :
    ((n : ENNReal) ^ 2)⁻¹ * scoreFourth n ≤ A := by
  calc
    ((n : ENNReal) ^ 2)⁻¹ * scoreFourth n ≤
        ((n : ENNReal) ^ 2)⁻¹ * (A * (n : ENNReal) ^ 2) := by
      gcongr
      exact hscore n hn
    _ = A := inv_square_mul_square_cancel A n hn

/-- A polynomial score fourth moment and an explicit normalized coercivity
estimate imply a uniform normalized estimator-error fourth moment. -/
theorem errorFourthMoment_le_of_score_and_coercivity
    (scoreFourth errorFourth : Nat -> ENNReal)
    (A coercivityConstant remainderBound : ENNReal)
    (hscore : HasPolynomialFourthMomentBound scoreFourth A)
    (hcoercive : HasNormalizedScoreCoercivity scoreFourth errorFourth
      coercivityConstant remainderBound)
    (n : Nat) (hn : 0 < n) :
    errorFourth n ≤ coercivityConstant * A + remainderBound := by
  calc
    errorFourth n ≤
        coercivityConstant * ((n : ENNReal) ^ 2)⁻¹ * scoreFourth n +
          remainderBound := hcoercive n hn
    _ = coercivityConstant *
          (((n : ENNReal) ^ 2)⁻¹ * scoreFourth n) +
          remainderBound := by ring
    _ ≤ coercivityConstant * A + remainderBound := by
      gcongr
      exact normalizedScoreFourthMoment_le scoreFourth A hscore n hn

/-- A stable Newton/MLE transfer propagates a uniform fourth-moment bound. -/
theorem stableFourthMoment_le
    (inputFourth outputFourth : Nat -> ENNReal)
    (inputBound stabilityConstant remainderBound : ENNReal)
    (hinput : ∀ n, 0 < n -> inputFourth n ≤ inputBound)
    (hstable : HasStableFourthMomentTransfer inputFourth outputFourth
      stabilityConstant remainderBound)
    (n : Nat) (hn : 0 < n) :
    outputFourth n ≤ stabilityConstant * inputBound + remainderBound := by
  exact (hstable n hn).trans (by gcongr; exact hinput n hn)

/-- The score/coercivity route supplies the exact uniform fourth-moment
hypothesis consumed by `MomentRiskTransfer`.  The time-zero case is stated
separately because no inverse sample size is available there. -/
theorem hasUniformFiniteLocalFourthMomentBound_of_score_coercivity
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : Nat -> StatisticalExperiment (LANParameter D))
    (T : (n : Nat) -> Statistic (E n) (LANParameter D))
    (I : Finset (LANParameter D))
    (scoreFourth : Nat -> ↥I -> ENNReal)
    (A coercivityConstant remainderBound zeroBound : ENNReal)
    (hscore : ∀ h : ↥I,
      HasPolynomialFourthMomentBound (fun n => scoreFourth n h) A)
    (hcoercive : ∀ h : ↥I,
      HasNormalizedScoreCoercivity
        (fun n => scoreFourth n h)
        (fun n => localQuadraticFourthMoment E T n h.1)
        coercivityConstant remainderBound)
    (hzero : ∀ h : ↥I,
      localQuadraticFourthMoment E T 0 h.1 ≤ zeroBound) :
    HasUniformFiniteLocalFourthMomentBound E T I
      (max zeroBound (coercivityConstant * A + remainderBound)) := by
  intro n h
  by_cases hn0 : n = 0
  · subst n
    exact (hzero h).trans (le_max_left _ _)
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    exact (errorFourthMoment_le_of_score_and_coercivity
      (fun m => scoreFourth m h)
      (fun m => localQuadraticFourthMoment E T m h.1)
      A coercivityConstant remainderBound (hscore h) (hcoercive h) n hn).trans
        (le_max_right _ _)

/-- A score-to-root coercivity estimate followed by a stable MLE transfer
supplies the corresponding uniform local MLE fourth moment. -/
theorem hasUniformFiniteLocalFourthMomentBound_of_score_root_mle
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : Nat -> StatisticalExperiment (LANParameter D))
    (T : (n : Nat) -> Statistic (E n) (LANParameter D))
    (I : Finset (LANParameter D))
    (scoreFourth rootFourth : Nat -> ↥I -> ENNReal)
    (A scoreCoercivity scoreRemainder mleStability mleRemainder zeroBound :
      ENNReal)
    (hscore : ∀ h : ↥I,
      HasPolynomialFourthMomentBound (fun n => scoreFourth n h) A)
    (hroot : ∀ h : ↥I,
      HasNormalizedScoreCoercivity
        (fun n => scoreFourth n h) (fun n => rootFourth n h)
        scoreCoercivity scoreRemainder)
    (hmle : ∀ h : ↥I,
      HasStableFourthMomentTransfer
        (fun n => rootFourth n h)
        (fun n => localQuadraticFourthMoment E T n h.1)
        mleStability mleRemainder)
    (hzero : ∀ h : ↥I,
      localQuadraticFourthMoment E T 0 h.1 ≤ zeroBound) :
    HasUniformFiniteLocalFourthMomentBound E T I
      (max zeroBound
        (mleStability * (scoreCoercivity * A + scoreRemainder) +
          mleRemainder)) := by
  intro n h
  by_cases hn0 : n = 0
  · subst n
    exact (hzero h).trans (le_max_left _ _)
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    have hrootBound : rootFourth n h ≤ scoreCoercivity * A + scoreRemainder :=
      errorFourthMoment_le_of_score_and_coercivity
        (fun m => scoreFourth m h) (fun m => rootFourth m h)
        A scoreCoercivity scoreRemainder (hscore h) (hroot h) n hn
    exact ((hmle h n hn).trans (by gcongr)).trans (le_max_right _ _)

/-- Direct bridge from martingale score moments to the quadratic-tail
condition used in the paper's expected-risk attainment theorem. -/
theorem quadraticTails_of_score_coercivity
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : Nat -> StatisticalExperiment (LANParameter D))
    (T : (n : Nat) -> Statistic (E n) (LANParameter D))
    (I : Finset (LANParameter D))
    (scoreFourth : Nat -> ↥I -> ENNReal)
    (A coercivityConstant remainderBound zeroBound : ENNReal)
    (hscore : ∀ h : ↥I,
      HasPolynomialFourthMomentBound (fun n => scoreFourth n h) A)
    (hcoercive : ∀ h : ↥I,
      HasNormalizedScoreCoercivity
        (fun n => scoreFourth n h)
        (fun n => localQuadraticFourthMoment E T n h.1)
        coercivityConstant remainderBound)
    (hzero : ∀ h : ↥I,
      localQuadraticFourthMoment E T 0 h.1 ≤ zeroBound)
    (hfinite : max zeroBound
      (coercivityConstant * A + remainderBound) ≠ ∞) :
    HasUniformFiniteLocalQuadraticTails E T I := by
  apply hasUniformFiniteLocalQuadraticTails_of_fourthMoment
    E T I (max zeroBound (coercivityConstant * A + remainderBound)) hfinite
  exact hasUniformFiniteLocalFourthMomentBound_of_score_coercivity
    E T I scoreFourth A coercivityConstant remainderBound zeroBound
    hscore hcoercive hzero

end SourceFaithfulMartingaleMoments

open SourceFaithfulMartingaleMoments

namespace Label

/-- Supplement equation `eq:SI_score_moments`: bounded score increments and
predictable conditional-variance growth imply fourth moments of order `n^2`. -/
theorem eq_SI_score_moments
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration Nat (inferInstance : MeasurableSpace Omega))
    (increment : Nat -> Omega -> Real)
    (hmartingale : Martingale (scalarPartialSum increment) filtration mu)
    (B : Real) (hB : 0 ≤ B)
    (hbound : ∀ k, ∀ᵐ omega ∂mu,
      norm (increment k omega) ≤ B)
    (V : ENNReal)
    (hpredictable : ∀ n, ∀ᵐ omega ∂mu,
      ENNReal.ofReal (conditionalVarianceSum mu filtration increment n omega) ≤
        (n : ENNReal) * V) :
    ∃ C_4 : ENNReal, 0 < C_4 ∧ C_4 ≠ ∞ ∧
      HasPolynomialFourthMomentBound
        (fun n => terminalAbsoluteMoment mu increment 4 n)
        (C_4 * (V ^ 2 + (ENNReal.ofReal B) ^ 4)) :=
  polynomialScoreFourthMoment_of_hallHeyde
    mu filtration increment hmartingale B hB hbound V hpredictable

/-- Supplement equation `eq:SI_error_moment_bound`: score growth plus the
explicit score-to-error coercivity inequality gives a uniform error moment. -/
theorem eq_SI_error_moment_bound
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : Nat -> StatisticalExperiment (LANParameter D))
    (T : (n : Nat) -> Statistic (E n) (LANParameter D))
    (I : Finset (LANParameter D))
    (scoreFourth : Nat -> ↥I -> ENNReal)
    (A coercivityConstant remainderBound zeroBound : ENNReal)
    (hscore : ∀ h : ↥I,
      HasPolynomialFourthMomentBound (fun n => scoreFourth n h) A)
    (hcoercive : ∀ h : ↥I,
      HasNormalizedScoreCoercivity
        (fun n => scoreFourth n h)
        (fun n => localQuadraticFourthMoment E T n h.1)
        coercivityConstant remainderBound)
    (hzero : ∀ h : ↥I,
      localQuadraticFourthMoment E T 0 h.1 ≤ zeroBound) :
    HasUniformFiniteLocalFourthMomentBound E T I
      (max zeroBound (coercivityConstant * A + remainderBound)) :=
  hasUniformFiniteLocalFourthMomentBound_of_score_coercivity
    E T I scoreFourth A coercivityConstant remainderBound zeroBound
    hscore hcoercive hzero

/-- Supplement equation `eq:SI_MLE_moment_bound`: a coercive score-root bound
and a stable Newton/MLE transfer give a uniform MLE fourth moment. -/
theorem eq_SI_MLE_moment_bound
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : Nat -> StatisticalExperiment (LANParameter D))
    (T : (n : Nat) -> Statistic (E n) (LANParameter D))
    (I : Finset (LANParameter D))
    (scoreFourth rootFourth : Nat -> ↥I -> ENNReal)
    (A scoreCoercivity scoreRemainder mleStability mleRemainder zeroBound :
      ENNReal)
    (hscore : ∀ h : ↥I,
      HasPolynomialFourthMomentBound (fun n => scoreFourth n h) A)
    (hroot : ∀ h : ↥I,
      HasNormalizedScoreCoercivity
        (fun n => scoreFourth n h) (fun n => rootFourth n h)
        scoreCoercivity scoreRemainder)
    (hmle : ∀ h : ↥I,
      HasStableFourthMomentTransfer
        (fun n => rootFourth n h)
        (fun n => localQuadraticFourthMoment E T n h.1)
        mleStability mleRemainder)
    (hzero : ∀ h : ↥I,
      localQuadraticFourthMoment E T 0 h.1 ≤ zeroBound) :
    HasUniformFiniteLocalFourthMomentBound E T I
      (max zeroBound
        (mleStability * (scoreCoercivity * A + scoreRemainder) +
          mleRemainder)) :=
  hasUniformFiniteLocalFourthMomentBound_of_score_root_mle
    E T I scoreFourth rootFourth A scoreCoercivity scoreRemainder
    mleStability mleRemainder zeroBound hscore hroot hmle hzero

end Label

end

end QubitOracle.Paper
