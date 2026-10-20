import QubitOracle.Paper.SourceFaithfulAsymptoticMinimax

/-!
# Quadratic-risk attainability

This module isolates the cap-removal argument needed to turn bounded-loss
asymptotics into full quadratic-risk attainability.

The assumptions are deliberately explicit.  For every nonempty finite local
parameter set, the increasing-cap worst risks must converge to the centered
Gaussian benchmark, and the cap-removal remainders must vanish uniformly in
sample size.  Neither full-risk convergence nor attainment is assumed.

The final equality combines the resulting upper bound with the independent
all-estimator local asymptotic minimax lower bound.
-/

namespace QubitOracle.Paper

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

noncomputable section

/-- Capped quadratic risk of the `n`th estimator at local parameter `h`. -/
def localCappedQuadraticRisk
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : ℕ → StatisticalExperiment (LANParameter D))
    (T : (n : ℕ) → Statistic (E n) (LANParameter D))
    (cap : ENNReal) (n : ℕ) (h : LANParameter D) : ENNReal :=
  ∫⁻ x, cappedSquaredNormLoss cap ((T n).toFun x - h) ∂(E n).measure h

/-- Worst capped risk over a finite local parameter set. -/
def finiteLocalWorstCappedQuadraticRisk
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : ℕ → StatisticalExperiment (LANParameter D))
    (T : (n : ℕ) → Statistic (E n) (LANParameter D))
    (cap : ENNReal) (I : Finset (LANParameter D)) (n : ℕ) : ENNReal :=
  ⨆ h : ↥I, localCappedQuadraticRisk E T cap n h.1

/-- Capping can only decrease local quadratic risk. -/
theorem localCappedQuadraticRisk_le_localQuadraticRisk
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : ℕ → StatisticalExperiment (LANParameter D))
    (T : (n : ℕ) → Statistic (E n) (LANParameter D))
    (cap : ENNReal) (n : ℕ) (h : LANParameter D) :
    localCappedQuadraticRisk E T cap n h ≤ localQuadraticRisk E T n h := by
  apply lintegral_mono
  intro x
  exact min_le_left _ _

/-- Capping can only decrease the worst risk over a finite local set. -/
theorem finiteLocalWorstCappedQuadraticRisk_le
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : ℕ → StatisticalExperiment (LANParameter D))
    (T : (n : ℕ) → Statistic (E n) (LANParameter D))
    (cap : ENNReal) (I : Finset (LANParameter D)) (n : ℕ) :
    finiteLocalWorstCappedQuadraticRisk E T cap I n ≤
      finiteLocalWorstQuadraticRisk E T I n := by
  refine iSup_le fun h => ?_
  exact (localCappedQuadraticRisk_le_localQuadraticRisk E T cap n h.1).trans
    (le_iSup (fun k : ↥I => localQuadraticRisk E T n k.1) h)

/-- The exact aggregate cap-removal remainder.  It is not an assumed error:
it is defined as full finite-local worst risk minus capped worst risk. -/
def finiteLocalQuadraticTailRemainder
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : ℕ → StatisticalExperiment (LANParameter D))
    (T : (n : ℕ) → Statistic (E n) (LANParameter D))
    (cap : ENNReal) (I : Finset (LANParameter D)) (n : ℕ) : ENNReal :=
  finiteLocalWorstQuadraticRisk E T I n -
    finiteLocalWorstCappedQuadraticRisk E T cap I n

/-- Full risk is exactly capped risk plus its cap-removal remainder. -/
theorem finiteLocalWorstCapped_add_tailRemainder
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : ℕ → StatisticalExperiment (LANParameter D))
    (T : (n : ℕ) → Statistic (E n) (LANParameter D))
    (cap : ENNReal) (I : Finset (LANParameter D)) (n : ℕ) :
    finiteLocalWorstCappedQuadraticRisk E T cap I n +
        finiteLocalQuadraticTailRemainder E T cap I n =
      finiteLocalWorstQuadraticRisk E T I n := by
  exact add_tsub_cancel_of_le
    (finiteLocalWorstCappedQuadraticRisk_le E T cap I n)

/-- Uniform quadratic-tail control: after raising the cap, the cap-removal
remainder tends to zero uniformly over all sample sizes.  This is the precise
uniform-integrability hypothesis used below. -/
def HasUniformFiniteLocalQuadraticTails
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : ℕ → StatisticalExperiment (LANParameter D))
    (T : (n : ℕ) → Statistic (E n) (LANParameter D))
    (I : Finset (LANParameter D)) : Prop :=
  Tendsto
    (fun m : ℕ =>
      ⨆ n : ℕ, finiteLocalQuadraticTailRemainder E T (m : ENNReal) I n)
    atTop (nhds 0)

/-- Uniform tail control implies vanishing tail along the diagonal cap
`cap = n`. -/
theorem HasUniformFiniteLocalQuadraticTails.diagonal
    {D : Type*} [Fintype D] [DecidableEq D]
    {E : ℕ → StatisticalExperiment (LANParameter D)}
    {T : (n : ℕ) → Statistic (E n) (LANParameter D)}
    {I : Finset (LANParameter D)}
    (hTail : HasUniformFiniteLocalQuadraticTails E T I) :
    Tendsto
      (fun n : ℕ => finiteLocalQuadraticTailRemainder E T (n : ENNReal) I n)
      atTop (nhds 0) := by
  refine Filter.Tendsto.squeeze tendsto_const_nhds hTail ?_ ?_
  · intro n
    exact bot_le
  · intro n
    exact le_iSup
      (fun k : ℕ => finiteLocalQuadraticTailRemainder E T (n : ENNReal) I k) n

/-- Abstract cap-removal lemma.  Convergence of capped risks and vanishing of
the exact tail remainder imply convergence of the full risks. -/
theorem finiteLocalWorstQuadraticRisk_tendsto_of_capped_and_tail
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : ℕ → StatisticalExperiment (LANParameter D))
    (T : (n : ℕ) → Statistic (E n) (LANParameter D))
    (cap : ℕ → ENNReal) (I : Finset (LANParameter D)) (benchmark : ENNReal)
    (hCapped :
      Tendsto
        (fun n => finiteLocalWorstCappedQuadraticRisk E T (cap n) I n)
        atTop (nhds benchmark))
    (hTail :
      Tendsto
        (fun n => finiteLocalQuadraticTailRemainder E T (cap n) I n)
        atTop (nhds 0)) :
    Tendsto (fun n => finiteLocalWorstQuadraticRisk E T I n)
      atTop (nhds benchmark) := by
  refine Filter.Tendsto.squeeze
    (h := fun n =>
      finiteLocalWorstCappedQuadraticRisk E T (cap n) I n +
        finiteLocalQuadraticTailRemainder E T (cap n) I n)
    hCapped ?_ ?_ ?_
  · simpa using hCapped.add hTail
  · intro n
    exact finiteLocalWorstCappedQuadraticRisk_le E T (cap n) I n
  · intro n
    exact (finiteLocalWorstCapped_add_tailRemainder E T (cap n) I n).ge

/-- Exact full quadratic risk of the centered Gaussian score benchmark. -/
def centeredGaussianQuadraticBenchmark
    {D : Type*} [Fintype D] [DecidableEq D]
    (J : Matrix D D ℝ) : ENNReal :=
  ∫⁻ z, ENNReal.ofReal (‖z‖ ^ 2)
    ∂multivariateGaussian (0 : LANParameter D) J⁻¹

/-- The centered Gaussian benchmark is `trace(J⁻¹)`. -/
theorem centeredGaussianQuadraticBenchmark_eq_trace
    {D : Type*} [Fintype D] [DecidableEq D]
    (J : Matrix D D ℝ) (hJ : J.PosDef) :
    centeredGaussianQuadraticBenchmark J =
      ENNReal.ofReal (Matrix.trace J⁻¹) := by
  exact lintegral_ofReal_norm_sq_multivariateGaussian J⁻¹ hJ.inv.posSemidef

/-- Increasing-cap finite-local risks converge to the centered Gaussian
benchmark.  This is an asymptotic capped-risk hypothesis, not a full-risk
hypothesis. -/
def CappedFiniteLocalRisksConvergeToCenteredGaussian
    {D : Type*} [Fintype D] [DecidableEq D]
    (J : Matrix D D ℝ)
    (E : ℕ → StatisticalExperiment (LANParameter D))
    (T : (n : ℕ) → Statistic (E n) (LANParameter D))
    (I : Finset (LANParameter D)) : Prop :=
  Tendsto
    (fun n : ℕ =>
      finiteLocalWorstCappedQuadraticRisk E T (n : ENNReal) I n)
    atTop (nhds (centeredGaussianQuadraticBenchmark J))

/-- Capped Gaussian asymptotics plus uniform quadratic tails imply convergence
of the full finite-local worst risk to `trace(J⁻¹)`. -/
theorem finiteLocalWorstQuadraticRisk_tendsto_trace_of_cappedGaussian_of_uniformTails
    {D : Type*} [Fintype D] [DecidableEq D]
    (J : Matrix D D ℝ) (hJ : J.PosDef)
    (E : ℕ → StatisticalExperiment (LANParameter D))
    (T : (n : ℕ) → Statistic (E n) (LANParameter D))
    (I : Finset (LANParameter D))
    (hCapped : CappedFiniteLocalRisksConvergeToCenteredGaussian J E T I)
    (hTail : HasUniformFiniteLocalQuadraticTails E T I) :
    Tendsto (fun n => finiteLocalWorstQuadraticRisk E T I n)
      atTop (nhds (ENNReal.ofReal (Matrix.trace J⁻¹))) := by
  have hFull :=
    finiteLocalWorstQuadraticRisk_tendsto_of_capped_and_tail
      E T (fun n : ℕ => (n : ENNReal)) I
      (centeredGaussianQuadraticBenchmark J) hCapped hTail.diagonal
  rwa [centeredGaussianQuadraticBenchmark_eq_trace J hJ] at hFull

/-- An estimator attains the Gaussian local asymptotic minimax bound when its
finite-local asymptotic quadratic-risk criterion equals `trace(J⁻¹)`. -/
def AttainsGaussianLocalAsymptoticMinimaxBound
    {D : Type*} [Fintype D] [DecidableEq D]
    (J : Matrix D D ℝ)
    (E : ℕ → StatisticalExperiment (LANParameter D))
    (T : (n : ℕ) → Statistic (E n) (LANParameter D)) : Prop :=
  asymptoticFiniteLocalQuadraticRisk E T =
    ENNReal.ofReal (Matrix.trace J⁻¹)

/-- Honest attainability bridge.

The capped-risk and uniform-tail hypotheses provide the upper bound.  The
experiment-convergence hypothesis is used only through the all-estimator
local asymptotic minimax theorem, which provides the matching lower bound. -/
theorem gaussianScore_localAsymptoticMinimax_attained_of_cappedGaussian_of_uniformTails
    {D : Type*} [Fintype D] [DecidableEq D]
    (J : Matrix D D ℝ) (hJ : J.PosDef)
    (E : ℕ → StatisticalExperiment (LANParameter D))
    (hExperiment : ExperimentsConverge E (gaussianScoreExperiment J))
    (T : (n : ℕ) → Statistic (E n) (LANParameter D))
    (hCapped :
      ∀ I : Finset (LANParameter D), I.Nonempty →
        CappedFiniteLocalRisksConvergeToCenteredGaussian J E T I)
    (hTail :
      ∀ I : Finset (LANParameter D), I.Nonempty →
        HasUniformFiniteLocalQuadraticTails E T I) :
    AttainsGaussianLocalAsymptoticMinimaxBound J E T := by
  apply le_antisymm
  · unfold asymptoticFiniteLocalQuadraticRisk
    refine iSup_le fun I => ?_
    by_cases hI : I.Nonempty
    · have hFull :=
        finiteLocalWorstQuadraticRisk_tendsto_trace_of_cappedGaussian_of_uniformTails
          J hJ E T I (hCapped I hI) (hTail I hI)
      rw [hFull.liminf_eq]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hI]
      simp [finiteLocalWorstQuadraticRisk]
  · exact gaussianScore_localAsymptoticMinimax_quadratic
      J hJ E hExperiment T

end

end QubitOracle.Paper
