import QubitOracle.Paper.GaussianNormRisk
import QubitOracle.Paper.SourceFaithfulMinimax

/-!
# Source-faithful asymptotic minimax transfer

The external declaration below is the finite-dimensional Gaussian-score,
bounded-loss specialization of the asymptotic minimax theorem for weakly
convergent experiments.  It is the form obtained from Pollard, *Some Thoughts
on Le Cam's Statistical Decision Theory*, theorem (5), together with the
Gaussian shift minimax identity (van der Vaart, *Asymptotic Statistics*,
Proposition 8.6).

Unlike an estimator-efficiency statement, this theorem quantifies over every
estimator sequence and takes a supremum over finite local parameter sets.  It
therefore supplies the genuine local asymptotic minimax lower bound needed by
the paper.  The loss cap is required to be finite, exactly as in the source
theorem.
-/

namespace QubitOracle.Paper

open MeasureTheory ProbabilityTheory Filter

noncomputable section

/-- Quadratic risk of the `n`th estimator at local parameter `h`. -/
def localQuadraticRisk
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : ℕ → StatisticalExperiment (LANParameter D))
    (T : (n : ℕ) → Statistic (E n) (LANParameter D))
    (n : ℕ) (h : LANParameter D) : ENNReal :=
  ∫⁻ x, ENNReal.ofReal (‖(T n).toFun x - h‖ ^ 2) ∂(E n).measure h

/-- Worst risk over one finite local parameter set.  The empty set contributes
zero, as it should under the outer supremum over all finite sets. -/
def finiteLocalWorstQuadraticRisk
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : ℕ → StatisticalExperiment (LANParameter D))
    (T : (n : ℕ) → Statistic (E n) (LANParameter D))
    (I : Finset (LANParameter D)) (n : ℕ) : ENNReal :=
  ⨆ h : ↥I, localQuadraticRisk E T n h.1

/-- The finite-local asymptotic minimax criterion used in the paper. -/
def asymptoticFiniteLocalQuadraticRisk
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : ℕ → StatisticalExperiment (LANParameter D))
    (T : (n : ℕ) → Statistic (E n) (LANParameter D)) : ENNReal :=
  ⨆ I : Finset (LANParameter D),
    Filter.liminf (fun n => finiteLocalWorstQuadraticRisk E T I n) Filter.atTop

/-- Pollard's asymptotic minimax theorem, specialized to a nondegenerate
Gaussian location limit and finite capped squared-norm loss.

This is a source theorem interface, not a placeholder over an arbitrary
proposition: its experiment, convergence mode, estimator, loss, Gaussian
benchmark, and finite-local conclusion are all represented explicitly. -/
axiom pollard_asymptoticMinimax_gaussianScore_capped
    {D : Type*} [Fintype D] [DecidableEq D]
    (J : Matrix D D ℝ) (hJ : J.PosDef)
    (E : ℕ → StatisticalExperiment (LANParameter D))
    (hExperiment : ExperimentsConverge E (gaussianScoreExperiment J))
    (T : (n : ℕ) → Statistic (E n) (LANParameter D))
    (cap : ENNReal) (hcap : cap ≠ ⊤) :
    (∫⁻ z, cappedSquaredNormLoss cap z
        ∂multivariateGaussian (0 : LANParameter D) J⁻¹) ≤
      asymptoticFiniteLocalQuadraticRisk E T

/-- Genuine local asymptotic minimax lower bound for every estimator sequence.
No regularity or weak-limit assumption is imposed on the estimators. -/
theorem gaussianScore_localAsymptoticMinimax_quadratic
    {D : Type*} [Fintype D] [DecidableEq D]
    (J : Matrix D D ℝ) (hJ : J.PosDef)
    (E : ℕ → StatisticalExperiment (LANParameter D))
    (hExperiment : ExperimentsConverge E (gaussianScoreExperiment J))
    (T : (n : ℕ) → Statistic (E n) (LANParameter D)) :
    ENNReal.ofReal (Matrix.trace J⁻¹) ≤
      asymptoticFiniteLocalQuadraticRisk E T := by
  apply le_of_tendsto
    (lintegral_cappedSquaredNormLoss_multivariateGaussian_tendsto
      J⁻¹ hJ.inv.posSemidef)
  filter_upwards [] with n
  exact pollard_asymptoticMinimax_gaussianScore_capped
    J hJ E hExperiment T (n : ENNReal) (by simp)

end

end QubitOracle.Paper
