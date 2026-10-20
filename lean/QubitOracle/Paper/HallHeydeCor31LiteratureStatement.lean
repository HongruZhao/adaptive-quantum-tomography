import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Process.Filtration

/-!
# Hall--Heyde Corollary 3.1: source-clean literature statement

This module contains only the generic deterministic-variance specialization
used by the pure-multilevel martingale reduction.  It deliberately imports no
qubit model.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace QubitOracle.Paper

noncomputable section

/-- Convergence in probability written through deviation-event
probabilities. -/
def HallHeydeScalarConvergesInProbability
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (Z : ℕ → Omega → ℝ) (z : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    Tendsto (fun n => mu {omega | epsilon ≤ |Z n omega - z|})
      atTop (nhds 0)

/-- Terminal sum of a varying-length scalar martingale row. -/
def hallHeydeDeterministicVarianceRowSum
    {Omega : Type*} (rowLength : ℕ → ℕ)
    (increment : (n : ℕ) → Fin (rowLength n) → Omega → ℝ) :
    ℕ → Omega → ℝ :=
  fun n omega => ∑ k : Fin (rowLength n), increment n k omega

/-- Exact deterministic-variance premise record for Hall and Heyde (1980),
Corollary 3.1. -/
structure HallHeyde1980Corollary31DeterministicVariancePremises
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    (mu : Measure Omega)
    (rowLength : ℕ → ℕ)
    (filtration : ℕ → Filtration ℕ mOmega)
    (increment : (n : ℕ) → Fin (rowLength n) → Omega → ℝ)
    (conditionalVariance :
      (n : ℕ) → Fin (rowLength n) → Omega → ℝ)
    (conditionalLindeberg :
      ℝ → (n : ℕ) → Fin (rowLength n) → Omega → ℝ)
    (sigmaSq : ℝ) : Prop where
  condition321 :
    ∀ n k : ℕ,
      k ≤ rowLength n → k ≤ rowLength (n + 1) →
        filtration n k ≤ filtration (n + 1) k
  increment_measurable :
    ∀ n (k : Fin (rowLength n)),
      Measurable[filtration n (k.1 + 1)] (increment n k)
  increment_integrable :
    ∀ n (k : Fin (rowLength n)), Integrable (increment n k) mu
  increment_square_integrable :
    ∀ n (k : Fin (rowLength n)),
      Integrable (fun omega => increment n k omega ^ 2) mu
  martingaleDifference :
    ∀ n (k : Fin (rowLength n)),
      mu[increment n k | filtration n k.1] =ᵐ[mu]
        (fun _ : Omega => (0 : ℝ))
  conditionalVarianceVersion :
    ∀ n (k : Fin (rowLength n)),
      mu[(fun omega => increment n k omega ^ 2) |
          filtration n k.1] =ᵐ[mu]
        conditionalVariance n k
  conditionalLindebergVersion :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ n (k : Fin (rowLength n)),
        mu[(fun omega =>
            if epsilon < |increment n k omega| then
              increment n k omega ^ 2
            else 0) | filtration n k.1] =ᵐ[mu]
          conditionalLindeberg epsilon n k
  sigmaSq_nonnegative : 0 ≤ sigmaSq
  conditionalVariance_converges :
    HallHeydeScalarConvergesInProbability mu
      (fun n omega =>
        ∑ k : Fin (rowLength n), conditionalVariance n k omega)
      sigmaSq
  conditionalLindeberg_converges :
    ∀ epsilon : ℝ, 0 < epsilon →
      HallHeydeScalarConvergesInProbability mu
        (fun n omega =>
          ∑ k : Fin (rowLength n),
            conditionalLindeberg epsilon n k omega)
        0

/-- The deterministic-variance consequence of Hall--Heyde Corollary 3.1.
The book proves the stronger stable-convergence statement; this is its
ordinary convergence-in-distribution specialization. -/
def HallHeyde1980Corollary31DeterministicVarianceStatement : Prop :=
  ∀ {Omega : Type*} [mOmega : MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (rowLength : ℕ → ℕ)
    (filtration : ℕ → Filtration ℕ mOmega)
    (increment : (n : ℕ) → Fin (rowLength n) → Omega → ℝ)
    (conditionalVariance :
      (n : ℕ) → Fin (rowLength n) → Omega → ℝ)
    (conditionalLindeberg :
      ℝ → (n : ℕ) → Fin (rowLength n) → Omega → ℝ)
    (sigmaSq : ℝ),
    HallHeyde1980Corollary31DeterministicVariancePremises
        mu rowLength filtration increment conditionalVariance
          conditionalLindeberg sigmaSq →
      TendstoInDistribution
        (hallHeydeDeterministicVarianceRowSum rowLength increment)
        atTop id (fun _ => mu)
        (gaussianReal 0 sigmaSq.toNNReal)

end
end QubitOracle.Paper
