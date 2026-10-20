import Mathlib
import QubitOracle.Paper.LogThirdOrderRemainderCore

/-!
# Pathwise Bernoulli LAN algebra for adaptive qubit measurements

At every time, conditional on the observed history, a binary qubit
measurement has probability `(1 + y*m)/2`.  Under a root-sample local
perturbation whose directional derivative is `d`, its likelihood ratio is
`1 + y*d / (sqrt N * (1 + y*m))`.

This file proves the exact finite-path decomposition into score, observed
quadratic term, and scalar logarithm remainder.  Adaptivity causes no issue in
this pathwise calculation: `m` and `d` may depend arbitrarily on the complete
path.  Predictability enters only later when the score is treated as a
martingale.
-/

open scoped BigOperators

namespace QubitOracle.Paper

noncomputable section

def bernoulliSign (outcome : Bool) : ℝ :=
  if outcome then 1 else -1

def bernoulliLocalRatio
    {N : ℕ} (baseMean localDirection : Fin N → (Fin N → Bool) → ℝ)
    (path : Fin N → Bool) (t : Fin N) : ℝ :=
  bernoulliSign (path t) * localDirection t path /
    (Real.sqrt N * (1 + bernoulliSign (path t) * baseMean t path))

def bernoulliLogLikelihoodRatio
    {N : ℕ} (baseMean localDirection : Fin N → (Fin N → Bool) → ℝ)
    (path : Fin N → Bool) : ℝ :=
  ∑ t, Real.log (1 + bernoulliLocalRatio baseMean localDirection path t)

def bernoulliLocalScore
    {N : ℕ} (baseMean localDirection : Fin N → (Fin N → Bool) → ℝ)
    (path : Fin N → Bool) : ℝ :=
  ∑ t, bernoulliLocalRatio baseMean localDirection path t

def bernoulliObservedQuadratic
    {N : ℕ} (baseMean localDirection : Fin N → (Fin N → Bool) → ℝ)
    (path : Fin N → Bool) : ℝ :=
  ∑ t, bernoulliLocalRatio baseMean localDirection path t ^ 2

def bernoulliLANRemainder
    {N : ℕ} (baseMean localDirection : Fin N → (Fin N → Bool) → ℝ)
    (path : Fin N → Bool) : ℝ :=
  ∑ t, logThirdOrderRemainder
    (bernoulliLocalRatio baseMean localDirection path t)

/-- Exact pathwise likelihood decomposition, before any limit theorem. -/
theorem bernoulliLogLikelihoodRatio_exact_decomposition
    {N : ℕ} (baseMean localDirection : Fin N → (Fin N → Bool) → ℝ)
    (path : Fin N → Bool) :
    bernoulliLogLikelihoodRatio baseMean localDirection path =
      bernoulliLocalScore baseMean localDirection path -
        bernoulliObservedQuadratic baseMean localDirection path / 2 +
          bernoulliLANRemainder baseMean localDirection path := by
  unfold bernoulliLogLikelihoodRatio bernoulliLocalScore
    bernoulliObservedQuadratic bernoulliLANRemainder
    logThirdOrderRemainder
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_div]
  ring

theorem abs_bernoulliLocalRatio_le
    {N : ℕ} (hN : 0 < N)
    (baseMean localDirection : Fin N → (Fin N → Bool) → ℝ)
    (path : Fin N → Bool) (t : Fin N)
    (margin R : ℝ) (hmargin : 0 < margin) (hR : 0 ≤ R)
    (hdenominator :
      margin ≤ 1 + bernoulliSign (path t) * baseMean t path)
    (hdirection : |localDirection t path| ≤ R) :
    |bernoulliLocalRatio baseMean localDirection path t| ≤
      R / (margin * Real.sqrt N) := by
  have hsqrt : 0 < Real.sqrt N := by
    exact Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hsign : |bernoulliSign (path t)| = 1 := by
    cases path t <;> simp [bernoulliSign]
  have hdenpos :
      0 < 1 + bernoulliSign (path t) * baseMean t path :=
    hmargin.trans_le hdenominator
  unfold bernoulliLocalRatio
  rw [abs_div, abs_mul, hsign, one_mul, abs_mul,
    abs_of_pos hsqrt, abs_of_pos hdenpos]
  exact div_le_div₀ hR hdirection (mul_pos hmargin hsqrt) (by
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_left hdenominator hsqrt.le))

/-- Uniform cubic remainder for an arbitrary history-dependent binary qubit
path. -/
theorem bernoulliLANRemainder_uniform_bound
    (hLog : LogThirdOrderRemainderContract)
    {N : ℕ} (hN : 0 < N)
    (baseMean localDirection : Fin N → (Fin N → Bool) → ℝ)
    (path : Fin N → Bool) (margin R : ℝ)
    (hmargin : 0 < margin) (hR : 0 ≤ R)
    (hdenominator : ∀ t,
      margin ≤ 1 + bernoulliSign (path t) * baseMean t path)
    (hdirection : ∀ t, |localDirection t path| ≤ R)
    (hlocal : R / (margin * Real.sqrt N) ≤ 1 / 2) :
    |bernoulliLANRemainder baseMean localDirection path| ≤
      (N : ℝ) * (8 / 3 : ℝ) *
        (R / (margin * Real.sqrt N)) ^ 3 := by
  have hratio : ∀ t,
      |bernoulliLocalRatio baseMean localDirection path t| ≤
        R / (margin * Real.sqrt N) := by
    intro t
    exact abs_bernoulliLocalRatio_le hN baseMean localDirection path t
      margin R hmargin hR (hdenominator t) (hdirection t)
  calc
    |bernoulliLANRemainder baseMean localDirection path| ≤
        ∑ t, |logThirdOrderRemainder
          (bernoulliLocalRatio baseMean localDirection path t)| := by
      unfold bernoulliLANRemainder
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t : Fin N,
          (8 / 3 : ℝ) * (R / (margin * Real.sqrt N)) ^ 3 := by
      apply Finset.sum_le_sum
      intro t ht
      calc
        |logThirdOrderRemainder
            (bernoulliLocalRatio baseMean localDirection path t)| ≤
            (8 / 3 : ℝ) *
              |bernoulliLocalRatio baseMean localDirection path t| ^ 3 :=
          hLog _ ((hratio t).trans hlocal)
        _ ≤ (8 / 3 : ℝ) *
              (R / (margin * Real.sqrt N)) ^ 3 := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀
              (abs_nonneg _) (hratio t) 3) (by norm_num)
    _ = (N : ℝ) * (8 / 3 : ℝ) *
          (R / (margin * Real.sqrt N)) ^ 3 := by
      simp
      ring

namespace Label

/-- Supplement-facing exact adaptive Bernoulli LAN decomposition. -/
theorem eq_SI_adaptive_Bernoulli_LAN_pathwise
    {N : ℕ} (baseMean localDirection : Fin N → (Fin N → Bool) → ℝ)
    (path : Fin N → Bool) :
    bernoulliLogLikelihoodRatio baseMean localDirection path =
      bernoulliLocalScore baseMean localDirection path -
        bernoulliObservedQuadratic baseMean localDirection path / 2 +
          bernoulliLANRemainder baseMean localDirection path :=
  bernoulliLogLikelihoodRatio_exact_decomposition
    baseMean localDirection path

end Label
end

end QubitOracle.Paper
