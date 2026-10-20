import Mathlib.Probability.Martingale.Convergence
import Mathlib.Analysis.PSeries

/-!
# Martingale strong law for finite information matrices

This module isolates the `p = 2`, `U_n = n` specialization of Hall and Heyde
(1980), Theorem 2.18.  Its exact hypothesis is almost-sure summability of the
predictable weighted conditional second moments.  Deterministically bounded
increments imply that hypothesis by conditional-expectation monotonicity and
the convergent `p`-series.  The external interface is scalar; finite-matrix
lifts and uniform-bound corollaries are proved below.

Primary source:
P. Hall and C. C. Heyde, *Martingale Limit Theory and Its Application*,
Academic Press, 1980, Theorem 2.18, p. 35.
https://www.stat.yale.edu/~mjk56/MartingaleLimitTheoryAndItsApplication.pdf
-/

namespace QubitOracle.Paper

open Filter MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

def scalarMartingalePartialSum
    {Omega : Type*} (increment : ℕ → Omega → ℝ) : ℕ → Omega → ℝ :=
  fun n omega => ∑ k ∈ Finset.range n, increment k omega

def scalarMartingaleNormalizedSum
    {Omega : Type*} (increment : ℕ → Omega → ℝ) : ℕ → Omega → ℝ :=
  fun n omega => (n : ℝ)⁻¹ * scalarMartingalePartialSum increment n omega

/-- The conditional second moment appearing in Hall--Heyde Theorem 2.18 after
translating their one-based increment `X_i` to our zero-based increment
`increment (i - 1)`. -/
def hallHeydeConditionalSecondMoment
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (filtration : Filtration ℕ (inferInstance : MeasurableSpace Omega))
    (increment : ℕ → Omega → ℝ)
    (n : ℕ) : Omega → ℝ :=
  mu[(fun omega => |increment n omega| ^ 2) | filtration n]

/-- The `U_i⁻² E(|X_i|² | F_{i-1})` summand of Hall--Heyde Theorem 2.18 for
the deterministic normalization `U_i = i`. -/
def hallHeydeWeightedSecondMoment
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (filtration : Filtration ℕ (inferInstance : MeasurableSpace Omega))
    (increment : ℕ → Omega → ℝ)
    (n : ℕ) (omega : Omega) : ℝ :=
  (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ *
    hallHeydeConditionalSecondMoment mu filtration increment n omega

/-- **External literature theorem.** Hall--Heyde Theorem 2.18 specialized to
`p = 2` and deterministic `U_i = i`.  The martingale hypothesis is stated for
the partial-sum process.  The weighted conditional-second-moment summability
assumption is exactly the source theorem's hypothesis under zero-based
indexing. -/
axiom hallHeyde1980_theorem2_18_conditional_second_moment
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ (inferInstance : MeasurableSpace Omega))
    (increment : ℕ → Omega → ℝ)
    (hmartingale : Martingale
      (scalarMartingalePartialSum increment) filtration mu)
    (hL2 : ∀ n, MemLp (increment n) 2 mu)
    (hsummable : ∀ᵐ omega ∂mu,
      Summable (fun n =>
        hallHeydeWeightedSecondMoment mu filtration increment n omega)) :
    ∀ᵐ omega ∂mu,
      Tendsto (fun n => scalarMartingaleNormalizedSum increment n omega)
        atTop (nhds 0)

/-- A deterministic pointwise increment bound implies the exact conditional
moment summability hypothesis of Hall--Heyde Theorem 2.18. -/
theorem hallHeyde1980_theorem2_18_of_uniform_bound
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ (inferInstance : MeasurableSpace Omega))
    (increment : ℕ → Omega → ℝ)
    (hmartingale : Martingale
      (scalarMartingalePartialSum increment) filtration mu)
    (hbound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ n omega, ‖increment n omega‖ ≤ C) :
    ∀ᵐ omega ∂mu,
      Tendsto (fun n => scalarMartingaleNormalizedSum increment n omega)
        atTop (nhds 0) := by
  apply hallHeyde1980_theorem2_18_conditional_second_moment
    mu filtration increment hmartingale
  · intro n
    rcases hbound with ⟨C, hC, hbound⟩
    apply MemLp.of_bound ?_ C
    · exact ae_of_all mu fun omega => hbound n omega
    · have hintegrable : Integrable (increment n) mu := by
        have hdifference :=
          (hmartingale.integrable (n + 1)).sub (hmartingale.integrable n)
        convert hdifference using 1
        funext omega
        simp [scalarMartingalePartialSum, Finset.sum_range_succ]
      exact hintegrable.aestronglyMeasurable
  rcases hbound with ⟨C, hC, hbound⟩
  have hconditional : ∀ n, ∀ᵐ omega ∂mu,
      0 ≤ hallHeydeConditionalSecondMoment mu filtration increment n omega ∧
      hallHeydeConditionalSecondMoment mu filtration increment n omega ≤ C ^ 2 := by
    intro n
    have hnonnegative : ∀ᵐ omega ∂mu,
        0 ≤ hallHeydeConditionalSecondMoment mu filtration increment n omega := by
      exact MeasureTheory.condExp_nonneg
        (ae_of_all mu fun omega => sq_nonneg |increment n omega|)
    have hinputUpper : ∀ᵐ omega ∂mu,
        |increment n omega| ^ 2 ≤ C ^ 2 := by
      apply ae_of_all
      intro omega
      apply (sq_le_sq₀ (abs_nonneg _) hC).2
      simpa only [Real.norm_eq_abs] using hbound n omega
    have hupper : ∀ᵐ omega ∂mu,
        hallHeydeConditionalSecondMoment mu filtration increment n omega ≤ C ^ 2 := by
      exact MeasureTheory.condExp_le_nonneg_const (sq_nonneg C) hinputUpper
    filter_upwards [hnonnegative, hupper] with omega hnonnegative hupper
    exact ⟨hnonnegative, hupper⟩
  have hconditionalAll : ∀ᵐ omega ∂mu, ∀ n,
      0 ≤ hallHeydeConditionalSecondMoment mu filtration increment n omega ∧
      hallHeydeConditionalSecondMoment mu filtration increment n omega ≤ C ^ 2 := by
    rw [ae_all_iff]
    exact hconditional
  filter_upwards [hconditionalAll] with omega homega
  have hbase : Summable (fun n : ℕ => (((n : ℝ) ^ 2)⁻¹)) :=
    Real.summable_nat_pow_inv.mpr (by omega)
  have hshift : Summable
      (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) ^ 2)⁻¹)) :=
    (summable_nat_add_iff 1).2 hbase
  have hmajor : Summable
      (fun n : ℕ => C ^ 2 * ((((n + 1 : ℕ) : ℝ) ^ 2)⁻¹)) :=
    hshift.mul_left (C ^ 2)
  apply hmajor.of_nonneg_of_le
  · intro n
    exact mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) (homega n).1
  · intro n
    calc
      hallHeydeWeightedSecondMoment mu filtration increment n omega
          ≤ (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ * C ^ 2 := by
            exact mul_le_mul_of_nonneg_left (homega n).2
              (inv_nonneg.mpr (sq_nonneg _))
      _ = C ^ 2 * ((((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by ring

/-- Finite matrix-valued consequence of the scalar Hall--Heyde interface. -/
theorem finiteMatrix_martingale_strongLaw
    {Omega D : Type*} [MeasurableSpace Omega]
    [Fintype D] [DecidableEq D]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ (inferInstance : MeasurableSpace Omega))
    (increment : ℕ → Omega → Matrix D D ℝ)
    (hmartingale : ∀ i j, Martingale
      (scalarMartingalePartialSum (fun n omega => increment n omega i j))
      filtration mu)
    (hL2 : ∀ i j n, MemLp (fun omega => increment n omega i j) 2 mu)
    (hsummable : ∀ i j, ∀ᵐ omega ∂mu,
      Summable (fun n => hallHeydeWeightedSecondMoment mu filtration
        (fun n omega => increment n omega i j) n omega)) :
    ∀ᵐ omega ∂mu,
      Tendsto
        (fun n : ℕ => (n : ℝ)⁻¹ •
          ∑ k ∈ Finset.range n, increment k omega)
        atTop (nhds 0) := by
  have hcoordinate : ∀ i j,
      ∀ᵐ omega ∂mu,
        Tendsto
          (fun n => scalarMartingaleNormalizedSum
            (fun k omega => increment k omega i j) n omega)
          atTop (nhds 0) := by
    intro i j
    exact hallHeyde1980_theorem2_18_conditional_second_moment
      mu filtration (fun n omega => increment n omega i j)
      (hmartingale i j) (hL2 i j) (hsummable i j)
  have hall : ∀ᵐ omega ∂mu, ∀ i j,
      Tendsto
        (fun n => scalarMartingaleNormalizedSum
          (fun k omega => increment k omega i j) n omega)
        atTop (nhds 0) := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro j
    exact hcoordinate i j
  filter_upwards [hall] with omega homega
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  simpa [scalarMartingaleNormalizedSum, scalarMartingalePartialSum,
    Matrix.smul_apply, Matrix.sum_apply] using homega i j

/-- Uniform pointwise coordinate bounds discharge the `L²` premise of the
finite matrix martingale strong law on a probability space. -/
theorem finiteMatrix_martingale_strongLaw_of_uniform_bound
    {Omega D : Type*} [MeasurableSpace Omega]
    [Fintype D] [DecidableEq D]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ (inferInstance : MeasurableSpace Omega))
    (increment : ℕ → Omega → Matrix D D ℝ)
    (hmartingale : ∀ i j, Martingale
      (scalarMartingalePartialSum (fun n omega => increment n omega i j))
      filtration mu)
    (hbound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ n omega i j, ‖increment n omega i j‖ ≤ C) :
    ∀ᵐ omega ∂mu,
      Tendsto
        (fun n : ℕ => (n : ℝ)⁻¹ •
          ∑ k ∈ Finset.range n, increment k omega)
        atTop (nhds 0) := by
  rcases hbound with ⟨C, hC, hbound⟩
  have hcoordinate : ∀ i j,
      ∀ᵐ omega ∂mu,
        Tendsto
          (fun n => scalarMartingaleNormalizedSum
            (fun k omega => increment k omega i j) n omega)
          atTop (nhds 0) := by
    intro i j
    apply hallHeyde1980_theorem2_18_of_uniform_bound
      mu filtration (fun n omega => increment n omega i j) (hmartingale i j)
    exact ⟨C, hC, fun n omega => hbound n omega i j⟩
  have hall : ∀ᵐ omega ∂mu, ∀ i j,
      Tendsto
        (fun n => scalarMartingaleNormalizedSum
          (fun k omega => increment k omega i j) n omega)
        atTop (nhds 0) := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro j
    exact hcoordinate i j
  filter_upwards [hall] with omega homega
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  simpa [scalarMartingaleNormalizedSum, scalarMartingalePartialSum,
    Matrix.smul_apply, Matrix.sum_apply] using homega i j

end

end QubitOracle.Paper
