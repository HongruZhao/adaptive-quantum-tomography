import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic
/-!
# Consistency of an actual coercive ridge least-squares estimator

The parameter space is any finite-dimensional real inner-product space, hence
in particular a finite real-coordinate representation of Hermitian matrices.
Every observation contributes a uniformly coercive frame operator.  We define
the ridge estimate by the inverse accumulated operator, prove its exact normal
equation, and deduce consistency from a vanishing average innovation.

This is a deterministic theorem.  The probabilistic application must prove the
innovation strong law from its actual adaptive Born experiment.  No statistical
source axiom or consistency assumption about the estimate is used here.
-/

namespace QubitOracle.AdaptiveDesign.CoerciveLeastSquares

open Filter
open scoped BigOperators Topology InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A lower quadratic-form bound; self-adjointness is not needed by the
deterministic consistency argument. -/
def Coercive (G : E →ₗ[ℝ] E) (c : ℝ) : Prop :=
  ∀ x, c * ‖x‖ ^ 2 ≤ ⟪x, G x⟫_ℝ

theorem norm_le_residual_div
    (G : E →ₗ[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hG : Coercive G c) (x r : E) (hequation : G x = r) :
    ‖x‖ ≤ ‖r‖ / c := by
  have hquadratic := hG x
  rw [hequation] at hquadratic
  have hcs := real_inner_le_norm x r
  by_cases hx : ‖x‖ = 0
  · rw [hx]
    positivity
  · have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx)
    apply (le_div_iff₀ hc).2
    nlinarith

theorem injective_of_coercive
    (G : E →ₗ[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hG : Coercive G c) : Function.Injective G := by
  intro x y hxy
  have hzero : G (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have hbound := norm_le_residual_div G c hc hG (x - y) 0 hzero
  have hnorm : ‖x - y‖ = 0 := by
    have hbound' : ‖x - y‖ ≤ 0 := by simpa using hbound
    exact le_antisymm hbound' (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- Accumulated design operator with a positive ridge. -/
def ridgeGram (frame : ℕ → E →ₗ[ℝ] E) (regularization : ℝ)
    (n : ℕ) : E →ₗ[ℝ] E :=
  regularization • LinearMap.id + ∑ t ∈ Finset.range n, frame t

theorem ridgeGram_apply
    (frame : ℕ → E →ₗ[ℝ] E) (regularization : ℝ) (n : ℕ) (x : E) :
    ridgeGram frame regularization n x =
      regularization • x + ∑ t ∈ Finset.range n, frame t x := by
  simp [ridgeGram]

theorem ridgeGram_coercive
    (frame : ℕ → E →ₗ[ℝ] E) (regularization κ : ℝ)
    (hframe : ∀ t, Coercive (frame t) κ) (n : ℕ) :
    Coercive (ridgeGram frame regularization n) (regularization + n * κ) := by
  intro x
  have hsum := Finset.sum_le_sum (s := Finset.range n)
    (fun t _ => hframe t x)
  rw [ridgeGram_apply, inner_add_right, inner_smul_right, inner_sum]
  simp only [real_inner_self_eq_norm_sq]
  have hsimplified :
      (n : ℝ) * (κ * ‖x‖ ^ 2) ≤
        ∑ t ∈ Finset.range n, ⟪x, frame t x⟫_ℝ := by
    simpa using hsum
  nlinarith

variable [FiniteDimensional ℝ E]

/-- The inverse accumulated operator exists by coercivity and finite dimension. -/
def ridgeEquivalence
    (frame : ℕ → E →ₗ[ℝ] E) (regularization κ : ℝ)
    (hregularization : 0 < regularization) (hκ : 0 ≤ κ)
    (hframe : ∀ t, Coercive (frame t) κ) (n : ℕ) : E ≃ₗ[ℝ] E :=
  LinearEquiv.ofInjectiveEndo (ridgeGram frame regularization n)
    (injective_of_coercive _ (regularization + n * κ)
      (by positivity) (ridgeGram_coercive frame regularization κ hframe n))

/-- The actual ridge estimate, formed from every response observed so far. -/
def ridgeEstimate
    (frame : ℕ → E →ₗ[ℝ] E) (response : ℕ → E)
    (regularization κ : ℝ) (hregularization : 0 < regularization)
    (hκ : 0 ≤ κ) (hframe : ∀ t, Coercive (frame t) κ) (n : ℕ) : E :=
  (ridgeEquivalence frame regularization κ hregularization hκ hframe n).symm
    (∑ t ∈ Finset.range n, response t)

theorem ridgeEstimate_normalEquation
    (frame : ℕ → E →ₗ[ℝ] E) (response : ℕ → E)
    (regularization κ : ℝ) (hregularization : 0 < regularization)
    (hκ : 0 ≤ κ) (hframe : ∀ t, Coercive (frame t) κ) (n : ℕ) :
    ridgeGram frame regularization n
        (ridgeEstimate frame response regularization κ hregularization hκ hframe n) =
      ∑ t ∈ Finset.range n, response t := by
  exact (ridgeEquivalence frame regularization κ hregularization hκ hframe n).apply_symm_apply _

/-- The response innovation relative to the true parameter. In the Born
application the conditional expectation of this quantity is zero. -/
def innovation (frame : ℕ → E →ₗ[ℝ] E) (response : ℕ → E)
    (truth : E) (t : ℕ) : E := response t - frame t truth

theorem ridgeEstimate_errorEquation
    (frame : ℕ → E →ₗ[ℝ] E) (response : ℕ → E) (truth : E)
    (regularization κ : ℝ) (hregularization : 0 < regularization)
    (hκ : 0 ≤ κ) (hframe : ∀ t, Coercive (frame t) κ) (n : ℕ) :
    ridgeGram frame regularization n
        (ridgeEstimate frame response regularization κ hregularization hκ hframe n - truth) =
      (∑ t ∈ Finset.range n, innovation frame response truth t) -
        regularization • truth := by
  rw [map_sub, ridgeEstimate_normalEquation, ridgeGram_apply]
  simp only [innovation, Finset.sum_sub_distrib]
  abel

theorem ridgeEstimate_error_bound
    (frame : ℕ → E →ₗ[ℝ] E) (response : ℕ → E) (truth : E)
    (regularization κ : ℝ) (hregularization : 0 < regularization)
    (hκ : 0 ≤ κ) (hframe : ∀ t, Coercive (frame t) κ) (n : ℕ) :
    ‖ridgeEstimate frame response regularization κ hregularization hκ hframe n - truth‖ ≤
      ‖(∑ t ∈ Finset.range n, innovation frame response truth t) -
        regularization • truth‖ / (regularization + n * κ) := by
  exact norm_le_residual_div _ _ (by positivity)
    (ridgeGram_coercive frame regularization κ hframe n) _ _
    (ridgeEstimate_errorEquation frame response truth regularization κ
      hregularization hκ hframe n)

/-- A vanishing average innovation implies consistency of the explicitly
defined inverse-Gram ridge estimate. The frame may change at every shot and
need not have a limit. -/
theorem ridgeEstimate_tendsto_of_averageInnovation
    (frame : ℕ → E →ₗ[ℝ] E) (response : ℕ → E) (truth : E)
    (regularization κ : ℝ) (hregularization : 0 < regularization)
    (hκ : 0 < κ) (hframe : ∀ t, Coercive (frame t) κ)
    (haverage : Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ •
        ∑ t ∈ Finset.range n, innovation frame response truth t)
      atTop (𝓝 0)) :
    Tendsto
      (ridgeEstimate frame response regularization κ hregularization hκ.le hframe)
      atTop (𝓝 truth) := by
  have hridge : Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ • (regularization • truth)) atTop (𝓝 (0 : E)) := by
    simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const
      (regularization • truth)
  have hresidual : Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ •
        ((∑ t ∈ Finset.range n, innovation frame response truth t) -
          regularization • truth)) atTop (𝓝 (0 : E)) := by
    simpa only [smul_sub, sub_zero] using haverage.sub hridge
  have hboundLimit : Tendsto
      (fun n : ℕ => ‖(n : ℝ)⁻¹ •
        ((∑ t ∈ Finset.range n, innovation frame response truth t) -
          regularization • truth)‖ / κ) atTop (𝓝 0) := by
    simpa using hresidual.norm.div_const κ
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _)) _ hboundLimit
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hcoercive : Coercive (ridgeGram frame regularization n) ((n : ℝ) * κ) := by
    intro x
    have hfull := ridgeGram_coercive frame regularization κ hframe n x
    nlinarith [sq_nonneg ‖x‖]
  have hbound := norm_le_residual_div _ _ (mul_pos hnpos hκ) hcoercive _ _
    (ridgeEstimate_errorEquation frame response truth regularization κ
      hregularization hκ.le hframe n)
  calc
    ‖ridgeEstimate frame response regularization κ hregularization hκ.le hframe n - truth‖ ≤
        ‖(∑ t ∈ Finset.range n, innovation frame response truth t) -
          regularization • truth‖ / ((n : ℝ) * κ) := hbound
    _ = ‖(n : ℝ)⁻¹ •
        ((∑ t ∈ Finset.range n, innovation frame response truth t) -
          regularization • truth)‖ / κ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hnpos.le)]
      field_simp

end

end QubitOracle.AdaptiveDesign.CoerciveLeastSquares
