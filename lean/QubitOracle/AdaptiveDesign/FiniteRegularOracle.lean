import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
/-!
# Finite regular classical experiments and the weighted oracle inequality

Regularity here is an explicit derivative condition on probability masses,
not a Cramer--Rao conclusion supplied as an assumption. A finite record may
encode every setting and outcome of an adaptive experiment. Probabilities
may vanish: nonnegativity forces their derivatives to vanish there.

The loss is represented by a factor R, so it is ||R (T-theta)||^2.
The score factor B allows quantum-information whitening. The principal
inequality follows directly from the score identity and finite Cauchy--Schwarz.
-/

namespace QubitOracle.AdaptiveDesign.FiniteRegularOracle

open Filter
open scoped BigOperators Topology
noncomputable section

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]

def shift (theta : ι → ℝ) (j : ι) (t : ℝ) : ι → ℝ :=
  theta + t • Pi.single j 1

/-- An honest finite probability model, with its coordinate derivatives at
the fixed truth. A model defined only on an open neighbourhood can first
be extended by any fixed probability law outside that neighbourhood. -/
structure RegularModel (ι Ω : Type*) [Fintype ι] [DecidableEq ι] [Fintype Ω] where
  theta : ι → ℝ
  mass : (ι → ℝ) → Ω → ℝ
  nonneg : ∀ theta w, 0 ≤ mass theta w
  total : ∀ theta, ∑ w, mass theta w = 1
  derivative : Ω → ι → ℝ
  hasDerivative : ∀ w j, HasDerivAt
    (fun t => mass (shift theta j t) w) (derivative w j) 0

namespace RegularModel

/-- Coordinate regularity on a neighbourhood is sufficient: use the
truth's probability law outside that neighbourhood. The extension has
exactly the supplied coordinate derivatives at the truth. -/
def ofNeighborhood (theta : ι → ℝ) (U : Set (ι → ℝ))
    (hU : U ∈ 𝓝 theta) (mass : (ι → ℝ) → Ω → ℝ)
    (hnonneg : ∀ theta' ∈ U, ∀ w, 0 ≤ mass theta' w)
    (htotal : ∀ theta' ∈ U, ∑ w, mass theta' w = 1)
    (derivative : Ω → ι → ℝ)
    (hderivative : ∀ w j, HasDerivAt
      (fun t => mass (shift theta j t) w) (derivative w j) 0) :
    RegularModel ι Ω := by
  classical
  exact {
    theta := theta
    mass := fun theta' w => if theta' ∈ U then mass theta' w else mass theta w
    nonneg := by
      intro theta' w
      split_ifs with h
      · exact hnonneg theta' h w
      · exact hnonneg theta (mem_of_mem_nhds hU) w
    total := by
      intro theta'
      by_cases h : theta' ∈ U
      · simpa only [if_pos h] using htotal theta' h
      · simpa only [if_neg h] using htotal theta (mem_of_mem_nhds hU)
    derivative := derivative
    hasDerivative := by
      intro w j
      have hc : Continuous (fun t : ℝ => shift theta j t) :=
        continuous_const.add (continuous_id.smul continuous_const)
      have ht : Tendsto (fun t : ℝ => shift theta j t) (𝓝 0) (𝓝 theta) := by
        simpa only [shift, zero_smul, add_zero] using hc.tendsto 0
      apply (hderivative w j).congr_of_eventuallyEq
      exact (ht.eventually hU).mono (fun t ht => if_pos ht)
  }

variable (P : RegularModel ι Ω)

def score (w : Ω) (j : ι) : ℝ := P.derivative w j / P.mass P.theta w

def expectation (f : Ω → ℝ) : ℝ := ∑ w, P.mass P.theta w * f w

def mean (T : Ω → ι → ℝ) (theta : ι → ℝ) (i : ι) : ℝ :=
  ∑ w, P.mass theta w * T w i

/-- Value and Jacobian conditions for local unbiasedness, stated through
actual derivatives of the finite expectation. -/
def LocallyUnbiased (T : Ω → ι → ℝ) : Prop :=
  (∀ i, P.mean T P.theta i = P.theta i) ∧
  ∀ i j, HasDerivAt (fun t => P.mean T (shift P.theta j t) i)
    (if i = j then 1 else 0) 0

theorem derivative_eq_zero_of_mass_eq_zero (w : Ω) (j : ι)
    (hz : P.mass P.theta w = 0) : P.derivative w j = 0 := by
  have hm : IsLocalMin (fun t : ℝ => P.mass (shift P.theta j t) w) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    simpa [shift, hz] using P.nonneg (shift P.theta j t) w
  exact hm.hasDerivAt_eq_zero (P.hasDerivative w j)

theorem mass_mul_score (w : Ω) (j : ι) :
    P.mass P.theta w * P.score w j = P.derivative w j := by
  by_cases hz : P.mass P.theta w = 0
  · simp [score, hz, P.derivative_eq_zero_of_mass_eq_zero w j hz]
  · unfold score
    field_simp

theorem derivative_sum (j : ι) : ∑ w, P.derivative w j = 0 := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun w _ => P.hasDerivative w j)
  have h' : HasDerivAt (fun _ : ℝ => (1 : ℝ)) (∑ w, P.derivative w j) 0 := by
    simpa only [P.total] using h
  exact h'.unique (hasDerivAt_const 0 (1 : ℝ))

theorem score_centered (j : ι) : P.expectation (fun w => P.score w j) = 0 := by
  simp only [expectation, P.mass_mul_score]
  exact P.derivative_sum j

theorem score_identity (T : Ω → ι → ℝ) (hT : P.LocallyUnbiased T) (i j : ι) :
    P.expectation (fun w => (T w i - P.theta i) * P.score w j) =
      if i = j then 1 else 0 := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ)
    (fun w _ => (P.hasDerivative w j).mul_const (T w i))
  have hd' : (∑ w, P.derivative w j * T w i) =
      if i = j then 1 else 0 := hd.unique (hT.2 i j)
  unfold expectation
  calc
    _ = ∑ w, (P.derivative w j * T w i - P.theta i * P.derivative w j) := by
      apply Finset.sum_congr rfl
      intro w _
      rw [show P.mass P.theta w * ((T w i - P.theta i) * P.score w j) =
        (T w i - P.theta i) * (P.mass P.theta w * P.score w j) by ring,
        P.mass_mul_score]
      ring
    _ = (∑ w, P.derivative w j * T w i) - P.theta i * (∑ w, P.derivative w j) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = _ := by rw [P.derivative_sum, hd']; ring

def factorRisk (R : Matrix ι ι ℝ) (T : Ω → ι → ℝ) : ℝ :=
  P.expectation (fun w => ∑ i, (∑ j, R i j * (T w j - P.theta j)) ^ 2)

def scoreEnergy (B : Matrix ι ι ℝ) : ℝ :=
  P.expectation (fun w => ∑ i, (∑ j, B i j * P.score w j) ^ 2)

theorem factorRisk_nonneg (R : Matrix ι ι ℝ) (T : Ω → ι → ℝ) :
    0 ≤ P.factorRisk R T := by
  apply Finset.sum_nonneg
  intro w _
  exact mul_nonneg (P.nonneg _ _) (Finset.sum_nonneg fun i _ => sq_nonneg _)

theorem transformed_score_identity (R B : Matrix ι ι ℝ)
    (T : Ω → ι → ℝ) (hT : P.LocallyUnbiased T) :
    P.expectation (fun w => ∑ i,
      (∑ j, R i j * (T w j - P.theta j)) *
      (∑ k, B i k * P.score w k)) = Matrix.trace (R * B.transpose) := by
  unfold expectation Matrix.trace
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  calc
    _ = ∑ j, ∑ k, R i k * B i j *
        P.expectation (fun w => (T w k - P.theta k) * P.score w j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      simp only [expectation, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      ring
    _ = _ := by
      simp [P.score_identity T hT, Matrix.mul_apply, Matrix.transpose_apply]

/-- Finite weighted Cauchy--Schwarz gives the full statistical oracle
inequality; no inverse-information or Cramer--Rao hypothesis is assumed. -/
theorem weighted_score_bound (R B : Matrix ι ι ℝ)
    (T : Ω → ι → ℝ) (hT : P.LocallyUnbiased T) :
    (Matrix.trace (R * B.transpose)) ^ 2 ≤ P.factorRisk R T * P.scoreEnergy B := by
  let f : Ω × ι → ℝ := fun wi => Real.sqrt (P.mass P.theta wi.1) *
    (∑ j, R wi.2 j * (T wi.1 j - P.theta j))
  let g : Ω × ι → ℝ := fun wi => Real.sqrt (P.mass P.theta wi.1) *
    (∑ j, B wi.2 j * P.score wi.1 j)
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  have hfg : (∑ wi, f wi * g wi) = Matrix.trace (R * B.transpose) := by
    rw [Fintype.sum_prod_type]
    calc
      _ = P.expectation (fun w => ∑ i,
          (∑ j, R i j * (T w j - P.theta j)) * (∑ k, B i k * P.score w k)) := by
        unfold expectation
        apply Finset.sum_congr rfl
        intro w _
        conv_rhs => rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [f, g]
        rw [show Real.sqrt (P.mass P.theta w) * _ *
            (Real.sqrt (P.mass P.theta w) * _) =
          (Real.sqrt (P.mass P.theta w))^2 *
            (∑ j, R i j * (T w j - P.theta j)) *
            (∑ k, B i k * P.score w k) by ring,
          Real.sq_sqrt (P.nonneg _ _)]
        ring
      _ = _ := P.transformed_score_identity R B T hT
  have hf : (∑ wi, f wi ^ 2) = P.factorRisk R T := by
    rw [Fintype.sum_prod_type]
    unfold factorRisk expectation
    apply Finset.sum_congr rfl
    intro w _
    conv_rhs => rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [f]
    rw [mul_pow, Real.sq_sqrt (P.nonneg _ _)]
  have hg : (∑ wi, g wi ^ 2) = P.scoreEnergy B := by
    rw [Fintype.sum_prod_type]
    unfold scoreEnergy expectation
    apply Finset.sum_congr rfl
    intro w _
    conv_rhs => rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [g]
    rw [mul_pow, Real.sq_sqrt (P.nonneg _ _)]
  simpa only [hfg, hf, hg] using h

/-- A score-information budget turns the statistical inequality into the
sample-size scaled lower bound. R and B are arbitrary real matrices. -/
theorem oracle_bound_of_information_budget (R B : Matrix ι ι ℝ)
    (T : Ω → ι → ℝ) (hT : P.LocallyUnbiased T)
    (n budget : ℝ) (hbudget : 0 < budget)
    (hInfo : P.scoreEnergy B ≤ n * budget) :
    (Matrix.trace (R * B.transpose))^2 / budget ≤ n * P.factorRisk R T := by
  apply (div_le_iff₀ hbudget).2
  calc
    _ ≤ P.factorRisk R T * P.scoreEnergy B := P.weighted_score_bound R B T hT
    _ ≤ P.factorRisk R T * (n * budget) :=
      mul_le_mul_of_nonneg_left hInfo (P.factorRisk_nonneg R T)
    _ = _ := by ring

end RegularModel
end
end QubitOracle.AdaptiveDesign.FiniteRegularOracle
