import QubitOracle.Paper.SequentialHessian
import QubitOracle.Paper.RetainedTailSet

/-!
# Exact protocol definitions used by the paper

This module transcribes the controller equations and the two terminal-rate
conditions.  The data are indexed from one, as in the manuscript.  No
consistency, concentration, or asymptotic-normality assertion is bundled into
these definitions.
-/

namespace QubitOracle.Paper

open scoped BigOperators
open Filter

noncomputable section

/-- The affine Born response `c_m(y) + a_m(y)^T theta`. -/
def paperAffineBornProbability
    {M Y D : Type*} [Fintype D]
    (c : M -> Y -> Real) (a : M -> Y -> D -> Real)
    (theta : D -> Real) (m : M) (y : Y) : Real :=
  c m y + dotProduct (a m y) theta

/-- The setting Gram matrix `G_m = sum_y a_m(y) a_m(y)^T`. -/
def paperSettingGram
    {M Y D : Type*} [Fintype Y]
    (a : M -> Y -> D -> Real) (m : M) : Matrix D D Real :=
  ∑ y, Matrix.vecMulVec (a m y) (a m y)

/-- The regularized controller Gram matrix through shot `n`. -/
def paperControllerGram
    {M Y D : Type*} [Fintype Y] [Fintype D] [DecidableEq D]
    (lambda : Real) (a : M -> Y -> D -> Real)
    (setting : Nat -> M) (n : Nat) : Matrix D D Real :=
  lambda • (1 : Matrix D D Real) +
    ∑ i ∈ Finset.Icc 1 n, paperSettingGram a (setting i)

/-- The centered affine response accumulated by recursive least squares. -/
def paperControllerResponse
    {M Y D : Type*} [Fintype Y] [DecidableEq Y]
    (c : M -> Y -> Real) (a : M -> Y -> D -> Real)
    (setting : Nat -> M) (outcome : Nat -> Y) (n : Nat) : D -> Real :=
  fun j =>
    ∑ i ∈ Finset.Icc 1 n, ∑ y,
      a (setting i) y j *
        ((if outcome i = y then (1 : Real) else 0) - c (setting i) y)

/-- The paper's recursive least-squares controller. -/
def paperRecursiveLS
    {M Y D : Type*} [Fintype Y] [DecidableEq Y]
    [Fintype D] [DecidableEq D]
    (lambda : Real) (c : M -> Y -> Real)
    (a : M -> Y -> D -> Real) (setting : Nat -> M)
    (outcome : Nat -> Y) (n : Nat) : D -> Real :=
  ((paperControllerGram lambda a setting n)⁻¹).mulVec
    (paperControllerResponse c a setting outcome n)

/-- One martingale regression-noise increment at the true parameter. -/
def paperRegressionNoise
    {M Y D : Type*} [Fintype Y] [DecidableEq Y] [Fintype D]
    (c : M -> Y -> Real) (a : M -> Y -> D -> Real)
    (setting : Nat -> M) (outcome : Nat -> Y)
    (thetaStar : D -> Real) (i : Nat) : D -> Real :=
  fun j => ∑ y,
    a (setting i) y j *
      ((if outcome i = y then (1 : Real) else 0) -
        paperAffineBornProbability c a thetaStar (setting i) y)

/-- The terminal localization condition `sqrt(n) log(n) / E_n -> 0`. -/
def TerminalExplorationRate (expectedExploration : Nat -> Real) : Prop :=
  Tendsto
    (fun n : Nat =>
      Real.sqrt (n : Real) * Real.log (n : Real) / expectedExploration n)
    atTop (nhds 0)

/-- Eventual regular batch growth `m_k <= C_B N_{k-1}`. -/
def RegularBatchGrowth (batchSize cumulativeSize : Nat -> Nat) : Prop :=
  ∃ C_B : Real, ∀ᶠ k : Nat in atTop,
    (batchSize k : Real) <= C_B * (cumulativeSize (k - 1) : Real)

namespace Label

/-- Main-text equation `eq:affine_born_controller`. -/
theorem eq_affine_born_controller
    {M Y D : Type*} [Fintype Y] [Fintype D] [DecidableEq D]
    (lambda : Real) (c : M -> Y -> Real)
    (a : M -> Y -> D -> Real) (theta : D -> Real)
    (setting : Nat -> M) (n : Nat) (m : M) (y : Y) :
    paperAffineBornProbability c a theta m y =
        c m y + dotProduct (a m y) theta ∧
      paperControllerGram lambda a setting n =
        lambda • (1 : Matrix D D Real) +
          ∑ i ∈ Finset.Icc 1 n,
            ∑ z, Matrix.vecMulVec (a (setting i) z) (a (setting i) z) := by
  constructor <;> rfl

/-- Main-text equation `eq:general_recursive_LS`. -/
theorem eq_general_recursive_LS
    {M Y D : Type*} [Fintype Y] [DecidableEq Y]
    [Fintype D] [DecidableEq D]
    (lambda : Real) (c : M -> Y -> Real)
    (a : M -> Y -> D -> Real) (setting : Nat -> M)
    (outcome : Nat -> Y) (n : Nat) :
    paperRecursiveLS lambda c a setting outcome n =
      ((paperControllerGram lambda a setting n)⁻¹).mulVec
        (fun j =>
          ∑ i ∈ Finset.Icc 1 n, ∑ y,
            a (setting i) y j *
              ((if outcome i = y then (1 : Real) else 0) -
                c (setting i) y)) :=
  rfl

/-- Main-text equation `eq:terminal_exploration_rate`. -/
theorem eq_terminal_exploration_rate (expectedExploration : Nat -> Real) :
    TerminalExplorationRate expectedExploration ↔
      Tendsto
        (fun n : Nat =>
          Real.sqrt (n : Real) * Real.log (n : Real) /
            expectedExploration n)
        atTop (nhds 0) :=
  Iff.rfl

/-- Supplement equation `eq:SI_terminal_rate`. -/
theorem eq_SI_terminal_rate (expectedExploration : Nat -> Real) :
    TerminalExplorationRate expectedExploration ↔
      Tendsto
        (fun n : Nat =>
          Real.sqrt (n : Real) * Real.log (n : Real) /
            expectedExploration n)
        atTop (nhds 0) :=
  Iff.rfl

/-- Supplement equation `eq:SI_batch_growth`. -/
theorem eq_SI_batch_growth (batchSize cumulativeSize : Nat -> Nat) :
    RegularBatchGrowth batchSize cumulativeSize ↔
      ∃ C_B : Real, ∀ᶠ k : Nat in atTop,
        (batchSize k : Real) <=
          C_B * (cumulativeSize (k - 1) : Real) :=
  Iff.rfl

/-- Supplement equation `eq:SI_RLS`. -/
theorem eq_SI_RLS
    {M Y D : Type*} [Fintype Y] [DecidableEq Y]
    [Fintype D] [DecidableEq D]
    (lambda : Real) (c : M -> Y -> Real)
    (a : M -> Y -> D -> Real) (setting : Nat -> M)
    (outcome : Nat -> Y) (n : Nat) :
    paperControllerGram lambda a setting n =
        lambda • (1 : Matrix D D Real) +
          ∑ i ∈ Finset.Icc 1 n, paperSettingGram a (setting i) ∧
      paperRecursiveLS lambda c a setting outcome n =
        ((paperControllerGram lambda a setting n)⁻¹).mulVec
          (fun j =>
            ∑ i ∈ Finset.Icc 1 n, ∑ y,
              a (setting i) y j *
                ((if outcome i = y then (1 : Real) else 0) -
                  c (setting i) y)) := by
  constructor <;> rfl

/-- Supplement equation `eq:SI_regression_noise`. -/
theorem eq_SI_regression_noise
    {M Y D : Type*} [Fintype Y] [DecidableEq Y] [Fintype D]
    (c : M -> Y -> Real) (a : M -> Y -> D -> Real)
    (setting : Nat -> M) (outcome : Nat -> Y)
    (thetaStar : D -> Real) (i : Nat) :
    paperRegressionNoise c a setting outcome thetaStar i =
      fun j => ∑ y,
        a (setting i) y j *
          ((if outcome i = y then (1 : Real) else 0) -
            paperAffineBornProbability c a thetaStar (setting i) y) :=
  rfl

end Label

end

end QubitOracle.Paper
