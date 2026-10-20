import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.LinearAlgebra.Matrix.StdBasis

/-!
# Projected RLS and Fisher-information convergence for pure multilevel states

This module is deterministic and pathwise.  The Hilbert dimension is `D`, the
sample index is `n`, and the real pure-state tangent dimension is
`2 * (D - 1)`.  A Davis--Kahan-style stability estimate is supplied as a
hypothesis rather than imported from an external theorem.  No probabilistic or
literature axiom is used.

The final section separates the optional stochastic ingredient: if the
realized-minus-predictable empirical Fisher average is known to vanish along a
path, then the realized empirical average has the same limit.
-/

namespace QubitOracle.Paper
namespace PureMultilevelProjectedRLSInformationConvergence

noncomputable section

open Filter
open scoped BigOperators Topology

/-- Real tangent-coordinate count for a pure state in Hilbert dimension `D`. -/
def pureTangentDimension (D : ℕ) : ℕ := 2 * (D - 1)

/-- Entrywise convergence of a sequence of finite real matrices. -/
def MatrixEntrywiseTendsto {m : ℕ}
    (A : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (L : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  ∀ i j, Tendsto (fun n => A n i j) atTop (nhds (L i j))

/-- The leading-projector estimate associated with a raw RLS path. -/
def projectedRLSPath {Raw Projector : Type*}
    (leadingProjector : Raw → Projector) (raw : ℕ → Raw) : ℕ → Projector :=
  fun n => leadingProjector (raw n)

/-- Raw RLS convergence plus a pathwise Davis--Kahan bound implies convergence
of the leading-projector estimate.  The theorem is agnostic about the chosen
finite-dimensional matrix norm, provided it forms a normed real vector space. -/
theorem projectedRLS_tendsto_of_davisKahan
    {Raw Projector : Type*}
    [NormedAddCommGroup Raw] [NormedSpace ℝ Raw]
    [NormedAddCommGroup Projector] [NormedSpace ℝ Projector]
    (raw : ℕ → Raw) (rawTruth : Raw)
    (leadingProjector : Raw → Projector) (truthProjector : Projector)
    (C : ℝ) (_hC : 0 ≤ C)
    (hraw : Tendsto raw atTop (nhds rawTruth))
    (hDK : ∀ n,
      ‖leadingProjector (raw n) - truthProjector‖ ≤
        C * ‖raw n - rawTruth‖) :
    Tendsto (projectedRLSPath leadingProjector raw) atTop
      (nhds truthProjector) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hrawZero :
      Tendsto (fun n => ‖raw n - rawTruth‖) atTop (nhds 0) := by
    simpa using (tendsto_iff_norm_sub_tendsto_zero.mp hraw)
  have hupper :
      Tendsto (fun n => C * ‖raw n - rawTruth‖) atTop (nhds 0) := by
    simpa using hrawZero.const_mul C
  exact squeeze_zero'
    (Eventually.of_forall fun n => norm_nonneg _)
    (Eventually.of_forall hDK) hupper

/-- A pointwise local-Lipschitz Fisher controller transfers projected-state
convergence to one-step exploitation Fisher convergence. -/
theorem canonicalController_tendsto_of_localLipschitz
    {D : ℕ} {Projector : Type*}
    [NormedAddCommGroup Projector] [NormedSpace ℝ Projector]
    (projected : ℕ → Projector) (truthProjector : Projector)
    (canonicalFisher : Projector →
      Matrix (Fin (pureTangentDimension D))
        (Fin (pureTangentDimension D)) ℝ)
    (L : Fin (pureTangentDimension D) →
      Fin (pureTangentDimension D) → ℝ)
    (_hL : ∀ i j, 0 ≤ L i j)
    (hprojected : Tendsto projected atTop (nhds truthProjector))
    (hlocal : ∀ i j, ∀ᶠ n in atTop,
      |canonicalFisher (projected n) i j -
          canonicalFisher truthProjector i j| ≤
        L i j * ‖projected n - truthProjector‖) :
    MatrixEntrywiseTendsto (fun n => canonicalFisher (projected n))
      (canonicalFisher truthProjector) := by
  intro i j
  rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_abs_tendsto_zero]
  have hprojectedZero :
      Tendsto (fun n => ‖projected n - truthProjector‖) atTop (nhds 0) := by
    simpa using (tendsto_iff_norm_sub_tendsto_zero.mp hprojected)
  have hupper : Tendsto
      (fun n => L i j * ‖projected n - truthProjector‖)
      atTop (nhds 0) := by
    simpa using hprojectedZero.const_mul (L i j)
  exact squeeze_zero'
    (Eventually.of_forall fun n => abs_nonneg _)
    (hlocal i j) hupper

/-- Predictable one-step Fisher information obtained by mixing exploitation
with an informationally complete exploration design of weight `epsilon n`. -/
def predictableFisher {m : ℕ}
    (epsilon : ℕ → ℝ)
    (exploitation exploration : ℕ → Matrix (Fin m) (Fin m) ℝ) :
    ℕ → Matrix (Fin m) (Fin m) ℝ :=
  fun n i j =>
    (1 - epsilon n) * exploitation n i j +
      epsilon n * exploration n i j

/-- Vanishing exploration preserves the exploitation Fisher limit whenever
the exploration matrices are uniformly entrywise bounded around the target. -/
theorem predictableFisher_tendsto_of_vanishing_exploration
    {m : ℕ}
    (epsilon : ℕ → ℝ)
    (exploitation exploration : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (target : Matrix (Fin m) (Fin m) ℝ)
    (B : Fin m → Fin m → ℝ)
    (hB : ∀ i j, 0 ≤ B i j)
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hexploitation : MatrixEntrywiseTendsto exploitation target)
    (hexplorationBound : ∀ n i j,
      |exploration n i j - target i j| ≤ B i j) :
    MatrixEntrywiseTendsto
      (predictableFisher epsilon exploitation exploration) target := by
  intro i j
  have hcontrolZero : Tendsto
      (fun n => exploitation n i j - target i j) atTop (nhds 0) :=
    by
      simpa using (hexploitation i j).sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => target i j)
          atTop (nhds (target i j)))
  have honeMinus : Tendsto (fun n => 1 - epsilon n) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hepsilon
  have hcontrolled : Tendsto
      (fun n => (1 - epsilon n) *
        (exploitation n i j - target i j)) atTop (nhds 0) := by
    simpa using honeMinus.mul hcontrolZero
  have hepsilonAbs : Tendsto (fun n => |epsilon n|) atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero] at hepsilon
    change Tendsto (abs ∘ epsilon) atTop (nhds 0)
    exact hepsilon
  have hexplorationZero : Tendsto
      (fun n => epsilon n * (exploration n i j - target i j))
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    have hupper : Tendsto (fun n => |epsilon n| * B i j)
        atTop (nhds 0) := by
      simpa using hepsilonAbs.mul_const (B i j)
    exact squeeze_zero'
      (Eventually.of_forall fun n => abs_nonneg _)
      (Eventually.of_forall fun n => by
        change |epsilon n * (exploration n i j - target i j)| ≤
          |epsilon n| * B i j
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (hexplorationBound n i j) (abs_nonneg _))
      hupper
  have hsum := hcontrolled.add hexplorationZero
  rw [← tendsto_sub_nhds_zero_iff]
  simpa only [zero_add] using hsum.congr'
    (Eventually.of_forall fun n => by
      simp only [predictableFisher]
      ring)

/-- Cesaro average of a sequence of finite Fisher matrices. -/
def fisherCesaroAverage {m : ℕ}
    (information : ℕ → Matrix (Fin m) (Fin m) ℝ) :
    ℕ → Matrix (Fin m) (Fin m) ℝ :=
  fun n i j => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, information k i j

/-- Entrywise convergence of one-step predictable information implies
entrywise convergence of its Cesaro average. -/
theorem fisherCesaroAverage_tendsto
    {m : ℕ}
    (information : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (target : Matrix (Fin m) (Fin m) ℝ)
    (h : MatrixEntrywiseTendsto information target) :
    MatrixEntrywiseTendsto (fisherCesaroAverage information) target := by
  intro i j
  simpa [fisherCesaroAverage] using (h i j).cesaro

/-- One canonical cyclic row: the rank-one Fisher matrix of one tangent
coordinate direction. -/
def canonicalCyclicRowFisher (D : ℕ)
    (row : Fin (pureTangentDimension D)) :
    Matrix (Fin (pureTangentDimension D))
      (Fin (pureTangentDimension D)) ℝ :=
  fun i j => if i = row ∧ j = row then 1 else 0

/-- Uniform average of the `2(D-1)` canonical cyclic rows. -/
def canonicalCyclicAverageFisher (D : ℕ) :
    Matrix (Fin (pureTangentDimension D))
      (Fin (pureTangentDimension D)) ℝ :=
  fun i j =>
    (pureTangentDimension D : ℝ)⁻¹ *
      ∑ row : Fin (pureTangentDimension D),
        canonicalCyclicRowFisher D row i j

/-- The canonical target written as identity divided by the number of rows. -/
def canonicalCyclicFisherTarget (D : ℕ) :
    Matrix (Fin (pureTangentDimension D))
      (Fin (pureTangentDimension D)) ℝ :=
  (pureTangentDimension D : ℝ)⁻¹ • 1

/-- Exact finite-dimensional identity: the canonical cyclic
`2(D-1)`-row Fisher target is `I / (2(D-1))`. -/
theorem canonicalCyclicAverageFisher_eq_identity_div
    (D : ℕ) (_hD : 1 < D) :
    canonicalCyclicAverageFisher D = canonicalCyclicFisherTarget D := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [canonicalCyclicAverageFisher, canonicalCyclicRowFisher,
      canonicalCyclicFisherTarget]
  · have hji : j ≠ i := fun h => hij h.symm
    simp [canonicalCyclicAverageFisher, canonicalCyclicRowFisher,
      canonicalCyclicFisherTarget, hij, hji]

/-- Complete deterministic/pathwise pipeline for a `D`-level pure state:
raw RLS consistency, Davis--Kahan leading-projector stability, a local
Lipschitz canonical controller, and vanishing bounded exploration imply
one-step predictable Fisher convergence and convergence of its Cesaro average
to an abstract supplied target `Istar`. -/
theorem projectedRLS_predictableFisher_and_cesaro_tendsto
    (D : ℕ)
    {Raw Projector : Type*}
    [NormedAddCommGroup Raw] [NormedSpace ℝ Raw]
    [NormedAddCommGroup Projector] [NormedSpace ℝ Projector]
    (raw : ℕ → Raw) (rawTruth : Raw)
    (leadingProjector : Raw → Projector) (truthProjector : Projector)
    (C : ℝ) (hC : 0 ≤ C)
    (hraw : Tendsto raw atTop (nhds rawTruth))
    (hDK : ∀ n,
      ‖leadingProjector (raw n) - truthProjector‖ ≤
        C * ‖raw n - rawTruth‖)
    (canonicalFisher : Projector →
      Matrix (Fin (pureTangentDimension D))
        (Fin (pureTangentDimension D)) ℝ)
    (L : Fin (pureTangentDimension D) →
      Fin (pureTangentDimension D) → ℝ)
    (hL : ∀ i j, 0 ≤ L i j)
    (Istar : Matrix (Fin (pureTangentDimension D))
      (Fin (pureTangentDimension D)) ℝ)
    (hcanonicalTruth : canonicalFisher truthProjector = Istar)
    (hlocal : ∀ i j, ∀ᶠ n in atTop,
      |canonicalFisher (projectedRLSPath leadingProjector raw n) i j -
          canonicalFisher truthProjector i j| ≤
        L i j *
          ‖projectedRLSPath leadingProjector raw n - truthProjector‖)
    (epsilon : ℕ → ℝ)
    (exploration : ℕ →
      Matrix (Fin (pureTangentDimension D))
        (Fin (pureTangentDimension D)) ℝ)
    (B : Fin (pureTangentDimension D) →
      Fin (pureTangentDimension D) → ℝ)
    (hB : ∀ i j, 0 ≤ B i j)
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hexplorationBound : ∀ n i j,
      |exploration n i j - Istar i j| ≤ B i j) :
    let exploitation := fun n =>
      canonicalFisher (projectedRLSPath leadingProjector raw n)
    let predictable := predictableFisher epsilon exploitation exploration
    MatrixEntrywiseTendsto predictable Istar ∧
      MatrixEntrywiseTendsto (fisherCesaroAverage predictable)
        Istar := by
  dsimp only
  have hprojected := projectedRLS_tendsto_of_davisKahan
    raw rawTruth leadingProjector truthProjector C hC hraw hDK
  have hexploitation : MatrixEntrywiseTendsto
      (fun n => canonicalFisher (projectedRLSPath leadingProjector raw n))
      Istar := by
    have hcontroller := canonicalController_tendsto_of_localLipschitz
      (projectedRLSPath leadingProjector raw) truthProjector
      canonicalFisher L hL hprojected hlocal
    simpa [hcanonicalTruth] using hcontroller
  have hpredictable := predictableFisher_tendsto_of_vanishing_exploration
    epsilon
    (fun n => canonicalFisher (projectedRLSPath leadingProjector raw n))
    exploration Istar B hB hepsilon
    hexploitation hexplorationBound
  exact ⟨hpredictable, fisherCesaroAverage_tendsto _ _ hpredictable⟩

/-- Concrete cyclic specialization of the abstract pathwise theorem.  This
corollary identifies the controller target with `I / (2(D-1))`; it makes no
claim that this target is Bures- or fidelity-optimal when `D > 2`. -/
theorem projectedRLS_cyclicFisher_and_cesaro_tendsto
    (D : ℕ) (hD : 1 < D)
    {Raw Projector : Type*}
    [NormedAddCommGroup Raw] [NormedSpace ℝ Raw]
    [NormedAddCommGroup Projector] [NormedSpace ℝ Projector]
    (raw : ℕ → Raw) (rawTruth : Raw)
    (leadingProjector : Raw → Projector) (truthProjector : Projector)
    (C : ℝ) (hC : 0 ≤ C)
    (hraw : Tendsto raw atTop (nhds rawTruth))
    (hDK : ∀ n,
      ‖leadingProjector (raw n) - truthProjector‖ ≤
        C * ‖raw n - rawTruth‖)
    (canonicalFisher : Projector →
      Matrix (Fin (pureTangentDimension D))
        (Fin (pureTangentDimension D)) ℝ)
    (L : Fin (pureTangentDimension D) →
      Fin (pureTangentDimension D) → ℝ)
    (hL : ∀ i j, 0 ≤ L i j)
    (hcanonicalTruth : canonicalFisher truthProjector =
      canonicalCyclicFisherTarget D)
    (hlocal : ∀ i j, ∀ᶠ n in atTop,
      |canonicalFisher (projectedRLSPath leadingProjector raw n) i j -
          canonicalFisher truthProjector i j| ≤
        L i j *
          ‖projectedRLSPath leadingProjector raw n - truthProjector‖)
    (epsilon : ℕ → ℝ)
    (exploration : ℕ →
      Matrix (Fin (pureTangentDimension D))
        (Fin (pureTangentDimension D)) ℝ)
    (B : Fin (pureTangentDimension D) →
      Fin (pureTangentDimension D) → ℝ)
    (hB : ∀ i j, 0 ≤ B i j)
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hexplorationBound : ∀ n i j,
      |exploration n i j - canonicalCyclicFisherTarget D i j| ≤ B i j) :
    let exploitation := fun n =>
      canonicalFisher (projectedRLSPath leadingProjector raw n)
    let predictable := predictableFisher epsilon exploitation exploration
    MatrixEntrywiseTendsto predictable (canonicalCyclicFisherTarget D) ∧
      MatrixEntrywiseTendsto (fisherCesaroAverage predictable)
        (canonicalCyclicFisherTarget D) ∧
      canonicalCyclicAverageFisher D = canonicalCyclicFisherTarget D := by
  dsimp only
  have hmain := projectedRLS_predictableFisher_and_cesaro_tendsto
    D raw rawTruth leadingProjector truthProjector C hC hraw hDK
    canonicalFisher L hL (canonicalCyclicFisherTarget D) hcanonicalTruth
    hlocal epsilon exploration B hB hepsilon hexplorationBound
  exact ⟨hmain.1, hmain.2,
    canonicalCyclicAverageFisher_eq_identity_div D hD⟩

/-- Fisher-symmetric target declaration.  It is only the algebraic target
`Istar = (1/2) QFI`; no optimality assertion is included. -/
def fisherSymmetricTarget {m : ℕ}
    (QFI : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  (1 / 2 : ℝ) • QFI

/-- If the exploitation controller converges to one half of the quantum
Fisher information and bounded exploration vanishes, then both predictable
one-step information and its Cesaro average converge to that same
Fisher-symmetric target. -/
theorem fisherSymmetric_predictable_and_cesaro_tendsto
    {m : ℕ}
    (QFI : Matrix (Fin m) (Fin m) ℝ)
    (epsilon : ℕ → ℝ)
    (exploitation exploration : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (B : Fin m → Fin m → ℝ)
    (hB : ∀ i j, 0 ≤ B i j)
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hcontroller : MatrixEntrywiseTendsto exploitation
      (fisherSymmetricTarget QFI))
    (hexplorationBound : ∀ n i j,
      |exploration n i j - fisherSymmetricTarget QFI i j| ≤ B i j) :
    MatrixEntrywiseTendsto
        (predictableFisher epsilon exploitation exploration)
        (fisherSymmetricTarget QFI) ∧
      MatrixEntrywiseTendsto
        (fisherCesaroAverage
          (predictableFisher epsilon exploitation exploration))
        (fisherSymmetricTarget QFI) := by
  have hpredictable := predictableFisher_tendsto_of_vanishing_exploration
    epsilon exploitation exploration (fisherSymmetricTarget QFI)
    B hB hepsilon hcontroller hexplorationBound
  exact ⟨hpredictable, fisherCesaroAverage_tendsto _ _ hpredictable⟩

/-! ## Optional realized empirical-information transfer -/

/-- A pathwise hypothesis expressing that the bounded martingale empirical
information deviation from its predictable compensator vanishes entrywise.
No martingale theorem is assumed here. -/
def EmpiricalInformationDeviationVanishes {m : ℕ}
    (realized predictable : ℕ → Matrix (Fin m) (Fin m) ℝ) : Prop :=
  ∀ i j, Tendsto
    (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
      (realized k i j - predictable k i j))
    atTop (nhds 0)

/-- If a bounded-martingale argument supplies the preceding deviation
hypothesis, realized empirical Fisher information converges to the same target
as the predictable Cesaro average. -/
theorem empiricalFisher_tendsto_of_martingaleDeviation
    {m : ℕ}
    (realized predictable : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (target : Matrix (Fin m) (Fin m) ℝ)
    (hpredictable : MatrixEntrywiseTendsto
      (fisherCesaroAverage predictable) target)
    (hdeviation : EmpiricalInformationDeviationVanishes realized predictable) :
    MatrixEntrywiseTendsto (fisherCesaroAverage realized) target := by
  intro i j
  have hsum := (hdeviation i j).add (hpredictable i j)
  simpa only [zero_add] using hsum.congr'
    (Eventually.of_forall fun n => by
      simp only [fisherCesaroAverage]
      rw [← mul_add, ← Finset.sum_add_distrib]
      congr 2
      funext k
      ring)

end

end PureMultilevelProjectedRLSInformationConvergence
end QubitOracle.Paper
