import Mathlib
/-!
# Exact Abbasi--Yadkori--Pal--Szepesvari citation contract

This file records the finite-dimensional statement used for the one-qubit RLS
pilot.  The source is Theorem 1 of:

Y. Abbasi-Yadkori, D. Pal, and C. Szepesvari,
"Online Least Squares Estimation with Self-Normalized Processes: An Application
to Bandit Problems," NeurIPS 2011.

No axiom is introduced here.  `APSSelfNormalizedContract data` is the exact
proposition that may later be asserted as a literature atom after approval.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace QubitOracle.Paper

noncomputable section

abbrev RLSVector (d : ℕ) := Fin d → ℝ
abbrev RLSMatrix (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

def rlsOuter {d : ℕ} (x : RLSVector d) : RLSMatrix d :=
  fun i j => x i * x j

def rlsQuadratic {d : ℕ} (M : RLSMatrix d) (x : RLSVector d) : ℝ :=
  ∑ i, ∑ j, x i * M i j * x j

def RLSPositiveDefinite {d : ℕ} (M : RLSMatrix d) : Prop :=
  M.IsSymm ∧ ∀ x : RLSVector d, x ≠ 0 → 0 < rlsQuadratic M x

/-- Measurability with an explicitly supplied source sigma-algebra. -/
def MeasurableFrom
    {Ω α : Type*} [MeasurableSpace α]
    (source : MeasurableSpace Ω) (f : Ω → α) : Prop :=
  ∀ s : Set α, MeasurableSet s → @MeasurableSet Ω source (f ⁻¹' s)

/-- A filtration represented without adding a second ambient typeclass
instance. -/
def IsRLSFiltration
    {Ω : Type*} [MeasurableSpace Ω] (F : ℕ → MeasurableSpace Ω) : Prop :=
  Monotone F ∧ ∀ t, F t ≤ ‹MeasurableSpace Ω›

/-- Conditional `R`-sub-Gaussianity in its integrated event form.  For every
past-measurable event this is the integral version of

`E[exp(lambda * eta_t) | F_(t-1)] <= exp(lambda^2 R^2 / 2)`.
-/
def ConditionallyRSubGaussian
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : ℕ → MeasurableSpace Ω)
    (η : ℕ → Ω → ℝ) (R : ℝ) : Prop :=
  0 ≤ R ∧
  ∀ (t : ℕ) (lambda : ℝ) (A : Set Ω),
    @MeasurableSet Ω (F t) A →
      (∫ ω in A, Real.exp (lambda * η (t + 1) ω) ∂μ) ≤
        Real.exp (lambda ^ 2 * R ^ 2 / 2) * (μ A).toReal

/-- The predictable vector process and conditionally sub-Gaussian noise in
Abbasi--Yadkori--Pal--Szepesvari Theorem 1. -/
structure APSSelfNormalizedData
    {Ω : Type*} [MeasurableSpace Ω] (d : ℕ) where
  μ : Measure Ω
  filtration : ℕ → MeasurableSpace Ω
  noise : ℕ → Ω → ℝ
  regressor : ℕ → Ω → RLSVector d
  initialMatrix : RLSMatrix d
  subGaussianRadius : ℝ
  probabilityMeasure : μ univ = 1
  filtration_property : IsRLSFiltration filtration
  noise_measurable : ∀ t, MeasurableFrom (filtration (t + 1)) (noise (t + 1))
  regressor_predictable :
    ∀ t, MeasurableFrom (filtration t) (regressor (t + 1))
  conditional_subGaussian :
    ConditionallyRSubGaussian μ filtration noise subGaussianRadius
  initial_positive_definite : RLSPositiveDefinite initialMatrix

def apsGram
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (data : APSSelfNormalizedData (Ω := Ω) d)
    (t : ℕ) (ω : Ω) : RLSMatrix d :=
  data.initialMatrix +
    ∑ s ∈ Finset.range t, rlsOuter (data.regressor (s + 1) ω)

def apsScore
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (data : APSSelfNormalizedData (Ω := Ω) d)
    (t : ℕ) (ω : Ω) : RLSVector d :=
  fun i =>
    ∑ s ∈ Finset.range t,
      data.noise (s + 1) ω * data.regressor (s + 1) ω i

def apsSelfNormalizedSquared
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (data : APSSelfNormalizedData (Ω := Ω) d)
    (t : ℕ) (ω : Ω) : ℝ :=
  rlsQuadratic (apsGram data t ω)⁻¹ (apsScore data t ω)

def apsLogBoundary
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (data : APSSelfNormalizedData (Ω := Ω) d) (delta : ℝ)
    (t : ℕ) (ω : Ω) : ℝ :=
  2 * data.subGaussianRadius ^ 2 *
    Real.log
      ((Real.sqrt (Matrix.det (apsGram data t ω)) /
          Real.sqrt (Matrix.det data.initialMatrix)) / delta)

/-- The simultaneous-in-time high-probability conclusion of Theorem 1. -/
def APSSelfNormalizedConclusion
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (data : APSSelfNormalizedData (Ω := Ω) d) (delta : ℝ) : Prop :=
  data.μ {ω | ∀ t : ℕ,
      apsSelfNormalizedSquared data t ω ≤ apsLogBoundary data delta t ω} ≥
    ENNReal.ofReal (1 - delta)

/-- Proposed single literature atom.  Its data fields are exactly the theorem's
filtration, adapted conditionally sub-Gaussian noise, predictable regressors,
and positive-definite initial matrix assumptions. -/
def APSSelfNormalizedContract
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (data : APSSelfNormalizedData (Ω := Ω) d) : Prop :=
  ∀ delta : ℝ, 0 < delta → delta < 1 →
    APSSelfNormalizedConclusion data delta

end

end QubitOracle.Paper
