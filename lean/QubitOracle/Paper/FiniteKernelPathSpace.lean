import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import QubitOracle.Paper.SequentialExperiment

/-!
# Infinite path space for the finite adaptive experiment

Finite normalized policy and outcome masses are converted to probability
measures and then assembled by Mathlib's Ionescu--Tulcea theorem into a
probability measure on infinite setting--outcome trajectories.
-/

namespace QubitOracle.Paper

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

/-- Probability measure represented by finitely many nonnegative real
masses. -/
def finiteMassMeasure
    {Beta : Type*} [Fintype Beta] [MeasurableSpace Beta]
    (mass : Beta → ℝ)
    (hmass : ∀ b, 0 ≤ mass b)
    (hsum : ∑ b, mass b = 1) : Measure Beta :=
  Measure.sum fun b => ENNReal.ofReal (mass b) • Measure.dirac b

instance finiteMassMeasure_isProbability
    {Beta : Type*} [Fintype Beta] [MeasurableSpace Beta]
    (mass : Beta → ℝ)
    (hmass : ∀ b, 0 ≤ mass b)
    (hsum : ∑ b, mass b = 1) :
    IsProbabilityMeasure (finiteMassMeasure mass hmass hsum) := by
  unfold finiteMassMeasure
  apply HasSum.isProbabilityMeasure_sum_dirac hmass
  simpa [hsum] using hasSum_fintype mass

theorem integral_finiteMassMeasure
    {Beta E : Type*} [Fintype Beta]
    [MeasurableSpace Beta] [MeasurableSingletonClass Beta]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (mass : Beta → ℝ)
    (hmass : ∀ b, 0 ≤ mass b)
    (hsum : ∑ b, mass b = 1)
    (f : Beta → E) :
    ∫ b, f b ∂finiteMassMeasure mass hmass hsum =
      ∑ b, mass b • f b := by
  have hfint : Integrable f (finiteMassMeasure mass hmass hsum) := by
    unfold finiteMassMeasure
    apply integrable_sum_measure
    · intro b
      exact (integrable_dirac (by finiteness)).smul_measure (by finiteness)
    · exact summable_of_finite_support (Set.toFinite _)
  unfold finiteMassMeasure at hfint ⊢
  rw [integral_sum_measure hfint, tsum_fintype]
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_smul_measure, integral_dirac]
  simp [ENNReal.toReal_ofReal (hmass b)]

/-- Joint law of the next predictable setting and its quantum outcome. -/
def adaptiveJointKernel
    {Theta M Y : Type*} [Fintype M] [Fintype Y]
    (q : AdaptivePolicy M Y)
    (p : OutcomeKernel Theta M Y)
    (theta : Theta) : FiniteKernel (SequentialHistory M Y) (M × Y) where
  mass h z := q.mass h z.1 * p.mass (theta, z.1) z.2
  mass_nonneg h z := mul_nonneg
    (q.mass_nonneg h z.1) (p.mass_nonneg (theta, z.1) z.2)
  sum_mass h := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ m, ∑ y, q.mass h m * p.mass (theta, m) y) =
          ∑ m, q.mass h m * ∑ y, p.mass (theta, m) y := by
        apply Finset.sum_congr rfl
        intro m _
        rw [Finset.mul_sum]
      _ = ∑ m, q.mass h m := by
        apply Finset.sum_congr rfl
        intro m _
        rw [p.sum_mass, mul_one]
      _ = 1 := q.sum_mass h

/-- Reverse-chronological list represented by a trajectory prefix through
time `n`. -/
def trajectoryPrefixHistory
    {M Y : Type*} {n : ℕ}
    (pathPrefix : (i : Finset.Iic n) → M × Y) : SequentialHistory M Y :=
  (List.ofFn fun k : Fin (n + 1) =>
    pathPrefix ⟨k.val,
      Finset.mem_Iic.mpr (Nat.le_of_lt_succ k.isLt)⟩).reverse

/-- Conditional kernel for point `n+1` given the trajectory through `n`. -/
def adaptiveTrajectoryKernel
    {Theta M Y : Type*}
    [Fintype M] [Fintype Y]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (q : AdaptivePolicy M Y)
    (p : OutcomeKernel Theta M Y)
    (theta : Theta) (n : ℕ) :
    ProbabilityTheory.Kernel
      ((i : Finset.Iic n) → M × Y) (M × Y) :=
  ProbabilityTheory.Kernel.ofFunOfCountable fun pathPrefix =>
    let K := adaptiveJointKernel q p theta
    finiteMassMeasure
      (K.mass (trajectoryPrefixHistory pathPrefix))
      (K.mass_nonneg (trajectoryPrefixHistory pathPrefix))
      (K.sum_mass (trajectoryPrefixHistory pathPrefix))

instance adaptiveTrajectoryKernel_isMarkov
    {Theta M Y : Type*}
    [Fintype M] [Fintype Y]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (q : AdaptivePolicy M Y)
    (p : OutcomeKernel Theta M Y)
    (theta : Theta) (n : ℕ) :
    IsMarkovKernel (adaptiveTrajectoryKernel q p theta n) where
  isProbabilityMeasure pathPrefix := by
    change IsProbabilityMeasure
      (finiteMassMeasure
        ((adaptiveJointKernel q p theta).mass
          (trajectoryPrefixHistory pathPrefix))
        ((adaptiveJointKernel q p theta).mass_nonneg
          (trajectoryPrefixHistory pathPrefix))
        ((adaptiveJointKernel q p theta).sum_mass
          (trajectoryPrefixHistory pathPrefix)))
    infer_instance

/-- Distribution of the first setting--outcome pair. -/
def adaptiveInitialMeasure
    {Theta M Y : Type*}
    [Fintype M] [Fintype Y]
    [MeasurableSpace M] [MeasurableSpace Y]
    (q : AdaptivePolicy M Y)
    (p : OutcomeKernel Theta M Y)
    (theta : Theta) : Measure (M × Y) :=
  let K := adaptiveJointKernel q p theta
  finiteMassMeasure (K.mass []) (K.mass_nonneg []) (K.sum_mass [])

instance adaptiveInitialMeasure_isProbability
    {Theta M Y : Type*}
    [Fintype M] [Fintype Y]
    [MeasurableSpace M] [MeasurableSpace Y]
    (q : AdaptivePolicy M Y)
    (p : OutcomeKernel Theta M Y)
    (theta : Theta) :
    IsProbabilityMeasure (adaptiveInitialMeasure q p theta) := by
  unfold adaptiveInitialMeasure
  infer_instance

/-- Ionescu--Tulcea law of the infinite adaptive setting--outcome path. -/
def adaptiveTrajectoryMeasure
    {Theta M Y : Type*}
    [Fintype M] [Fintype Y]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (q : AdaptivePolicy M Y)
    (p : OutcomeKernel Theta M Y)
    (theta : Theta) : Measure (ℕ → M × Y) :=
  ProbabilityTheory.Kernel.trajMeasure
    (adaptiveInitialMeasure q p theta)
    (adaptiveTrajectoryKernel q p theta)

instance adaptiveTrajectoryMeasure_isProbability
    {Theta M Y : Type*}
    [Fintype M] [Fintype Y]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (q : AdaptivePolicy M Y)
    (p : OutcomeKernel Theta M Y)
    (theta : Theta) :
    IsProbabilityMeasure (adaptiveTrajectoryMeasure q p theta) := by
  unfold adaptiveTrajectoryMeasure
  infer_instance

end

end QubitOracle.Paper
