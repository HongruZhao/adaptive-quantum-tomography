import QubitOracle.Paper.HistoryDependentInformationMartingale

/-!
# Convergence assembly for history-dependent information

This module separates adaptive information convergence into its two exact
parts: convergence of the predictable conditional-information average and a
martingale innovation strong law.  It applies to arbitrary finite parameter
dimension and arbitrary information matrices chosen from the observed past.
-/

noncomputable section

namespace QubitOracle.Paper

open scoped BigOperators
open Filter MeasureTheory

/-- Information of the setting actually selected after the prefix through
time `n`. -/
def historyPathSelectedInformation
    {M Y D : Type*} [Fintype M]
    (information : SequentialHistory M Y → M → Matrix D D ℝ)
    (n : ℕ) (omega : ℕ → M × Y) : Matrix D D ℝ :=
  information (trajectoryPrefixHistory (Preorder.frestrictLe n omega))
    (omega (n + 1)).1

/-- Conditional mean information before the next setting is selected. -/
def historyPathPredictableInformation
    {M Y D : Type*} [Fintype M]
    (q : AdaptivePolicy M Y)
    (information : SequentialHistory M Y → M → Matrix D D ℝ)
    (n : ℕ) (omega : ℕ → M × Y) : Matrix D D ℝ :=
  historyPolicyMeanInformation q information
    (trajectoryPrefixHistory (Preorder.frestrictLe n omega))

/-- One selected information matrix is its conditional mean plus its centered
innovation. -/
theorem historyPathSelectedInformation_eq_predictable_add_innovation
    {M Y D : Type*} [Fintype M]
    (q : AdaptivePolicy M Y)
    (information : SequentialHistory M Y → M → Matrix D D ℝ)
    (n : ℕ) (omega : ℕ → M × Y) :
    historyPathSelectedInformation information n omega =
      historyPathPredictableInformation q information n omega +
        historyPathInformationInnovation q information n omega :=
  historyInformation_eq_mean_add_innovation q information
    (trajectoryPrefixHistory (Preorder.frestrictLe n omega))
    (omega (n + 1)).1

/-- Exact normalized observed/predictable/martingale decomposition. -/
theorem historyPathInformationAverage_decompose
    {M Y D : Type*} [Fintype M]
    (q : AdaptivePolicy M Y)
    (information : SequentialHistory M Y → M → Matrix D D ℝ)
    (N : ℕ) (omega : ℕ → M × Y) :
    (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N,
        historyPathSelectedInformation information n omega =
      (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N,
        historyPathPredictableInformation q information n omega +
      (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N,
        historyPathInformationInnovation q information n omega := by
  rw [← smul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  exact historyPathSelectedInformation_eq_predictable_add_innovation
    q information n omega

/-- Pointwise convergence assembly from the two decomposition terms. -/
theorem historyPathSelectedInformationAverage_tendsto
    {M Y D : Type*} [Fintype M]
    (q : AdaptivePolicy M Y)
    (information : SequentialHistory M Y → M → Matrix D D ℝ)
    (omega : ℕ → M × Y) (target : Matrix D D ℝ)
    (hpredictable : Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N,
        historyPathPredictableInformation q information n omega)
      atTop (nhds target))
    (hinnovation : Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N,
        historyPathInformationInnovation q information n omega)
      atTop (nhds 0)) :
    Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N,
        historyPathSelectedInformation information n omega)
      atTop (nhds target) := by
  convert hpredictable.add hinnovation using 1
  · funext N
    exact historyPathInformationAverage_decompose q information N omega
  · simp

/-- Almost-sure convergence assembly under the exact Hall--Heyde conditional
moment premise. -/
theorem historyPathSelectedInformationAverage_ae_tendsto_of_conditionalMoments
    {Theta M Y D : Type*} [Fintype M] [Fintype Y]
    [Fintype D] [DecidableEq D]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [StandardBorelSpace M] [StandardBorelSpace Y]
    [Nonempty M] [Nonempty Y]
    (q : AdaptivePolicy M Y) (p : OutcomeKernel Theta M Y) (theta : Theta)
    (information : SequentialHistory M Y → M → Matrix D D ℝ)
    (target : Matrix D D ℝ)
    (hL2 : ∀ n i j, MemLp
      (fun omega : ℕ → M × Y =>
        historyPathInformationInnovation q information n omega i j)
      2 (adaptiveTrajectoryMeasure q p theta))
    (hsummable : ∀ i j, ∀ᵐ omega ∂adaptiveTrajectoryMeasure q p theta,
      Summable (fun n => hallHeydeWeightedSecondMoment
        (adaptiveTrajectoryMeasure q p theta)
        MeasureTheory.Filtration.piLE
        (fun n omega => historyPathInformationInnovation q information n omega i j)
        n omega))
    (hpredictable : ∀ᵐ omega ∂adaptiveTrajectoryMeasure q p theta,
      Tendsto
        (fun N : ℕ => (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N,
          historyPathPredictableInformation q information n omega)
        atTop (nhds target)) :
    ∀ᵐ omega ∂adaptiveTrajectoryMeasure q p theta,
      Tendsto
        (fun N : ℕ => (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N,
          historyPathSelectedInformation information n omega)
        atTop (nhds target) := by
  have hinnovation :=
    historyInformationInnovation_strongLaw_adaptiveTrajectory_of_conditionalMoments
      q p theta information hL2 hsummable
  filter_upwards [hpredictable, hinnovation] with omega hpredictable hinnovation
  exact historyPathSelectedInformationAverage_tendsto
    q information omega target hpredictable hinnovation

/-- Uniformly bounded specialization of the almost-sure assembly theorem. -/
theorem historyPathSelectedInformationAverage_ae_tendsto_of_uniform_bound
    {Theta M Y D : Type*} [Fintype M] [Fintype Y]
    [Fintype D] [DecidableEq D]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    [StandardBorelSpace M] [StandardBorelSpace Y]
    [Nonempty M] [Nonempty Y]
    (q : AdaptivePolicy M Y) (p : OutcomeKernel Theta M Y) (theta : Theta)
    (information : SequentialHistory M Y → M → Matrix D D ℝ)
    (target : Matrix D D ℝ)
    (hbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ history setting i j,
      ‖historyInformationInnovation q information history setting i j‖ ≤ C)
    (hpredictable : ∀ᵐ omega ∂adaptiveTrajectoryMeasure q p theta,
      Tendsto
        (fun N : ℕ => (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N,
          historyPathPredictableInformation q information n omega)
        atTop (nhds target)) :
    ∀ᵐ omega ∂adaptiveTrajectoryMeasure q p theta,
      Tendsto
        (fun N : ℕ => (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N,
          historyPathSelectedInformation information n omega)
        atTop (nhds target) := by
  have hinnovation :=
    historyInformationInnovation_strongLaw_adaptiveTrajectory_of_uniform_bound
      q p theta information hbound
  filter_upwards [hpredictable, hinnovation] with omega hpredictable hinnovation
  exact historyPathSelectedInformationAverage_tendsto
    q information omega target hpredictable hinnovation

end QubitOracle.Paper
