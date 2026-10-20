import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
/-! Supporting definitions and proved lemmas used by the manuscript. -/

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









end

end QubitOracle.Paper
