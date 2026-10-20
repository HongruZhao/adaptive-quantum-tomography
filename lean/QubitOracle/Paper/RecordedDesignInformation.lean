import QubitOracle.Paper.InformationDefinitions

/-! Recorded settings and design information. The setting distribution is
held fixed in the score. The general integral identity uses the usual
integrability hypotheses; the actual designs in the paper have finite
support, covered by InformationDefinitions.randomized_information. -/
namespace QubitOracle.Paper.RecordedDesignInformation
open MeasureTheory InformationDefinitions
open scoped BigOperators
noncomputable section
variable {A O : Type*} [MeasurableSpace A] [Fintype O]

def designInformation (ξ : Measure A) (p dp dq : A → O → ℝ) : ℝ :=
  ∫ a, directionalFisher (p a) (dp a) (dq a) ∂ξ

theorem design_information_expected_score (ξ : Measure A) (p dp dq : A → O → ℝ) :
    designInformation ξ p dp dq =
      ∫ a, ∑ y, p a y * directionalScore (p a) (dp a) y *
        directionalScore (p a) (dq a) y ∂ξ := by
  unfold designInformation
  congr 1
  funext a
  exact fisher_eq_expected_scores _ _ _

theorem design_information_sum_integral (ξ : Measure A) (p dp dq : A → O → ℝ)
    (hi : ∀ y, Integrable (fun a =>
      if 0 < p a y then dp a y * dq a y / p a y else 0) ξ) :
    designInformation ξ p dp dq =
      ∑ y, ∫ a, if 0 < p a y then dp a y * dq a y / p a y else 0 ∂ξ := by
  exact integral_finsetSum _ (fun y _ => hi y)

theorem point_mass_information (a : A) (p dp dq : A → O → ℝ)
    (hm : Measurable (fun a => directionalFisher (p a) (dp a) (dq a))) :
    designInformation (Measure.dirac a) p dp dq = directionalFisher (p a) (dp a) (dq a) :=
  integral_dirac' _ a hm.stronglyMeasurable

theorem bounded_average_budget (ξ : Measure A) [IsProbabilityMeasure ξ]
    (budget : A → ℝ) (hbudget : Integrable budget ξ) (c : ℝ)
    (hc : ∀ᵐ a ∂ξ, budget a ≤ c) : ∫ a, budget a ∂ξ ≤ c := by
  simpa using integral_mono_ae hbudget (integrable_const c) hc

end
end QubitOracle.Paper.RecordedDesignInformation
