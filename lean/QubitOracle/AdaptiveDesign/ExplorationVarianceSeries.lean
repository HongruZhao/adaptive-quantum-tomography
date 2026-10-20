import QubitOracle.AdaptiveDesign.ExplorationBudgetStrongLaw

/-! Literal infinite-series version of the exploration-budget bound. -/
namespace QubitOracle.AdaptiveDesign.ExplorationBudgetStrongLaw
open scoped BigOperators
noncomputable section

theorem variance_weight_summable (ε : ℕ → ℝ) (hε : ∀ n, 0≤ε n) :
    Summable (fun n => ε n/mass ε (n+1)^2) :=
  summable_of_sum_range_le (fun n => div_nonneg (hε n) (sq_nonneg _))
    (variance_weight_bound ε hε)

theorem variance_weight_tsum_le_one (ε : ℕ → ℝ) (hε : ∀ n, 0≤ε n) :
    (∑' n, ε n/mass ε (n+1)^2)≤1 :=
  Real.tsum_le_of_sum_range_le (fun n => div_nonneg (hε n) (sq_nonneg _))
    (variance_weight_bound ε hε)

end
end QubitOracle.AdaptiveDesign.ExplorationBudgetStrongLaw
