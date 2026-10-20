-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.ExplorationBudgetStrongLaw

/-! The exploration-pilot route separates mere divergence (consistency)
from the stronger, but improved, one-step efficiency budget. -/
namespace QubitOracle.AdaptiveDesign.PVMPilotSchedule
open Filter
open scoped BigOperators Topology
noncomputable section

class Schedule where
  probability : ℕ → ℝ
  nonnegative : ∀ n, 0 ≤ probability n
  le_one : ∀ n, probability n ≤ 1
  vanishes : Tendsto probability atTop (𝓝 0)
  diverges : Tendsto (ExplorationBudgetStrongLaw.mass probability) atTop atTop

variable [S : Schedule]
def epsilon (n : ℕ) : ℝ := S.probability n
lemma epsilon_nonnegative (n : ℕ) : 0 ≤ epsilon n := S.nonnegative n
lemma epsilon_le_one (n : ℕ) : epsilon n ≤ 1 := S.le_one n
lemma epsilon_tendsto_zero : Tendsto epsilon atTop (𝓝 0) := S.vanishes
def mass (n : ℕ) : ℝ := ExplorationBudgetStrongLaw.mass epsilon n
lemma mass_pos (n : ℕ) : 0 < mass n :=
  ExplorationBudgetStrongLaw.mass_pos epsilon epsilon_nonnegative n
lemma mass_ge_one (n : ℕ) : 1 ≤ mass n :=
  ExplorationBudgetStrongLaw.mass_ge_one epsilon epsilon_nonnegative n
lemma mass_mono : Monotone mass :=
  ExplorationBudgetStrongLaw.mass_mono epsilon epsilon_nonnegative
lemma mass_tendsto : Tendsto mass atTop atTop := S.diverges

/-- E_n / sqrt(n) tends to infinity. It is an efficiency hypothesis on
the known schedule, never an assumed rate for the estimator. -/
def OneStepBudget : Prop :=
  Tendsto (fun n : ℕ => Real.sqrt ((n:ℝ)+1)/mass n) atTop (𝓝 0)

end
end QubitOracle.AdaptiveDesign.PVMPilotSchedule

-/
