-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMPilotSchedule

namespace QubitOracle.AdaptiveDesign.PVMPilotSchedule
open Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1800000

/-- A quantitative budget lemma for power-law exploration. -/
lemma power_mass_ratio (α β : ℝ) (hα : 0 < α) (hgap : α+β<1) :
    Tendsto (fun n : ℕ => ((n:ℝ)+1)^β /
      ExplorationBudgetStrongLaw.mass (fun t => ((t:ℝ)+1)^(-α)) n) atTop (𝓝 0) := by
  unfold ExplorationBudgetStrongLaw.mass
  let e : ℕ → ℝ := fun n => ((n:ℝ)+1)^(-α)
  have he (n : ℕ) : 0 < e n := Real.rpow_pos_of_pos (by positivity) _
  have hanti : Antitone e := by
    intro m n hmn
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
    exact_mod_cast Nat.add_le_add_right hmn 1
  have hlower (n : ℕ) : (n:ℝ)*e n ≤ ∑ t ∈ Finset.range n, e t := by
    calc
      _ = ∑ t ∈ Finset.range n, e n := by simp
      _ ≤ _ := Finset.sum_le_sum (fun t ht => hanti (Nat.le_of_lt (Finset.mem_range.mp ht)))
  have hden (n : ℕ) : 0 < 1 + ∑ t ∈ Finset.range n, e t := by
    have hn := Finset.sum_nonneg (s := Finset.range n) (fun t _ => (he t).le)
    linarith
  have ht : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hz : Tendsto (fun n : ℕ => 2 * ((n:ℝ)+1)^(α+β-1)) atTop (𝓝 0) := by
    have hh := ((tendsto_rpow_neg_atTop (by linarith : 0 < 1-α-β)).comp ht).const_mul 2
    convert hh using 1 <;> simp only [mul_zero, neg_sub, Function.comp_def]
    funext n
    congr 2
    ring
  apply squeeze_zero' (Eventually.of_forall fun n => by positivity) _ hz
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hd : (((n:ℝ)+1)/2)*e n ≤ 1 + ∑ t ∈ Finset.range n, e t := by
    have hh := hlower n
    nlinarith [he n]
  calc
    ((n:ℝ)+1)^β / (1+∑ t ∈ Finset.range n, e t) ≤
        ((n:ℝ)+1)^β / ((((n:ℝ)+1)/2)*e n) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hd
    _ = 2 * ((n:ℝ)+1)^(α+β-1) := by
      dsimp [e]
      have hp : 0 < (n:ℝ)+1 := by positivity
      have heq : ((n:ℝ)+1)^(α+β-1) * ((n:ℝ)+1) * ((n:ℝ)+1)^(-α) =
          ((n:ℝ)+1)^β := by
        conv_lhs => arg 1; arg 2; rw [← Real.rpow_one ((n:ℝ)+1)]
        rw [← Real.rpow_add hp, ← Real.rpow_add hp]
        congr 1
        ring
      apply (div_eq_iff (by positivity)).mpr
      nlinarith [heq]

def powerSchedule (α : ℝ) (hα : 0 < α) (hα1 : α < 1) : Schedule where
  probability n := ((n:ℝ)+1)^(-α)
  nonnegative n := by positivity
  le_one n := Real.rpow_le_one_of_one_le_of_nonpos
    (by have h := Nat.cast_nonneg (α:=ℝ) n; linarith) (by linarith)
  vanishes := by
    have ht : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    exact (tendsto_rpow_neg_atTop hα).comp ht
  diverges := by
    have hh := power_mass_ratio α 0 hα (by linarith)
    simp only [Real.rpow_zero,one_div] at hh
    have hp : ∀ n, 0 < (ExplorationBudgetStrongLaw.mass (fun t => ((t:ℝ)+1)^(-α)) n)⁻¹ :=
      fun n => inv_pos.mpr (ExplorationBudgetStrongLaw.mass_pos _ (fun t => by positivity) n)
    have ht : Tendsto (fun n => (ExplorationBudgetStrongLaw.mass (fun t => ((t:ℝ)+1)^(-α)) n)⁻¹)
        atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨hh,Eventually.of_forall hp⟩
    have hi := ht.inv_tendsto_nhdsGT_zero
    change Tendsto (fun n => ((ExplorationBudgetStrongLaw.mass (fun t => ((t:ℝ)+1)^(-α)) n)⁻¹)⁻¹) atTop atTop at hi
    simpa only [inv_inv] using hi

lemma powerSchedule_oneStep (α : ℝ) (hα : 0 < α) (hhalf : α < 1/2) :
    @OneStepBudget (powerSchedule α hα (by linarith)) := by
  have hh := power_mass_ratio α (1/2) hα (by linarith)
  change Tendsto (fun n : ℕ => Real.sqrt ((n:ℝ)+1) /
    ExplorationBudgetStrongLaw.mass (fun t => ((t:ℝ)+1)^(-α)) n) atTop (𝓝 0)
  simpa only [Real.sqrt_eq_rpow] using hh

end
end QubitOracle.AdaptiveDesign.PVMPilotSchedule

-/
