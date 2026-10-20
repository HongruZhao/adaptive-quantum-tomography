-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.BatchExplorationMomentBudget

/-! The deterministic super-polynomial bound used for exceptional
histories in the mean-risk proof. -/
namespace QubitOracle.AdaptiveDesign.ExplorationRareEventRate
open Filter
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

theorem polynomial_exp_tendsto (M : ℕ → ℝ) (hM : ∀ n, 0 < M n)
    (hMt : Tendsto M atTop atTop)
    (hlog : Tendsto (fun n : ℕ => Real.log ((n:ℝ)+1)/M n) atTop (𝓝 0))
    (c : ℝ) (hc : 0 < c) (p : ℕ) :
    Tendsto (fun n : ℕ => ((n:ℝ)+1)^p*Real.exp (-c*M n)) atTop (𝓝 0) := by
  have hMp : Tendsto (fun n => (c/2)*M n) atTop atTop := hMt.const_mul_atTop (by positivity)
  have hupper := Real.tendsto_exp_neg_atTop_nhds_zero.comp hMp
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _ hupper
  have he := hlog.eventually (eventually_lt_nhds (show (0:ℝ) < c/(2*((p:ℝ)+1)) by positivity))
  filter_upwards [he] with n hn
  have hlogpos : 0 ≤ Real.log ((n:ℝ)+1) := Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg n))
  have hh := (div_lt_iff₀ (hM n)).mp hn
  have hx : Real.log ((n:ℝ)+1) < (c*M n)/(2*((p:ℝ)+1)) := by
    calc
      _ < (c/(2*((p:ℝ)+1)))*M n := hh
      _ = _ := by ring
  have hk := (lt_div_iff₀ (show 0 < 2*((p:ℝ)+1) by positivity)).mp hx
  have hp : (p:ℝ)*Real.log ((n:ℝ)+1) ≤ c*M n/2 := by nlinarith
  have hid : ((n:ℝ)+1)^p = Real.exp ((p:ℝ)*Real.log ((n:ℝ)+1)) := by
    rw [Real.exp_nat_mul,Real.exp_log (by positivity)]
  rw [hid,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [hp]

theorem held_polynomial_exp [PVMPilotSchedule.Schedule]
    (b : ℕ → ℕ) (hp : ∀ j, 0 < b j) (hb : PVMPilotSchedule.BatchMomentCondition b)
    (c : ℝ) (hc : 0 < c) (p : ℕ) :
    Tendsto (fun n : ℕ => ((n:ℝ)+1)^p*Real.exp
      (-c*PVMPilotSchedule.mass
        (SequentialRidgeController.lastRefresh (SequentialRidgeController.batchRefresh b) (n/2))))
      atTop (𝓝 0) := by
  apply polynomial_exp_tendsto _ (fun _ => PVMPilotSchedule.mass_pos _)
    (PVMPilotSchedule.mass_tendsto.comp
      ((SequentialRidgeController.batchRefresh_lastRefresh_tendsto b hp).comp PVMPilotSchedule.half_tendsto))
    (PVMPilotSchedule.held_budget b hp hb) c hc p

end
end QubitOracle.AdaptiveDesign.ExplorationRareEventRate

-/
