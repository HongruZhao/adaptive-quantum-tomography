-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMPilotSchedule
import QubitOracle.AdaptiveDesign.RidgeBatchSchedule

/-! The extra deterministic batch condition for mean-risk convergence.
This is separate from the hypotheses for consistency and the CLT. -/
namespace QubitOracle.AdaptiveDesign.PVMPilotSchedule
open SequentialRidgeController Filter
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
variable [Schedule]

/-- The paper's boundary condition, using the harmless augmented mass
`1+E_n` already used in the pilot normal equation. -/
def BatchMomentCondition (batchSize : ℕ → ℕ) : Prop :=
  Tendsto (fun j => Real.log ((batchBoundary batchSize (j+1):ℝ)+1)/
    mass (batchBoundary batchSize j)) atTop (𝓝 0)

def containingBatch (batchSize : ℕ → ℕ) (hp : ∀ j, 0 < batchSize j) (n : ℕ) : ℕ :=
  Nat.find (show ∃ j, n < batchBoundary batchSize (j+1) from
    ⟨n,Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (le_batchBoundary batchSize hp (n+1))⟩)

theorem containingBatch_upper (b : ℕ → ℕ) (hp : ∀ j, 0 < b j) (n : ℕ) :
    n < batchBoundary b (containingBatch b hp n+1) := by
  unfold containingBatch
  exact Nat.find_spec (p:=fun j => n < batchBoundary b (j+1)) _

theorem containingBatch_lower (b : ℕ → ℕ) (hp : ∀ j, 0 < b j) (n : ℕ) :
    batchBoundary b (containingBatch b hp n) ≤ n := by
  let j := containingBatch b hp n
  by_cases hj : j = 0
  · simp only [show containingBatch b hp n = 0 from hj,batchBoundary,Finset.range_zero,
      Finset.sum_empty,Nat.zero_le]
  · have hx : ∃ k, n < batchBoundary b (k+1) :=
      ⟨n,Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (le_batchBoundary b hp (n+1))⟩
    have hm : ¬ n < batchBoundary b ((j-1)+1) :=
      Nat.find_min (p:=fun k => n < batchBoundary b (k+1)) hx (by
        change j-1 < containingBatch b hp n
        change j-1 < j
        omega)
    have hs : j-1+1 = j := by omega
    rw [hs] at hm
    exact Nat.le_of_not_gt hm

theorem containingBatch_tendsto (b : ℕ → ℕ) (hp : ∀ j, 0 < b j) :
    Tendsto (containingBatch b hp) atTop atTop := by
  apply tendsto_atTop.2
  intro K
  filter_upwards [eventually_ge_atTop (batchBoundary b K)] with n hn
  have hu := containingBatch_upper b hp n
  by_contra hh
  have hj : containingBatch b hp n+1 ≤ K := by omega
  have hm := (batchBoundary_strictMono b hp).monotone hj
  omega

theorem boundary_le_lastRefresh (b : ℕ → ℕ) (hp : ∀ j, 0 < b j) (n : ℕ) :
    batchBoundary b (containingBatch b hp n) ≤ lastRefresh (batchRefresh b) n := by
  have hh := lastRefresh_monotone (batchRefresh b) (containingBatch_lower b hp n)
  rw [lastRefresh_at_refresh _ _ (batchRefresh_at_boundary b hp _)] at hh
  exact hh

theorem half_tendsto : Tendsto (fun n : ℕ => n/2) atTop atTop := by
  apply tendsto_atTop.2
  intro K
  filter_upwards [eventually_ge_atTop (2*K)] with n hn
  omega

/-- Estimates used for the final half of the records have exploration
mass growing faster than the logarithm of the total record count. -/
theorem held_budget (b : ℕ → ℕ) (hp : ∀ j, 0 < b j) (hbatch : BatchMomentCondition b) :
    Tendsto (fun n : ℕ => Real.log ((n:ℝ)+1)/
      mass (lastRefresh (batchRefresh b) (n/2))) atTop (𝓝 0) := by
  have hj := (containingBatch_tendsto b hp).comp half_tendsto
  have hh := hbatch.comp hj
  have hlim := hh.const_mul 2
  simp only [mul_zero] at hlim
  apply squeeze_zero _ _ hlim
  · intro n
    exact div_nonneg (Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg n))) (mass_pos _).le
  · intro n
    let j := containingBatch b hp (n/2)
    let N := batchBoundary b (j+1)
    have hNnat : n < 2*N := by have hu := containingBatch_upper b hp (n/2); change n/2 < N at hu; omega
    have hN : 0 < (N:ℝ)+1 := by positivity
    have hn : 0 < (n:ℝ)+1 := by positivity
    have hl : Real.log ((n:ℝ)+1) ≤ 2*Real.log ((N:ℝ)+1) := by
      have hnn : (n:ℝ)+1 ≤ 2*(N:ℝ) := by exact_mod_cast hNnat
      have hx : (n:ℝ)+1 ≤ ((N:ℝ)+1)^2 := by nlinarith [sq_nonneg (N:ℝ)]
      have hh := Real.log_le_log hn hx
      simpa only [Real.log_pow,Nat.cast_ofNat] using hh
    have hm := mass_mono (boundary_le_lastRefresh b hp (n/2))
    calc
      _ ≤ Real.log ((n:ℝ)+1)/mass (batchBoundary b j) :=
        div_le_div_of_nonneg_left (Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg n))) (mass_pos _) hm
      _ ≤ (2*Real.log ((N:ℝ)+1))/mass (batchBoundary b j) :=
        div_le_div_of_nonneg_right hl (mass_pos _).le
      _ = _ := by dsimp only [Function.comp_def,N,j]; ring

end
end QubitOracle.AdaptiveDesign.PVMPilotSchedule

-/
