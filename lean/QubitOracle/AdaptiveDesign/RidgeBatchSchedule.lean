import QubitOracle.AdaptiveDesign.SequentialRidgeController
/-!
# Every positive predetermined batch sequence is an admissible refresh rule

Refresh occurs at completed cumulative shot counts. The rule is a finite
search, includes unit batches, and imposes no growth bound. Its latest refresh
time tends to infinity, so a consistent raw estimator remains consistent when
frozen for the current batch.
-/

namespace QubitOracle.AdaptiveDesign.SequentialRidgeController

open Filter
open scoped BigOperators Topology

theorem lastRefresh_le (refresh : ℕ → Bool) (n : ℕ) : lastRefresh refresh n ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [lastRefresh]
    split_ifs <;> omega

theorem lastRefresh_monotone (refresh : ℕ → Bool) : Monotone (lastRefresh refresh) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [lastRefresh]
  split_ifs
  · exact (lastRefresh_le refresh n).trans (Nat.le_succ n)
  · rfl

theorem lastRefresh_at_refresh (refresh : ℕ → Bool) (n : ℕ) (hn : refresh n = true) :
    lastRefresh refresh n = n := by
  cases n with
  | zero => rfl
  | succ n => simp [lastRefresh, hn]

theorem lastRefresh_tendsto_of_cofinal
    (refresh : ℕ → Bool) (hcofinal : ∀ b, ∃ n, b ≤ n ∧ refresh n = true) :
    Tendsto (lastRefresh refresh) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  obtain ⟨n, hbn, hn⟩ := hcofinal b
  filter_upwards [eventually_ge_atTop n] with m hm
  have hmono := lastRefresh_monotone refresh hm
  rw [lastRefresh_at_refresh refresh n hn] at hmono
  exact hbn.trans hmono

/-- Cumulative shot count after the first `j` complete batches. -/
def batchBoundary (batchSize : ℕ → ℕ) (j : ℕ) : ℕ :=
  ∑ k ∈ Finset.range j, batchSize k

theorem batchBoundary_succ (batchSize : ℕ → ℕ) (j : ℕ) :
    batchBoundary batchSize (j+1) = batchBoundary batchSize j + batchSize j := by
  exact Finset.sum_range_succ batchSize j

theorem le_batchBoundary (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j)
    (j : ℕ) : j ≤ batchBoundary batchSize j := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih =>
    rw [batchBoundary_succ]
    have := hpositive j
    omega

theorem batchBoundary_strictMono (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    StrictMono (batchBoundary batchSize) := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [batchBoundary_succ]
  exact Nat.lt_add_of_pos_right (hpositive j)

/-- Finite-search implementation of the refresh predicate. Since positive
batches imply `j ≤ N_j`, only indices through the current shot need checking. -/
def batchRefresh (batchSize : ℕ → ℕ) (n : ℕ) : Bool :=
  decide (∃ j : Fin (n+1), batchBoundary batchSize j = n)

theorem batchRefresh_at_boundary (batchSize : ℕ → ℕ)
    (hpositive : ∀ j, 0 < batchSize j) (j : ℕ) :
    batchRefresh batchSize (batchBoundary batchSize j) = true := by
  simp only [batchRefresh, decide_eq_true_eq]
  exact ⟨⟨j, Nat.lt_succ_of_le (le_batchBoundary batchSize hpositive j)⟩, rfl⟩

theorem batchRefresh_iff (batchSize : ℕ → ℕ) (n : ℕ) :
    batchRefresh batchSize n = true ↔ ∃ j ≤ n, batchBoundary batchSize j = n := by
  simp only [batchRefresh, decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, Nat.le_of_lt_succ j.2, hj⟩
  · rintro ⟨j, hj, heq⟩
    exact ⟨⟨j, Nat.lt_succ_of_le hj⟩, heq⟩

theorem batchRefresh_lastRefresh_tendsto
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    Tendsto (lastRefresh (batchRefresh batchSize)) atTop atTop := by
  apply lastRefresh_tendsto_of_cofinal
  intro b
  exact ⟨batchBoundary batchSize b, le_batchBoundary batchSize hpositive b,
    batchRefresh_at_boundary batchSize hpositive b⟩

theorem consistent_estimate_at_batch_refresh
    {E : Type*} [TopologicalSpace E] (estimate : ℕ → E) (truth : E)
    (hconsistent : Tendsto estimate atTop (𝓝 truth))
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    Tendsto (fun n => estimate (lastRefresh (batchRefresh batchSize) n)) atTop (𝓝 truth) :=
  hconsistent.comp (batchRefresh_lastRefresh_tendsto batchSize hpositive)

/-- Unit batches refresh after every observation. -/
theorem unitBatch_refresh (n : ℕ) : batchRefresh (fun _ => 1) n = true := by
  have h := batchRefresh_at_boundary (fun _ => 1) (fun _ => Nat.zero_lt_succ 0) n
  simpa [batchBoundary] using h

end QubitOracle.AdaptiveDesign.SequentialRidgeController
