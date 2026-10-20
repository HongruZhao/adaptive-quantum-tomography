import Mathlib

/-! Supporting definitions and proved lemmas used by the manuscript. -/
namespace QubitOracle.AdaptiveDesign.P1
open Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section

def batchEndpoint (m : Nat → Nat) (j : Nat) : Nat :=
  ∑ k ∈ Finset.range j, m k

def batchRefresh (m : Nat → Nat) (n : Nat) : Bool := by
  classical
  exact decide (∃ j, batchEndpoint m j = n)

theorem batchEndpoint_ge_index (m : Nat → Nat) (hm : ∀ j, 0 < m j) :
    ∀ j, j ≤ batchEndpoint m j := by
  intro j
  induction j with
  | zero => simp [batchEndpoint]
  | succ j ih =>
    simp only [batchEndpoint, Finset.sum_range_succ] at *
    have h := hm j
    omega

theorem batchEndpoint_strictMono (m : Nat → Nat) (hm : ∀ j, 0 < m j) :
    StrictMono (batchEndpoint m) := by
  apply strictMono_nat_of_lt_succ
  intro j
  simp only [batchEndpoint, Finset.sum_range_succ]
  exact Nat.lt_add_of_pos_right (hm j)

theorem batchRefresh_unbounded (m : Nat → Nat) (hm : ∀ j, 0 < m j) :
    ∀ K, ∃ n, K ≤ n ∧ batchRefresh m n = true := by
  intro K
  refine ⟨batchEndpoint m K, batchEndpoint_ge_index m hm K, ?_⟩
  simp only [batchRefresh, decide_eq_true_eq]
  exact ⟨K, rfl⟩

theorem batchRefresh_at_endpoint (m : Nat → Nat) (j : Nat) :
    batchRefresh m (batchEndpoint m j) = true := by
  simp only [batchRefresh, decide_eq_true_eq]
  exact ⟨j, rfl⟩

theorem batchRefresh_false_inside (m : Nat → Nat) (hm : ∀ j, 0 < m j)
    (j n : Nat) (hl : batchEndpoint m j < n)
    (hu : n < batchEndpoint m (j+1)) : batchRefresh m n = false := by
  simp only [batchRefresh, decide_eq_false_iff_not]
  rintro ⟨k, hk⟩
  have hmono := batchEndpoint_strictMono m hm
  have hlow : j < k := hmono.lt_iff_lt.mp (hk ▸ hl)
  have hhigh : k < j+1 := hmono.lt_iff_lt.mp (hk ▸ hu)
  omega




end
end QubitOracle.AdaptiveDesign.P1
