import QubitOracle.Paper.DeletedMixedInformation

noncomputable section

namespace QubitOracle.Paper

open scoped BigOperators

local instance : NormedAddCommGroup OracleMatrix :=
  Matrix.frobeniusNormedAddCommGroup

local instance : NormedSpace ℝ OracleMatrix :=
  Matrix.frobeniusNormedSpace

local instance : NormSMulClass ℝ OracleMatrix :=
  Matrix.frobeniusNormSMulClass

/-- All one-based observation indices through endpoint `n`. -/
def terminalObservedSet (n : ℕ) : Finset ℕ :=
  Finset.Icc 1 n

/-- Observations omitted from the terminal likelihood. -/
def terminalDeletedSet (n : ℕ) (exploration : ℕ → ℕ) : Finset ℕ :=
  terminalObservedSet n \ terminalTailSet n exploration

/-- Burn-in part of the omitted observations. -/
def terminalBurnInSet (n : ℕ) : Finset ℕ :=
  (terminalObservedSet n).filter
    (fun i => i ≤ terminalBurnInCutoff n)

/-- Realized-exploration part of the omitted observations. -/
def terminalExplorationSet
    (n : ℕ) (exploration : ℕ → ℕ) : Finset ℕ :=
  (terminalObservedSet n).filter (fun i => exploration i ≠ 0)

theorem terminalDeletedSet_subset_burnIn_union_exploration
    (n : ℕ) (exploration : ℕ → ℕ) :
    terminalDeletedSet n exploration ⊆
      terminalBurnInSet n ∪ terminalExplorationSet n exploration := by
  intro i hi
  have hiobs : i ∈ terminalObservedSet n :=
    (Finset.mem_sdiff.mp hi).1
  have hnret : i ∉ terminalTailSet n exploration :=
    (Finset.mem_sdiff.mp hi).2
  by_cases hburn : i ≤ terminalBurnInCutoff n
  · exact Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨hiobs, hburn⟩)
  · have hz : exploration i ≠ 0 := by
      intro hz0
      apply hnret
      apply (mem_terminalTailSet_iff n exploration i).2
      have hobs := Finset.mem_Icc.mp hiobs
      exact ⟨Nat.lt_of_not_ge hburn, hobs.2, hz0⟩
    exact Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨hiobs, hz⟩)

theorem terminalBurnInSet_card_le (n : ℕ) :
    (terminalBurnInSet n).card ≤ terminalBurnInCutoff n := by
  have hsubset : terminalBurnInSet n ⊆
      Finset.Icc 1 (terminalBurnInCutoff n) := by
    intro i hi
    have h := Finset.mem_filter.mp hi
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp h.1).1, h.2⟩
  calc
    (terminalBurnInSet n).card ≤
        (Finset.Icc 1 (terminalBurnInCutoff n)).card :=
      Finset.card_le_card hsubset
    _ = terminalBurnInCutoff n := by
      rw [Nat.card_Icc]
      omega

theorem terminalExplorationSet_card_le_sum
    (n : ℕ) (exploration : ℕ → ℕ) :
    (terminalExplorationSet n exploration).card ≤
      ∑ i ∈ terminalObservedSet n, exploration i := by
  calc
    (terminalExplorationSet n exploration).card =
        ∑ i ∈ terminalExplorationSet n exploration, 1 :=
      Finset.card_eq_sum_ones _
    _ ≤ ∑ i ∈ terminalExplorationSet n exploration,
        exploration i := by
      exact Finset.sum_le_sum fun i hi =>
        Nat.one_le_iff_ne_zero.mpr (Finset.mem_filter.mp hi).2
    _ ≤ ∑ i ∈ terminalObservedSet n, exploration i :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- Exact deterministic count bound used in the retained-information proof. -/
theorem terminalDeletedSet_card_le
    (n : ℕ) (exploration : ℕ → ℕ) :
    (terminalDeletedSet n exploration).card ≤
      terminalBurnInCutoff n +
        ∑ i ∈ terminalObservedSet n, exploration i := by
  calc
    (terminalDeletedSet n exploration).card ≤
        (terminalBurnInSet n ∪
          terminalExplorationSet n exploration).card :=
      Finset.card_le_card
        (terminalDeletedSet_subset_burnIn_union_exploration n exploration)
    _ ≤ (terminalBurnInSet n).card +
        (terminalExplorationSet n exploration).card :=
      Finset.card_union_le _ _
    _ ≤ terminalBurnInCutoff n +
        ∑ i ∈ terminalObservedSet n, exploration i :=
      Nat.add_le_add
        (terminalBurnInSet_card_le n)
        (terminalExplorationSet_card_le_sum n exploration)

namespace Label

/-- `eq:SI_delete_mixed`: exact terminal-set form of the normalized deleted
mixed-information bound. -/
theorem eq_SI_delete_mixed
    (theta : Fin 3 → ℝ)
    (hinterior : QubitOracle.blochNormSq theta < 1)
    (axis : ℕ → Fin 3 → ℝ)
    (haxis : ∀ i, QubitOracle.blochNormSq (axis i) = 1)
    (n : ℕ) (hn : 0 < n) (exploration : ℕ → ℕ) :
    ‖(n : ℝ)⁻¹ •
        ∑ i ∈ terminalDeletedSet n exploration,
          QubitOracle.mixedAxisFisher theta (axis i)‖ ≤
      ((terminalBurnInCutoff n +
          ∑ i ∈ terminalObservedSet n, exploration i : ℕ) : ℝ) /
        ((n : ℝ) * (1 - QubitOracle.blochNormSq theta)) := by
  exact eq_SI_delete_mixed_of_card_bound
    theta hinterior axis haxis n (terminalBurnInCutoff n)
    (∑ i ∈ terminalObservedSet n, exploration i) hn
    (terminalDeletedSet n exploration)
    (terminalDeletedSet_card_le n exploration)

end Label

end QubitOracle.Paper
