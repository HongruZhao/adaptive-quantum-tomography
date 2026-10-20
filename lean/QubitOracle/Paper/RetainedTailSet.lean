import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Finset.Interval

noncomputable section

namespace QubitOracle.Paper

/-- Paper burn-in cutoff `q_n = ceil(n^(1/3))`. -/
def terminalBurnInCutoff (n : ℕ) : ℕ :=
  ⌈Real.rpow (n : ℝ) (1 / 3 : ℝ)⌉₊

/-- One-based retained terminal indices: after burn-in and not exploration. -/
def terminalTailSet (n : ℕ) (exploration : ℕ → ℕ) : Finset ℕ :=
  (Finset.Icc (terminalBurnInCutoff n + 1) n).filter
    (fun i => exploration i = 0)

/-- Number of observations retained by the terminal likelihood. -/
def terminalRetainedCount (n : ℕ) (exploration : ℕ → ℕ) : ℕ :=
  (terminalTailSet n exploration).card

/-- Extensional form of the retained-tail definition. -/
theorem mem_terminalTailSet_iff
    (n : ℕ) (exploration : ℕ → ℕ) (i : ℕ) :
    i ∈ terminalTailSet n exploration ↔
      terminalBurnInCutoff n < i ∧ i ≤ n ∧ exploration i = 0 := by
  simp only [terminalTailSet, Finset.mem_filter, Finset.mem_Icc]
  omega

namespace Label

/-- Supplement equation `SI_tail_set`. -/
theorem eq_SI_tail_set (n : ℕ) (exploration : ℕ → ℕ) :
    terminalBurnInCutoff n =
        ⌈Real.rpow (n : ℝ) (1 / 3 : ℝ)⌉₊ ∧
      terminalTailSet n exploration =
        (Finset.Icc (terminalBurnInCutoff n + 1) n).filter
          (fun i => exploration i = 0) ∧
      terminalRetainedCount n exploration =
        (terminalTailSet n exploration).card := by
  simp [terminalBurnInCutoff, terminalTailSet, terminalRetainedCount]

end Label
end QubitOracle.Paper
