import QubitOracle.Paper.TerminalDeletedSet
import QubitOracle.Paper.LimitAssembly

noncomputable section

namespace QubitOracle.Paper

open scoped BigOperators
open Filter

local instance : NormedAddCommGroup OracleMatrix :=
  Matrix.frobeniusNormedAddCommGroup

local instance : NormedSpace ℝ OracleMatrix :=
  Matrix.frobeniusNormedSpace

local instance : NormSMulClass ℝ OracleMatrix :=
  Matrix.frobeniusNormSMulClass

/-- Normalized full mixed-information sum through one-based endpoint `n`. -/
def mixedObservedInformationAverage
    (theta : Fin 3 → ℝ) (axis : ℕ → Fin 3 → ℝ) (n : ℕ) : OracleMatrix :=
  (n : ℝ)⁻¹ •
    ∑ i ∈ terminalObservedSet n,
      QubitOracle.mixedAxisFisher theta (axis i)

/-- Normalized information omitted by the terminal likelihood. -/
def mixedDeletedInformationAverage
    (theta : Fin 3 → ℝ) (axis : ℕ → Fin 3 → ℝ)
    (exploration : ℕ → ℕ) (n : ℕ) : OracleMatrix :=
  (n : ℝ)⁻¹ •
    ∑ i ∈ terminalDeletedSet n exploration,
      QubitOracle.mixedAxisFisher theta (axis i)

/-- Normalized information retained by the terminal likelihood. -/
def mixedRetainedInformationAverage
    (theta : Fin 3 → ℝ) (axis : ℕ → Fin 3 → ℝ)
    (exploration : ℕ → ℕ) (n : ℕ) : OracleMatrix :=
  (n : ℝ)⁻¹ •
    ∑ i ∈ terminalTailSet n exploration,
      QubitOracle.mixedAxisFisher theta (axis i)

/-- Scalar right-hand side of `eq:SI_delete_mixed`. -/
def mixedTerminalDeletionBound
    (theta : Fin 3 → ℝ) (exploration : ℕ → ℕ) (n : ℕ) : ℝ :=
  ((terminalBurnInCutoff n +
      ∑ i ∈ terminalObservedSet n, exploration i : ℕ) : ℝ) /
    ((n : ℝ) * (1 - QubitOracle.blochNormSq theta))

theorem terminalTailSet_subset_observed
    (n : ℕ) (exploration : ℕ → ℕ) :
    terminalTailSet n exploration ⊆ terminalObservedSet n := by
  intro i hi
  have h := (mem_terminalTailSet_iff n exploration i).1 hi
  apply Finset.mem_Icc.mpr
  constructor
  · omega
  · exact h.2.1

/-- The full normalized sum is retained plus deleted, hence retained is full
minus deleted. -/
theorem mixedTerminalInformationAverage_decompose
    (theta : Fin 3 → ℝ) (axis : ℕ → Fin 3 → ℝ)
    (exploration : ℕ → ℕ) (n : ℕ) :
    mixedRetainedInformationAverage theta axis exploration n =
      mixedObservedInformationAverage theta axis n -
        mixedDeletedInformationAverage theta axis exploration n := by
  unfold mixedRetainedInformationAverage mixedObservedInformationAverage
    mixedDeletedInformationAverage terminalDeletedSet
  have hsum := Finset.sum_sdiff
    (f := fun i => QubitOracle.mixedAxisFisher theta (axis i))
    (terminalTailSet_subset_observed n exploration)
  rw [← hsum, smul_add]
  abel

/-- The exact deletion inequality plus convergence of its scalar right-hand
side forces the deleted information itself to vanish. -/
theorem mixedDeletedInformationAverage_tendsto_zero
    (theta : Fin 3 → ℝ)
    (hinterior : QubitOracle.blochNormSq theta < 1)
    (axis : ℕ → Fin 3 → ℝ)
    (haxis : ∀ i, QubitOracle.blochNormSq (axis i) = 1)
    (exploration : ℕ → ℕ)
    (hbound : Tendsto
      (mixedTerminalDeletionBound theta exploration) atTop (nhds 0)) :
    Tendsto
      (mixedDeletedInformationAverage theta axis exploration)
      atTop (nhds 0) := by
  apply (tendsto_iff_norm_sub_tendsto_zero).2
  have hnorm : ∀ᶠ n in atTop,
      ‖mixedDeletedInformationAverage theta axis exploration n‖ ≤
        mixedTerminalDeletionBound theta exploration n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : 0 < n := by omega
    exact Label.eq_SI_delete_mixed
      theta hinterior axis haxis n hnpos exploration
  have hsqueeze : Tendsto
      (fun n => ‖mixedDeletedInformationAverage theta axis exploration n‖)
      atTop (nhds 0) :=
    squeeze_zero'
      (Eventually.of_forall fun _ => norm_nonneg _)
      hnorm hbound
  simpa only [sub_zero] using hsqueeze

namespace Label

/-- `eq:SI_retained_mixed`: the exact retained mixed-information limit follows
from the full information theorem and the explicit vanishing deletion bound. -/
theorem eq_SI_retained_mixed
    (theta : Fin 3 → ℝ)
    (hinterior : QubitOracle.blochNormSq theta < 1)
    (axis : ℕ → Fin 3 → ℝ)
    (haxis : ∀ i, QubitOracle.blochNormSq (axis i) = 1)
    (exploration : ℕ → ℕ) (target : OracleMatrix)
    (hfull : Tendsto
      (mixedObservedInformationAverage theta axis) atTop (nhds target))
    (hbound : Tendsto
      (mixedTerminalDeletionBound theta exploration) atTop (nhds 0)) :
    Tendsto
      (mixedRetainedInformationAverage theta axis exploration)
      atTop (nhds target) := by
  exact retainedLimit_of_fullLimit_of_deletedLimit
    (mixedObservedInformationAverage theta axis)
    (mixedDeletedInformationAverage theta axis exploration)
    (mixedRetainedInformationAverage theta axis exploration)
    target
    (mixedTerminalInformationAverage_decompose theta axis exploration)
    hfull
    (mixedDeletedInformationAverage_tendsto_zero
      theta hinterior axis haxis exploration hbound)

end Label

end QubitOracle.Paper
