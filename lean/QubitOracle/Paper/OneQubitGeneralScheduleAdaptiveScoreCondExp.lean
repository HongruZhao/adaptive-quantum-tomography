import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.AdaptiveTrajectoryExperiment
import QubitOracle.Paper.ConcreteProtocolA1A3
import QubitOracle.Paper.MixedProbabilityFloor
import QubitOracle.Paper.OneQubitCyclicBornPath
import QubitOracle.Paper.OneQubitGeneralScheduleAdaptiveBornProtocol
/-! Supporting definitions and proved lemmas used by the manuscript. -/

namespace QubitOracle.Paper

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

local instance generalScheduleScoreMeasurableSpaceBinaryOutcome :
    MeasurableSpace BinaryOutcome := ⊤

local instance generalScheduleScoreNonemptyBinaryOutcome :
    Nonempty BinaryOutcome := ⟨.plus⟩

/-- Every coordinate of a three-dimensional Euclidean vector is bounded by
its norm.  Kept local to avoid importing an incompatible legacy instance. -/
private theorem generalSchedule_abs_apply_le_norm
    (x : EuclideanSpace Real (Fin 3)) (j : Fin 3) :
    |x j| ≤ ‖x‖ := by
  have hCoordinate :
      ‖x j‖ ^ 2 ≤ ∑ k : Fin 3, ‖x k‖ ^ 2 := by
    exact Finset.single_le_sum
      (fun k _ => sq_nonneg (‖x k‖)) (Finset.mem_univ j)
  have hSquare : |x j| ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simpa only [Real.norm_eq_abs] using hCoordinate
  nlinarith [abs_nonneg (x j), norm_nonneg x]

/-- A finite prefix through coordinate `k`. -/
abbrev GeneralSchedulePrefix (k : Nat) :=
  (i : ↥(Finset.Iic k)) → AdaptiveOutcomeProcess BinaryOutcome i.1




/-- A two-constructor sum can be expanded without relying on constructor
ordering in the generated `Fintype` instance. -/
theorem sum_binaryOutcome (f : BinaryOutcome → Real) :
    (∑ y, f y) = f .plus + f .minus := by
  have hUniv : (Finset.univ : Finset BinaryOutcome) = {.plus, .minus} := by
    ext y
    cases y <;> simp
  rw [show (∑ y, f y) =
      ∑ y ∈ (Finset.univ : Finset BinaryOutcome), f y by simp]
  rw [hUniv]
  simp











end

end QubitOracle.Paper
