import QubitOracle.Paper.AdaptiveTrajectoryExperiment
import QubitOracle.FiniteGillMassar
/-! Supporting definitions and proved lemmas used by the manuscript. -/

namespace QubitOracle.Paper

open Filter MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- Physical one-qubit parameters, represented by their Bloch vectors. -/
abbrev OneQubitPhysicalParameter :=
  {theta : Fin 3 → ℝ // QubitOracle.blochNormSq theta ≤ 1}










/--
Protocol indexing uses coordinate zero for initialization.  Coordinate `k+1`
uses cyclic Pauli axis `k`, exactly matching `oneQubitRLSNoise`.
-/
def oneQubitCyclicProtocolSlot : ℕ → Fin 3
  | 0 => 0
  | k + 1 => ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩

















end

end QubitOracle.Paper
