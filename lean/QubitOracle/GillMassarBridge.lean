import QubitOracle.FiniteGillMassar
import QubitOracle.TwoBasis
/-! Supporting definitions and proved lemmas used by the manuscript. -/

namespace QubitOracle

noncomputable section

/-- The rank-one tangent chart in dimension `n + 1` has `2n` real
coordinates. -/
theorem tangentIndex_card (n : ℕ) :
    Fintype.card (TangentIndex n) = 2 * n := by
  simp [TangentIndex]
  omega

/-- Normalized Gill--Massar trace budget for an information matrix on the
rank-one tangent chart.  This is a property, not an axiom asserting that any
particular measurement class satisfies it. -/
def SatisfiesGillMassarTraceBudget {n : ℕ}
    (M : Matrix (TangentIndex n) (TangentIndex n) ℝ) : Prop :=
  M.trace ≤ (n : ℝ)

/-- The equal two-basis information matrix is positive definite. -/
theorem equalMixtureFisher_posDef {n : ℕ} (F : OracleFrame n) :
    (equalMixtureFisher F).PosDef := by
  rw [equalMixtureFisher_eq_half_identity]
  exact Matrix.PosDef.one.smul (by norm_num)

/-- The equal two-basis information matrix saturates, hence satisfies, the
normalized trace budget. -/
theorem equalMixture_satisfies_gillMassarTraceBudget {n : ℕ}
    (F : OracleFrame n) :
    SatisfiesGillMassarTraceBudget (equalMixtureFisher F) := by
  rw [SatisfiesGillMassarTraceBudget, equalMixtureFisher_eq_half_identity,
    Matrix.trace_smul, Matrix.trace_one, tangentIndex_card]
  simp only [Nat.cast_mul, Nat.cast_ofNat, smul_eq_mul]
  ring_nf
  exact le_rfl









/-- Every finite POVM in the rank-one reference chart satisfies the trace
budget, now as a proved theorem rather than a hypothesis. -/
theorem referenceFisher_satisfies_gillMassarTraceBudget
    {n : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (n + 1)) O) :
    SatisfiesGillMassarTraceBudget (referenceFisher P) :=
  rankOne_reference_gillMassar P










end


end QubitOracle
