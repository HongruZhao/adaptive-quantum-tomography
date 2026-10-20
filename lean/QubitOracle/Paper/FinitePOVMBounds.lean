import QubitOracle.FiniteGillMassar

/-! Literal matrix-order bound on every finite POVM effect in Section 2.1.
The complement is the sum of the other positive effects. -/
namespace QubitOracle.Paper.FinitePOVMBounds
open scoped BigOperators ComplexOrder
noncomputable section
variable {D O : Type} [Fintype D] [DecidableEq D] [Fintype O]

def matrixLE (A B : Matrix D D ℂ) : Prop := (B-A).PosSemidef
def matrixLT (A B : Matrix D D ℂ) : Prop := (B-A).PosDef

theorem effect_complement_positive (P : QubitOracle.FinitePOVM D O) (y : O) :
    (1-P.effect y).PosSemidef := by
  classical
  have hs := Matrix.posSemidef_sum (Finset.univ.erase y)
    (fun z _ => P.positive z)
  have he : ∑ z ∈ Finset.univ.erase y, P.effect z = 1-P.effect y := by
    have hh := Finset.sum_erase_add Finset.univ (P.effect) (Finset.mem_univ y)
    rw [P.complete] at hh
    exact eq_sub_of_add_eq hh
  exact he ▸ hs

theorem effect_order_bounds (P : QubitOracle.FinitePOVM D O) (y : O) :
    matrixLE 0 (P.effect y) ∧ matrixLE (P.effect y) 1 := by
  exact ⟨by simpa [matrixLE] using P.positive y,effect_complement_positive P y⟩

end
end QubitOracle.Paper.FinitePOVMBounds
