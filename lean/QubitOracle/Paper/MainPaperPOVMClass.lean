import QubitOracle.FiniteGillMassar

set_option autoImplicit false

/-! The all-finite-POVM class displayed at the start of Section 5.
The union over positive outcome counts is represented by a dependent
sum. Arbitrary finite outcome types are related to it by proved
relabeling, not restricted to the paper's algorithmic action spaces. -/
namespace QubitOracle.Paper.MainPaperPOVMClass
open QubitOracle
open scoped BigOperators
noncomputable section

def POVMClass (D : ℕ) := Σ m : ℕ+, FinitePOVM (Fin D) (Fin (m : ℕ))

abbrev History (O : Type) := List O

abbrev Policy (D : ℕ) (O : Type) [Fintype O] :=
  History O → FinitePOVM (Fin D) O

def relabel {D : ℕ} {O Z : Type} [Fintype O] [Fintype Z]
    (P : FinitePOVM (Fin D) O) (e : O ≃ Z) : FinitePOVM (Fin D) Z where
  effect z := P.effect (e.symm z)
  positive z := P.positive (e.symm z)
  complete := by
    have he : ∑ z : Z, P.effect (e.symm z) = ∑ o : O, P.effect o :=
      Equiv.sum_comp e.symm P.effect
    exact he.trans P.complete

theorem relabel_effect {D : ℕ} {O Z : Type} [Fintype O] [Fintype Z]
    (P : FinitePOVM (Fin D) O) (e : O ≃ Z) (o : O) :
    (relabel P e).effect (e o) = P.effect o := by
  simp [relabel]

def toClass {D : ℕ} {O : Type} [Fintype O] [Nonempty O]
    (P : FinitePOVM (Fin D) O) : POVMClass D :=
  ⟨⟨Fintype.card O, Fintype.card_pos⟩, relabel P (Fintype.equivFin O)⟩

theorem toClass_effect {D : ℕ} {O : Type} [Fintype O] [Nonempty O]
    (P : FinitePOVM (Fin D) O) (o : O) :
    (toClass P).2.effect ((Fintype.equivFin O) o) = P.effect o :=
  relabel_effect P (Fintype.equivFin O) o

end
end QubitOracle.Paper.MainPaperPOVMClass
