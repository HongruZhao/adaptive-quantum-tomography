import QubitOracle.Paper.ElementaryReferenceAlgebra
import QubitOracle.AdaptiveDesign.GlobalPFSICLibrary

/-! The actual real/imaginary two-level bases of Appendix S4.1.
The replacement vectors are explicit and their projectors sum to the
identity, so the column matrices are proved unitary.
-/
namespace QubitOracle.Paper.ElementaryPVMBases
open QubitOracle.Paper ProjectiveStateGeometry ElementaryReferenceAlgebra
open QubitOracle.AdaptiveDesign.GlobalPFSIC (coordinate coordinate_projector_sum)
open scoped BigOperators ComplexOrder
noncomputable section
set_option maxHeartbeats 1200000

theorem sum_update_group {I V : Type*} [Fintype I] [DecidableEq I] [AddCommGroup V]
    (f : I → V) (i : I) (v : V) : ∑ k, Function.update f i v k = (∑ k, f k) - f i + v := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]
  have he := Finset.sum_erase_add (s := Finset.univ) (f := f) (Finset.mem_univ i)
  rw [← he]
  abel

def pairVectors {D : ℕ} (r s : Fin D) (q : ℂ) : Fin D → Fin D → ℂ :=
  Function.update (Function.update coordinate r (balanced (coordinate r) (q • coordinate s)))
    s (balanced (coordinate r) (-(q • coordinate s)))

theorem pairVectors_first {D : ℕ} (r s : Fin D) (hrs : r ≠ s) (q : ℂ) :
    pairVectors r s q r = balanced (coordinate r) (q • coordinate s) := by
  simp [pairVectors, hrs]

theorem pairVectors_second {D : ℕ} (r s : Fin D) (q : ℂ) :
    pairVectors r s q s = balanced (coordinate r) (-(q • coordinate s)) := by
  simp [pairVectors]

theorem pairVectors_other {D : ℕ} (r s k : Fin D) (hkr : k ≠ r) (hks : k ≠ s) (q : ℂ) :
    pairVectors r s q k = coordinate k := by
  simp [pairVectors, hkr, hks]

theorem pairVectors_complete {D : ℕ} (r s : Fin D) (hrs : r ≠ s)
    (q : ℂ) (hq : Complex.normSq q = 1) : ∑ k, rankOneDensity (pairVectors r s q k) = 1 := by
  let f := fun k : Fin D => rankOneDensity (coordinate k)
  let P := rankOneDensity (balanced (coordinate r) (q • coordinate s))
  let M := rankOneDensity (balanced (coordinate r) (-(q • coordinate s)))
  have he : (fun k => rankOneDensity (pairVectors r s q k)) =
      Function.update (Function.update f r P) s M := by
    funext k
    by_cases hks : k = s
    · subst k
      simp [pairVectors, M]
    · by_cases hkr : k = r
      · subst k
        simp [pairVectors, P, hrs]
      · simp [pairVectors, f, hks, hkr]
  rw [he, sum_update_group, sum_update_group]
  have hc : ∑ k, f k = 1 := coordinate_projector_sum D
  have hp : P + M = f r + f s := pair_projectors_sum _ _ q hq
  simp only [Function.update_of_ne (Ne.symm hrs)]
  rw [hc]
  calc
    _ = 1 - (f r + f s) + (P + M) := by abel
    _ = 1 := by rw [hp]; abel

def pairMatrix {D : ℕ} (r s : Fin D) (q : ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  fun i k => pairVectors r s q k i

theorem pairMatrix_unitary {D : ℕ} (r s : Fin D) (hrs : r ≠ s)
    (q : ℂ) (hq : Complex.normSq q = 1) : pairMatrix r s q ∈ Matrix.unitaryGroup (Fin D) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  rw [Matrix.star_eq_conjTranspose]
  have he : pairMatrix r s q * (pairMatrix r s q).conjTranspose =
      ∑ k, rankOneDensity (pairVectors r s q k) := by
    ext i j
    simp only [pairMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.sum_apply, rankOneDensity]
  rw [he, pairVectors_complete r s hrs q hq]

abbrev OrderedPair (D : ℕ) := {p : Fin D × Fin D // p.1 < p.2}
abbrev BasisLabel (D : ℕ) := Unit ⊕ (Bool × OrderedPair D)

def basisMatrix {D : ℕ} : BasisLabel D → Matrix (Fin D) (Fin D) ℂ
  | .inl _ => 1
  | .inr (b,p) => pairMatrix p.val.1 p.val.2 (if b then Complex.I else 1)

theorem basisMatrix_unitary {D : ℕ} (l : BasisLabel D) :
    basisMatrix l ∈ Matrix.unitaryGroup (Fin D) ℂ := by
  rcases l with _ | ⟨b,p⟩
  · simp [basisMatrix]
  · apply pairMatrix_unitary _ _ (ne_of_lt p.property)
    cases b <;> norm_num

theorem orderedPair_card (D : ℕ) : Fintype.card (OrderedPair D) = D.choose 2 := by
  rw [Fintype.card_subtype]
  exact pair_count D

theorem basis_count (D : ℕ) : Fintype.card (BasisLabel D) = 1 + 2 * D.choose 2 := by
  simp [BasisLabel, orderedPair_card]

theorem basis_count_real (D : ℕ) : (Fintype.card (BasisLabel D) : ℝ) = (D:ℝ)^2-D+1 := by
  rw [basis_count]
  push_cast
  rw [Nat.cast_choose_two]
  ring

end
end QubitOracle.Paper.ElementaryPVMBases
