import QubitOracle.AdaptiveDesign.SinglePVMDimension
import QubitOracle.AdaptiveDesign.GlobalPFSICBornModel
import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel
import QubitOracle.AdaptiveDesign.PVMGeometry
import QubitOracle.AdaptiveDesign.TracelessHermitianDimension
set_option autoImplicit false

/-! The necessary B >= D+1 number of bases in Supplement S2.4.
The shared identity removes one generator from each additional basis;
this is stronger than merely counting all B*D recorded effects. -/
namespace QubitOracle.Paper.MainPaperBasisBound
open QubitOracle QubitOracle.Paper QubitOracle.AdaptiveDesign
open GlobalPFSICHermitian GlobalPFSICBorn PureMatrixController
open PVMGeometry TracelessHermitianDimension
open scoped BigOperators
noncomputable section

def reducedFamily {d B : ℕ} (U : Fin B → Action d) :
    Option (Fin B × Fin d) → HermitianSpace (d+1)
  | none => identity (d+1)
  | some (l,k) => basisEffect (U l) k.succ

theorem effects_mem_reduced_span {d B : ℕ} (U : Fin B → Action d)
    (l : Fin B) (k : Fin (d+1)) :
    basisEffect (U l) k ∈ Submodule.span ℝ (Set.range (reducedFamily U)) := by
  classical
  refine Fin.cases ?_ (fun k => ?_) k
  · have hs : (∑ j, basisEffect (U l) j) = identity (d+1) := by
      apply toMatrix_injective
      change toMatrixLinear (d+1) _ = 1
      rw [map_sum]
      exact basisEffect_sum (U l)
    rw [Fin.sum_univ_succ] at hs
    rw [show basisEffect (U l) 0 = identity (d+1)-∑ j : Fin d,
      basisEffect (U l) j.succ from eq_sub_iff_add_eq.mpr hs]
    apply Submodule.sub_mem
    · exact Submodule.subset_span ⟨none,rfl⟩
    · apply Submodule.sum_mem
      intro j _
      exact Submodule.subset_span ⟨some (l,j),rfl⟩
  · exact Submodule.subset_span ⟨some (l,k),rfl⟩

theorem span_dimension_bound {d B : ℕ} (U : Fin B → Action d) :
    Module.finrank ℝ
      (Submodule.span ℝ (Set.range (fun o : Fin B × Fin (d+1) =>
        basisEffect (U o.1) o.2))) ≤ 1+B*d := by
  classical
  have hle : Submodule.span ℝ (Set.range (fun o : Fin B × Fin (d+1) =>
      basisEffect (U o.1) o.2)) ≤ Submodule.span ℝ (Set.range (reducedFamily U)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨l,k⟩,rfl⟩
    exact effects_mem_reduced_span U l k
  have hcard := finrank_range_le_card (R := ℝ) (reducedFamily U)
  exact (Submodule.finrank_mono hle).trans (by simpa [Set.finrank, Nat.add_comm] using hcard)

theorem necessary_number_of_bases {d B : ℕ} (hd : 0 < d) (U : Fin B → Action d)
    (hspan : Submodule.span ℝ (Set.range (fun o : Fin B × Fin (d+1) =>
      basisEffect (U o.1) o.2)) = ⊤) : d+2 ≤ B := by
  have h := span_dimension_bound U
  rw [hspan,finrank_top,hermitian_finrank] at h
  by_contra hb
  have hB : B ≤ d+1 := by omega
  have hm : B*d ≤ (d+1)*d := Nat.mul_le_mul_right d hB
  nlinarith

theorem one_basis_not_spanning {d : ℕ} (hd : 0 < d) (U : Action d) :
    Submodule.span ℝ (Set.range (fun o : Fin 1 × Fin (d+1) =>
      basisEffect U o.2)) ≠ ⊤ := by
  intro hs
  have h := necessary_number_of_bases hd (fun _ : Fin 1 => U) hs
  omega

end
end QubitOracle.Paper.MainPaperBasisBound
