-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.TracelessHermitianDimension
import QubitOracle.AdaptiveDesign.PVMGeneralGeometry

/-! A complete spectral exploration library with exactly D^2-1 labelled
bases, in every finite dimension D>=2. Eigenbasis choices include a fixed
resolution of repeated eigenvalues. -/
namespace QubitOracle.AdaptiveDesign.SpectralExplorationLibrary
open QubitOracle.Paper GlobalPFSIC GlobalPFSICHermitian GlobalPFSICBorn
open PVMGeometry TracelessHermitianDimension
open scoped BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def spectralBasis {d : ℕ} (A : HermitianSpace (d+1)) : Action d :=
  ⟨(toMatrix_isHermitian A).eigenvectorUnitary.val,
    (toMatrix_isHermitian A).eigenvectorUnitary.property⟩

theorem spectral_expansion {d : ℕ} (A : HermitianSpace (d+1)) :
    A=∑ k, (toMatrix_isHermitian A).eigenvalues k • basisEffect (spectralBasis A) k := by
  apply toMatrix_injective
  change toMatrix A=toMatrixLinear (d+1) _
  rw [map_sum]
  simp only [toMatrixLinear,LinearMap.coe_mk,AddHom.coe_mk,toMatrix_smul]
  conv_lhs => rw [(toMatrix_isHermitian A).spectral_theorem,Unitary.conjStarAlgAut_apply]
  have hd : Matrix.diagonal (fun k => ((toMatrix_isHermitian A).eigenvalues k:ℂ))=
      ∑ k, (toMatrix_isHermitian A).eigenvalues k • projector (coordinate k) := by
    ext i j
    by_cases hij : i=j
    · subst j; simp [Matrix.diagonal_apply,projector,Matrix.vecMulVec_apply,coordinate,Pi.single_apply,
      Matrix.sum_apply,Matrix.smul_apply]
    · simp [Matrix.diagonal_apply,projector,Matrix.vecMulVec_apply,coordinate,Pi.single_apply,
        Matrix.sum_apply,Matrix.smul_apply,hij]
  change (spectralBasis A).matrix *
    Matrix.diagonal (fun k => ((toMatrix_isHermitian A).eigenvalues k:ℂ)) *
      (spectralBasis A).matrix.conjTranspose = _
  rw [hd,Matrix.mul_sum,Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Matrix.mul_smul,Matrix.smul_mul]
  rfl

theorem sum_effects {d : ℕ} (U : Action d) :
    (∑ k, basisEffect U k)=identity (d+1) := by
  apply toMatrix_injective
  change toMatrixLinear (d+1) _=1
  rw [map_sum]
  exact basisEffect_sum U

theorem identity_inner {n : ℕ} (A : HermitianSpace n) :
    ⟪identity n,A⟫_ℝ=traceMap n A := by
  rw [inner_eq_trace]
  simp [identity,traceMap]

def bases (d : ℕ) : Fin ((d+1)^2-1) → Action d :=
  fun j => spectralBasis ((tracelessBasis (d+1) (by omega)) j).val

theorem identifies (d : ℕ) (hd : 0<d) (A : HermitianSpace (d+1))
    (h : ∀ j k, ⟪basisEffect (bases d j) k,A⟫_ℝ=0) : A=0 := by
  have hk : 0<(d+1)^2-1 := by
    apply Nat.sub_pos_of_lt
    nlinarith
  let j0 : Fin ((d+1)^2-1) := ⟨0,hk⟩
  have ht : traceMap (d+1) A=0 := by
    rw [← identity_inner,← sum_effects (bases d j0),sum_inner]
    simp [h]
  let a : traceless (d+1) := ⟨A,ht⟩
  let b := tracelessBasis (d+1) (by omega)
  have hb (j : Fin ((d+1)^2-1)) : ⟪(b j).val,A⟫_ℝ=0 := by
    rw [spectral_expansion (b j).val,sum_inner]
    change (∑ k, ⟪(toMatrix_isHermitian (b j).val).eigenvalues k •
      basisEffect (bases d j) k,A⟫_ℝ)=0
    simp [real_inner_smul_left,h]
  have he : A=∑ j, (b.repr a j) • (b j).val := by
    have hh := congrArg ((traceless (d+1)).subtype) (b.sum_repr a)
    simpa only [map_sum,map_smul,Submodule.subtype_apply,a] using hh.symm
  have hz : ⟪A,A⟫_ℝ=0 := by
    conv_lhs => lhs; rw [he]
    simp [sum_inner,real_inner_smul_left,hb]
  exact (inner_self_eq_zero.mp hz)

def library (d : ℕ) (hd : 0<d) : PVMGeneralGeometry.ExplorationLibrary d where
  count := (d+1)^2-1
  count_pos := by
    apply Nat.sub_pos_of_lt
    nlinarith
  basis := bases d
  identifies := identifies d hd

@[simp] theorem library_count (d : ℕ) (hd : 0<d) : (library d hd).count=(d+1)^2-1 := rfl

end
end QubitOracle.AdaptiveDesign.SpectralExplorationLibrary

-/
