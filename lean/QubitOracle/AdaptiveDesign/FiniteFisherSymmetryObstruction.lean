import QubitOracle.AdaptiveDesign.PureFisherLoewner
import Mathlib.LinearAlgebra.Matrix.Permutation

/-! Literal finite-outcome obstruction cited in Sections 1 and 4.2.
An effect can be diagonalized in a basis with positive mass in a tangent
coordinate. It then contributes no Fisher information at the center,
making the Gill--Massar budget strictly deficient. -/
namespace QubitOracle.AdaptiveDesign.FiniteFisherSymmetryObstruction
open QubitOracle GlobalPFSICHermitian
open scoped BigOperators ComplexOrder
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ} {O : Type} [Fintype O]

theorem strict_budget (P : FinitePOVM (Fin (d+1)) O)
    (y : O) (hzero : referenceOffdiagEnergy P y=0)
    (hmass : 0 < tangentDiagonalMass P y) :
    (referenceFisher P).trace < (d:ℝ) := by
  rw [referenceFisher_trace,← sum_tangentDiagonalMass P]
  apply Finset.sum_lt_sum
  · intro z _
    exact referenceOutcomeRatio_le_diagonalMass P z
  · refine ⟨y,Finset.mem_univ y,?_⟩
    simpa [hzero,safeRatio] using hmass

theorem permutation_unitary {D : ℕ} (e : Equiv.Perm (Fin D)) :
    e.permMatrix ℂ ∈ Matrix.unitaryGroup (Fin D) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  rw [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_permMatrix,
    ← Matrix.permMatrix_mul]
  simp

theorem permutation_conjugation {D : ℕ} (e : Equiv.Perm (Fin D))
    (A : Matrix (Fin D) (Fin D) ℂ) :
    e.permMatrix ℂ * A * (e.permMatrix ℂ).conjTranspose = A.submatrix e e := by
  rw [Matrix.conjTranspose_permMatrix]
  simp [Equiv.Perm.permMatrix,PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  rfl

theorem diagonalization_obstruction (P : FinitePOVM (Fin (d+1)) O)
    (hd : 0 < d) (y : O) (hne : P.effect y ≠ 0) :
    ∃ U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ,
      ∃ hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ,
      (referenceFisher (PureFisherLoewner.rotated P U hU)).trace < (d:ℝ) := by
  classical
  let hE := (P.positive y).isHermitian
  obtain ⟨r,hr⟩ : ∃ r : Fin (d+1), 0 < hE.eigenvalues r := by
    by_contra h
    push_neg at h
    have he : hE.eigenvalues=0 := by
      funext r
      exact le_antisymm (h r) ((P.positive y).eigenvalues_nonneg r)
    exact hne (hE.eigenvalues_eq_zero_iff.mp he)
  let one : Fin (d+1) := ⟨1,by omega⟩
  let s : Fin (d+1) := if r=0 then one else 0
  have hrs : r ≠ s := by
    dsimp [s,one]
    split_ifs with h
    · subst r; simp
    · exact h
  let e : Equiv.Perm (Fin (d+1)) := Equiv.swap 0 s
  let U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
    e.permMatrix ℂ * hE.eigenvectorUnitary.val.conjTranspose
  have hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ := by
    apply (Matrix.unitaryGroup (Fin (d+1)) ℂ).mul_mem (permutation_unitary e)
    apply Matrix.mem_unitaryGroup_iff.mpr
    simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_conjTranspose] using
      Matrix.mem_unitaryGroup_iff'.mp hE.eigenvectorUnitary.property
  let R := PureFisherLoewner.rotated P U hU
  have he : R.effect y =
      (Matrix.diagonal (fun i => (hE.eigenvalues i:ℂ))).submatrix e e := by
    have hu := Matrix.mem_unitaryGroup_iff'.mp hE.eigenvectorUnitary.property
    change hE.eigenvectorUnitary.val.conjTranspose*hE.eigenvectorUnitary.val=1 at hu
    have hs := hE.spectral_theorem
    change e.permMatrix ℂ * hE.eigenvectorUnitary.val.conjTranspose * P.effect y *
      (e.permMatrix ℂ * hE.eigenvectorUnitary.val.conjTranspose).conjTranspose = _
    conv_lhs => arg 1; arg 2; rw [hs]
    simp only [Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose,
      RCLike.ofReal_eq_complex_ofReal,
      Function.comp_def]
    rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
    have hc : hE.eigenvectorUnitary.val.conjTranspose *
        (hE.eigenvectorUnitary.val * Matrix.diagonal (fun i => (hE.eigenvalues i:ℂ)) *
        hE.eigenvectorUnitary.val.conjTranspose) * hE.eigenvectorUnitary.val =
          Matrix.diagonal (fun i => (hE.eigenvalues i:ℂ)) := by
      simp only [← Matrix.mul_assoc,hu,Matrix.one_mul]
      simp only [Matrix.mul_assoc,hu,Matrix.mul_one]
    simpa only [Matrix.mul_assoc] using
      (congrArg (fun M => e.permMatrix ℂ*M*(e.permMatrix ℂ).conjTranspose) hc).trans
        (permutation_conjugation e _)
  have hz : referenceOffdiagEnergy R y=0 := by
    unfold referenceOffdiagEnergy
    apply Finset.sum_eq_zero
    intro k _
    rw [he]
    have hk0 : (0:Fin (d+1)) ≠ k.succ := fun h => (Fin.succ_ne_zero k) h.symm
    simp only [Matrix.submatrix_apply,Matrix.diagonal_apply,
      if_neg (e.injective.ne hk0),Complex.normSq_zero]
  have hj : e.symm r ≠ 0 := by
    intro h
    have hh := congrArg e h
    simp only [Equiv.apply_symm_apply,e,Equiv.swap_apply_left] at hh
    exact hrs hh
  obtain ⟨k,hk⟩ : ∃ k : Fin d, e.symm r=k.succ := by
    cases heq : e.symm r using Fin.cases with
    | zero => exact (hj heq).elim
    | succ k => exact ⟨k,rfl⟩
  have hm : 0 < tangentDiagonalMass R y := by
    have hl := Finset.single_le_sum
      (fun a _ => (Complex.nonneg_iff.mp ((R.positive y).diag_nonneg (i:=a.succ))).1)
      (Finset.mem_univ k)
    have hdg : (R.effect y k.succ k.succ).re=hE.eigenvalues r := by
      rw [he]
      simp only [Matrix.submatrix_apply,Matrix.diagonal_apply,if_pos rfl,Complex.ofReal_re]
      rw [← hk,Equiv.apply_symm_apply]
      simp
    exact lt_of_lt_of_le (hdg.symm ▸ hr) hl
  exact ⟨U,hU,strict_budget R y hz hm⟩

theorem no_finite_universal_fisher_symmetry (P : FinitePOVM (Fin (d+1)) O)
    (hd : 0 < d) :
    ¬ ∀ U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ,
      ∀ hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ,
      referenceFisher (PureFisherLoewner.rotated P U hU) = (1/2:ℝ) • 1 := by
  classical
  have hy : ∃ y, P.effect y ≠ 0 := by
    by_contra h
    push_neg at h
    have hc := P.complete
    simp only [h,Finset.sum_const_zero] at hc
    exact zero_ne_one hc
  obtain ⟨y,hy⟩ := hy
  obtain ⟨U,hU,ht⟩ := diagonalization_obstruction P hd y hy
  intro h
  rw [h U hU,Matrix.trace_smul,Matrix.trace_one] at ht
  simp only [Fintype.card_sum,Fintype.card_fin,smul_eq_mul,Nat.cast_add] at ht
  linarith

end
end QubitOracle.AdaptiveDesign.FiniteFisherSymmetryObstruction
