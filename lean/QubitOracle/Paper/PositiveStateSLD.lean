import QubitOracle.Paper.SLDLinearAlgebra

/-! The positive-definite SLD assertion in Section 2.4, in the original
matrix coordinates as well as an eigenbasis. Spectral diagonalization is
proved by Mathlib; the SLD equation and uniqueness are derived here. -/
namespace QubitOracle.Paper.SLDLinearAlgebra
open scoped ComplexOrder
noncomputable section
set_option maxHeartbeats 1000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem positive_state_sld_exists_unique (rho A : Matrix ι ι ℂ)
    (hrho : rho.PosDef) :
    ∃! L : Matrix ι ι ℂ, rho*L+L*rho=2 • A := by
  let phi := Unitary.conjStarAlgAut ℂ _ hrho.isHermitian.eigenvectorUnitary
  let eig := hrho.isHermitian.eigenvalues
  let B := phi.symm A
  let L := phi (diagonalSLD eig B)
  have heig : ∀ i, 0 < eig i := hrho.eigenvalues_pos
  have hs : rho = phi (Matrix.diagonal (fun i => (eig i:ℂ))) := by
    simpa only [phi,eig,RCLike.ofReal_eq_complex_ofReal,Function.comp_def] using
      hrho.isHermitian.spectral_theorem
  have hL : rho*L+L*rho=2 • A := by
    dsimp only [L]
    rw [hs,← map_mul,← map_mul,← map_add,diagonal_sld_equation eig heig B]
    simpa only [map_nsmul,B,phi.apply_symm_apply]
  refine ⟨L,hL,fun K hK => ?_⟩
  have hD : Matrix.diagonal (fun i => (eig i:ℂ))*phi.symm K+
      phi.symm K*Matrix.diagonal (fun i => (eig i:ℂ))=2 • B := by
    have hh := congrArg phi.symm hK
    rw [hs] at hh
    simpa only [map_add,map_mul,map_nsmul,phi.symm_apply_apply,B] using hh
  calc
    K = phi (phi.symm K) := (phi.apply_symm_apply K).symm
    _ = L := congrArg phi (diagonal_sld_unique eig heig B _ hD)

theorem positive_state_sld_isHermitian (rho A L : Matrix ι ι ℂ)
    (hrho : rho.PosDef) (hA : A.IsHermitian) (hL : rho*L+L*rho=2 • A) :
    L.IsHermitian := by
  obtain ⟨K,hK,hu⟩ := positive_state_sld_exists_unique rho A hrho
  have hs : rho*L.conjTranspose+L.conjTranspose*rho=2 • A := by
    have hh := congrArg Matrix.conjTranspose hL
    simp only [Matrix.conjTranspose_add,Matrix.conjTranspose_mul,
      Matrix.conjTranspose_smul,star_ofNat,hrho.isHermitian.eq,hA.eq] at hh
    simpa only [add_comm] using hh
  exact (hu _ hs).trans (hu _ hL).symm

end
end QubitOracle.Paper.SLDLinearAlgebra
