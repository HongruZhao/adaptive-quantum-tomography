import QubitOracle.AdaptiveDesign.GeneralPOVMModel
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Ambient informational completeness requires at least D squared outcomes.
The argument complexifies the real Hermitian measurement map; it does not
assume an unproved dimension formula for the Hermitian subspace. -/
namespace QubitOracle.AdaptiveDesign.GeneralPOVM
open QubitOracle.Paper GlobalPFSICHermitian
open scoped BigOperators InnerProductSpace
noncomputable section

variable {d : ℕ} {O : Type} [Fintype O]

def complexAnalysis (P : FinitePOVM (Fin (d+1)) O) :
    Matrix (Fin (d+1)) (Fin (d+1)) ℂ →ₗ[ℂ] (O → ℂ) where
  toFun A o := Matrix.trace (A * P.effect o)
  map_add' A B := by ext o; simp [Matrix.add_mul]
  map_smul' c A := by ext o; simp [Matrix.smul_mul]

theorem complexAnalysis_injective (P : FinitePOVM (Fin (d+1)) O)
    (hP : Identifying P) : Function.Injective (complexAnalysis P) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro A hA
  let X : HermitianSpace (d+1) := realPart (A : HSMatrix (d+1))
  let Y : HermitianSpace (d+1) := imaginaryPart (A : HSMatrix (d+1))
  have hdecomp : toMatrix X + Complex.I • toMatrix Y = A :=
    realPart_add_I_smul_imaginaryPart (A : HSMatrix (d+1))
  have hz (o : O) :
      (⟪effectVector P o, X⟫_ℝ : ℂ) +
        Complex.I * (⟪effectVector P o, Y⟫_ℝ : ℂ) = 0 := by
    rw [complex_inner_eq_trace, complex_inner_eq_trace]
    change Matrix.trace (toMatrix X * P.effect o) +
      Complex.I * Matrix.trace (toMatrix Y * P.effect o) = 0
    have hh := congrFun hA o
    change Matrix.trace (A * P.effect o) = 0 at hh
    rw [← hdecomp, Matrix.add_mul, Matrix.trace_add, Matrix.smul_mul,
      Matrix.trace_smul] at hh
    exact hh
  have hX : X = 0 := hP X (fun o => by
    have hh := congrArg Complex.re (hz o)
    simpa using hh)
  have hY : Y = 0 := hP Y (fun o => by
    have hh := congrArg Complex.im (hz o)
    simpa using hh)
  have hX' : toMatrix X = 0 := congrArg toMatrix hX
  have hY' : toMatrix Y = 0 := congrArg toMatrix hY
  simpa [hX', hY'] using hdecomp.symm

theorem identifying_card_bound (P : FinitePOVM (Fin (d+1)) O)
    (hP : Identifying P) : (d+1)^2 ≤ Fintype.card O := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (complexAnalysis_injective P hP)
  simpa [Module.finrank_matrix, Module.finrank_pi, pow_two] using h

end
end QubitOracle.AdaptiveDesign.GeneralPOVM
