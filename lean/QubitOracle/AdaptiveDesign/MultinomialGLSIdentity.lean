import Mathlib
/-! The multinomial covariance identity used by tangent GLS. A zero sum
of probability derivatives removes the multinomial rank-one term. -/
namespace QubitOracle.AdaptiveDesign.MultinomialGLSIdentity
open Matrix
open scoped BigOperators
noncomputable section
variable {Y I : Type*} [Fintype Y] [Fintype I] [DecidableEq Y] [DecidableEq I]

theorem covariance_identity (q : Y → ℝ) (hq : ∀ y, q y ≠ 0)
    (G : Matrix Y I ℝ) (hG : ∀ i, ∑ y, G y i = 0) :
    G.transpose * diagonal (fun y => (q y)⁻¹) *
        (diagonal q - vecMulVec q q) * diagonal (fun y => (q y)⁻¹) * G =
      G.transpose * diagonal (fun y => (q y)⁻¹) * G := by
  let D := diagonal (fun y => (q y)⁻¹)
  have hD : D*diagonal q=1 := by
    ext i j
    by_cases hij : i=j
    · subst j; simp [D,Matrix.diagonal_apply,hq,Matrix.one_apply]
    · simp [D,Matrix.diagonal_apply,hij,Matrix.one_apply]
  have hDq : D *ᵥ q = fun _ => 1 := by
    ext y
    simp [D,Matrix.mulVec_diagonal,hq]
  have hG1 : G.transpose *ᵥ (fun _ => 1) = 0 := by
    ext i
    simp [Matrix.mulVec,dotProduct,hG]
  have hcross : (G.transpose*D)*vecMulVec q q=0 := by
    rw [Matrix.mul_vecMulVec,← Matrix.mulVec_mulVec,hDq,hG1]
    simp
  change G.transpose*D*(diagonal q-vecMulVec q q)*D*G = G.transpose*D*G
  rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.sub_mul,hcross,Matrix.zero_mul,Matrix.zero_mul,sub_zero,
    Matrix.mul_assoc G.transpose D (diagonal q),hD,Matrix.mul_one]

end
end QubitOracle.AdaptiveDesign.MultinomialGLSIdentity
