import QubitOracle.AdaptiveDesign.PhasePairPOVM

/-! The quantitative frame bound in Proposition 4.1, including both
labelled branches. Each effect has weight one half, so its frame
contribution has weight one quarter. Unitary transport preserves the
original coercivity constant. -/
namespace QubitOracle.AdaptiveDesign.PhasePair
open QubitOracle QubitOracle.Paper GeneralPOVM GlobalPFSICHermitian
open FiniteFrameCoercivity CoerciveLeastSquares
open scoped BigOperators InnerProductSpace
noncomputable section

variable {d : ℕ} {O : Type} [Fintype O]

theorem paired_effectVector (P : FinitePOVM (Fin (d+1)) O) (b : Bool) (o : O) :
    effectVector (paired P) (b,o) = (1/2 : ℝ) •
      conjugationIsometry (branch d b) (branch_unitary d b) (effectVector P o) := by
  apply toMatrix_injective
  rfl

/-- The constant is exactly the paper's kappa_F / 2, not merely an
unspecified positive coercivity constant. -/
theorem paired_frame_coercive (P : FinitePOVM (Fin (d+1)) O) (κ : ℝ)
    (hκ : Coercive (frameOperator (effectVector P)) κ) :
    Coercive (frameOperator (effectVector (paired P))) (κ/2) := by
  intro A
  have hb (b : Bool) := coercivity_preserved_by_isometry
    (conjugationIsometry (branch d b) (branch_unitary d b)) (effectVector P) κ hκ A
  simp only [frameOperator_quadratic] at hb ⊢
  simp only [Fintype.sum_prod_type, paired_effectVector, real_inner_smul_left]
  have hs (b : Bool) :
      (∑ o, ((1/2 : ℝ) * ⟪conjugationIsometry (branch d b)
        (branch_unitary d b) (effectVector P o), A⟫_ℝ)^2) =
      (1/4 : ℝ) * ∑ o, ⟪conjugationIsometry (branch d b)
        (branch_unitary d b) (effectVector P o), A⟫_ℝ^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro o _
    ring
  simp_rw [hs]
  rw [Fintype.sum_bool]
  linarith [hb false, hb true]

end
end QubitOracle.AdaptiveDesign.PhasePair
