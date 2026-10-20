import QubitOracle.Paper.InformationDefinitions
import QubitOracle.AdaptiveDesign.InformationCoordinateInvariance

/-! Smoothness, coordinate contractions, and persistence of singularity.
These supply prose assertions in Section 2.4, separately from the
matrix inverse/trace formulas already in InformationCoordinateInvariance.
-/
namespace QubitOracle.Paper.InformationSmoothness
open scoped BigOperators InnerProductSpace
noncomputable section

theorem fisher_smooth_at {E O : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fintype O] (effects : O → E) (A B P : E)
    (hp : ∀ y, 0 < ⟪effects y, P⟫_ℝ) :
    ContDiffAt ℝ ⊤ (fun Q => ∑ y,
      (⟪effects y, A⟫_ℝ * ⟪effects y, B⟫_ℝ) / ⟪effects y, Q⟫_ℝ) P := by
  apply ContDiffAt.sum
  intro y _
  exact contDiffAt_const.div ((innerSL ℝ (effects y)).contDiff.contDiffAt) (ne_of_gt (hp y))

theorem bilinear_coordinate_contraction {E I : Type*} [AddCommGroup E] [Module ℝ E]
    [Fintype I] (B : LinearMap.BilinForm ℝ E) (v : I → E) (u w : I → ℝ) :
    B (∑ j, u j • v j) (∑ k, w k • v k) =
      u ⬝ᵥ ((LinearMap.BilinForm.toMatrixAux v B).mulVec w) := by
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, Matrix.mulVec, dotProduct, LinearMap.BilinForm.toMatrixAux_apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem singularity_coordinate_invariant {I : Type*} [Fintype I] [DecidableEq I]
    (M J : Matrix I I ℝ) (hJ : J.det ≠ 0) :
    (J.transpose * M * J).det = 0 ↔ M.det = 0 := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  simp [mul_eq_zero, hJ]

end
end QubitOracle.Paper.InformationSmoothness
