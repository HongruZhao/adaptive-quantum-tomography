import QubitOracle.AdaptiveDesign.RegularReferenceVector
import QubitOracle.AdaptiveDesign.PureMatrixController

/-! Every finite nonzero positive effect family can be oriented to be
regular at e_0. No random unitary or simultaneous diagonalization is assumed. -/
namespace QubitOracle.AdaptiveDesign.RegularReferenceVector
open QubitOracle QubitOracle.Paper PureMatrixController
open scoped BigOperators ComplexOrder
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

theorem exists_regular_rotation {d : ℕ} {O : Type} [Fintype O] [Nonempty O]
    (E : O → Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hp : ∀ y, (E y).PosSemidef) (hne : ∀ y, E y ≠ 0) :
    ∃ U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ,
      U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ ∧
      ∀ y, 0 < ((U.conjTranspose*E y*U) 0 0).re := by
  obtain ⟨v,hv,hpos⟩ := exists_regular_unit E hp hne
  have hnorm : pureStateNormSq v.ofLp=1 := by
    have hh := congrArg (fun x : ℝ => x^2) hv
    rw [EuclideanSpace.norm_sq_eq] at hh
    simpa [pureStateNormSq,Complex.sq_norm] using hh
  let h : PureVector d := ⟨v.ofLp,hnorm⟩
  obtain ⟨U,hU,hcol⟩ := exists_unitary_firstColumn h
  refine ⟨U,hU,fun y => ?_⟩
  have he : (U.conjTranspose*E y*U) 0 0=star v.ofLp ⬝ᵥ (E y).mulVec v.ofLp := by
    have hc (i : Fin (d+1)) : U i 0=v.ofLp i := congrFun hcol i
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,star,
      Matrix.mulVec,dotProduct,hc,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  exact hpos y

end
end QubitOracle.AdaptiveDesign.RegularReferenceVector
