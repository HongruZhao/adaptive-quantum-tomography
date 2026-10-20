import QubitOracle.AdaptiveDesign.GeneralPOVMModel
import Mathlib.Analysis.Matrix.Order
import Mathlib.Topology.Baire.Lemmas

/-! A finite family of nonzero positive effects always has a unit reference
vector with strictly positive outcome probabilities. -/
namespace QubitOracle.AdaptiveDesign.RegularReferenceVector
open Filter Topology Matrix
open scoped BigOperators ComplexOrder
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

theorem dense_nonzero_family {E F O : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [Countable O]
    (f : O → E →L[ℂ] F) (hf : ∀ o, f o ≠ 0) :
    Dense {x : E | ∀ o, f o x ≠ 0} := by
  have hproper (o : O) : (f o).ker ≠ ⊤ := by
    intro h
    apply hf o
    ext x
    have hx : x ∈ (f o).ker := by rw [h]; trivial
    exact hx
  have hd (o : O) : Dense ((f o).ker : Set E)ᶜ := by
    apply interior_eq_empty_iff_dense_compl.mp
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hproper o ((f o).ker.eq_top_of_nonempty_interior' ⟨x,hx⟩)
  have h := dense_iInter_of_isOpen (fun o => (f o).isClosed_ker.isOpen_compl) hd
  convert h using 1
  ext x
  simp

theorem exists_regular_unit {n : ℕ} {O : Type*} [Fintype O] [Nonempty O]
    (E : O → Matrix (Fin n) (Fin n) ℂ)
    (hp : ∀ o, (E o).PosSemidef) (hne : ∀ o, E o ≠ 0) :
    ∃ v : EuclideanSpace ℂ (Fin n), ‖v‖ = 1 ∧
      ∀ o, 0 < (star (WithLp.ofLp v) ⬝ᵥ (E o *ᵥ WithLp.ofLp v)).re := by
  let f := fun o => (Matrix.toEuclideanLin (E o)).toContinuousLinearMap
  have hf (o : O) : f o ≠ 0 := by
    intro h
    apply hne o
    apply Matrix.toEuclideanLin.injective
    change Matrix.toEuclideanLin (E o) = Matrix.toEuclideanLin 0
    simp only [map_zero]
    exact congrArg ContinuousLinearMap.toLinearMap h
  obtain ⟨v,hv⟩ := (dense_nonzero_family f hf).nonempty
  have hv0 : v ≠ 0 := by
    intro h
    obtain ⟨o⟩ := ‹Nonempty O›
    exact hv o (by simp [h])
  let u : EuclideanSpace ℂ (Fin n) := (‖v‖⁻¹ : ℂ) • v
  have hu : ‖u‖ = 1 := by
    simp [u,norm_smul,Complex.norm_real,norm_inv,norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
  refine ⟨u,hu,fun o => ?_⟩
  have hfu : f o u ≠ 0 := by
    dsimp only [u]
    rw [map_smul]
    exact smul_ne_zero (by exact_mod_cast inv_ne_zero (norm_ne_zero_iff.mpr hv0)) (hv o)
  have hmul : E o *ᵥ WithLp.ofLp u ≠ 0 := by
    intro h
    apply hfu
    change WithLp.toLp 2 (E o *ᵥ WithLp.ofLp u) = 0
    simp [h]
  have hpos := (hp o).dotProduct_mulVec_nonneg (WithLp.ofLp u)
  have hnz := mt ((hp o).dotProduct_mulVec_zero_iff (WithLp.ofLp u)).mp hmul
  exact lt_of_le_of_ne (Complex.nonneg_iff.mp hpos).1 (by
    intro h
    apply hnz
    apply Complex.ext
    · exact h.symm
    · exact (Complex.nonneg_iff.mp hpos).2.symm)

end
end QubitOracle.AdaptiveDesign.RegularReferenceVector
