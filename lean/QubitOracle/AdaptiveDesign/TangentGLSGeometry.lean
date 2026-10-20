import QubitOracle.AdaptiveDesign.TangentGLSAlgebra
import QubitOracle.AdaptiveDesign.PureHermitianController

/-!
# The update h -> h + Delta h -> normalization

The tangent condition is the intrinsic matrix identity `P D + D P = D`.
The normalizing denominator is proved nonzero for every tangent correction.
No coordinate chart, true state, or chosen complement enters these definitions.
-/

namespace QubitOracle.AdaptiveDesign.TangentGLS

open QubitOracle.Paper GlobalPFSICHermitian PureMatrixController
open scoped BigOperators ComplexOrder InnerProductSpace
noncomputable section

def pureVector {d : ℕ} (h : PureVector d) : EuclideanSpace ℂ (Fin (d+1)) :=
  WithLp.toLp 2 h.val

theorem pureVector_norm {d : ℕ} (h : PureVector d) : ‖pureVector h‖ = 1 := by
  have hs : ‖pureVector h‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ i, ‖h.val i‖ ^ 2) = 1
    simp only [Complex.sq_norm]
    exact h.property
  nlinarith [norm_nonneg (pureVector h)]

def tangentCondition {d : ℕ} (h : PureVector d) :
    HermitianSpace (d+1) →ₗ[ℝ] Matrix (Fin (d+1)) (Fin (d+1)) ℂ where
  toFun A := rankOneDensity h.val * toMatrix A +
    toMatrix A * rankOneDensity h.val - toMatrix A
  map_add' A B := by
    simp only [toMatrix_add, Matrix.mul_add, Matrix.add_mul]
    abel
  map_smul' c A := by
    simp [toMatrix_smul, Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_sub]

def tangentSpace {d : ℕ} (h : PureVector d) : Submodule ℝ (HermitianSpace (d+1)) :=
  (tangentCondition h).ker

theorem tangentSpace_mem {d : ℕ} (h : PureVector d) (A : HermitianSpace (d+1)) :
    A ∈ tangentSpace h ↔ rankOneDensity h.val * toMatrix A +
      toMatrix A * rankOneDensity h.val = toMatrix A := by
  simp only [tangentSpace, LinearMap.mem_ker, tangentCondition,
    LinearMap.coe_mk, AddHom.coe_mk, sub_eq_zero]

theorem pureProjector_idempotent {d : ℕ} (h : PureVector d) :
    rankOneDensity h.val * rankOneDensity h.val = rankOneDensity h.val := by
  change GlobalPFSIC.projector h.val * GlobalPFSIC.projector h.val = _
  have hh : ∑ i, Complex.normSq (h.val i) = 1 := h.property
  rw [ExactHouseholder.projector_square, hh]
  simp only [Complex.ofReal_one, one_smul]
  rfl

theorem tangent_sandwich_zero {d : ℕ} (h : PureVector d) (A : tangentSpace h) :
    rankOneDensity h.val * toMatrix A.val * rankOneDensity h.val = 0 := by
  let P := rankOneDensity h.val
  let D := toMatrix A.val
  have hP : P * P = P := pureProjector_idempotent h
  have hA : P * D + D * P = D := (tangentSpace_mem h A.val).mp A.property
  have hx : P * D * P + P * D * P = P * D * P := by
    calc
      _ = P * (P * D + D * P) * P := by
        simp only [Matrix.mul_add, Matrix.add_mul]
        simp only [Matrix.mul_assoc, ← Matrix.mul_assoc P P, hP]
      _ = _ := by rw [hA]
  have hz : P * D * P = 0 := by
    have hcancel : P * D * P + P * D * P = P * D * P + 0 := by simpa using hx
    exact add_left_cancel hcancel
  exact hz

def tangentVector {d : ℕ} (h : PureVector d) (A : tangentSpace h) :
    EuclideanSpace ℂ (Fin (d+1)) := WithLp.toLp 2 ((toMatrix A.val).mulVec h.val)

theorem tangentVector_orthogonal {d : ℕ} (h : PureVector d) (A : tangentSpace h) :
    ⟪pureVector h, tangentVector h A⟫_ℂ = 0 := by
  have htrace : Matrix.trace (toMatrix A.val * rankOneDensity h.val) = 0 := by
    have hs := congrArg Matrix.trace (tangent_sandwich_zero h A)
    rw [Matrix.trace_mul_cycle, pureProjector_idempotent h] at hs
    rw [Matrix.trace_mul_comm] at hs
    simpa only [Matrix.trace_zero] using hs
  have hq : GlobalPFSIC.quadratic (toMatrix A.val) h.val = 0 := by
    rw [← trace_mul_projector]
    exact htrace
  change (∑ i, (toMatrix A.val).mulVec h.val i * star (h.val i)) = 0
  simpa only [Matrix.mulVec, dotProduct, GlobalPFSIC.quadratic,
    Finset.sum_mul, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] using hq

def unnormalizedVector {d : ℕ} (h : PureVector d) (A : tangentSpace h) :
    EuclideanSpace ℂ (Fin (d+1)) := pureVector h + tangentVector h A

theorem unnormalizedVector_norm_sq {d : ℕ} (h : PureVector d) (A : tangentSpace h) :
    ‖unnormalizedVector h A‖ ^ 2 = 1 + ‖tangentVector h A‖ ^ 2 := by
  simpa only [unnormalizedVector, pow_two, pureVector_norm, one_mul] using
    (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ (tangentVector_orthogonal h A))

theorem unnormalizedVector_norm_pos {d : ℕ} (h : PureVector d) (A : tangentSpace h) :
    0 < ‖unnormalizedVector h A‖ := by
  have hs := unnormalizedVector_norm_sq h A
  nlinarith [norm_nonneg (unnormalizedVector h A), sq_nonneg ‖tangentVector h A‖]

def updatedVector {d : ℕ} (h : PureVector d) (A : tangentSpace h) :
    EuclideanSpace ℂ (Fin (d+1)) :=
  (‖unnormalizedVector h A‖⁻¹ : ℝ) • unnormalizedVector h A

theorem updatedVector_norm {d : ℕ} (h : PureVector d) (A : tangentSpace h) :
    ‖updatedVector h A‖ = 1 := by
  rw [updatedVector, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact inv_mul_cancel₀ (unnormalizedVector_norm_pos h A).ne'

def updatedPureVector {d : ℕ} (h : PureVector d) (A : tangentSpace h) : PureVector d :=
  ⟨(updatedVector h A).ofLp, by
    change (∑ i, Complex.normSq ((updatedVector h A).ofLp i)) = 1
    have hs := congrArg (fun x : ℝ => x ^ 2) (updatedVector_norm h A)
    rw [EuclideanSpace.norm_sq_eq] at hs
    simpa only [Complex.sq_norm, one_pow] using hs⟩

def updatedState {d : ℕ} (h : PureVector d) (A : tangentSpace h) :
    Matrix (Fin (d+1)) (Fin (d+1)) ℂ := rankOneDensity (updatedPureVector h A).val

theorem updatedState_physical {d : ℕ} (h : PureVector d) (A : tangentSpace h) :
    (updatedState h A).PosSemidef ∧ Matrix.trace (updatedState h A) = 1 ∧
      updatedState h A * updatedState h A = updatedState h A :=
  ⟨GlobalPFSIC.projector_posSemidef _,
    rankOneDensity_trace_eq_one _ (updatedPureVector h A).property,
    pureProjector_idempotent (updatedPureVector h A)⟩

end
end QubitOracle.AdaptiveDesign.TangentGLS
