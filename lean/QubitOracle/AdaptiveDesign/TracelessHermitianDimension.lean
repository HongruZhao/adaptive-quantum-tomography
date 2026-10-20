import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel
/-! The D^2-1 exploration count follows from an actual dimension calculation,
not from a supplied basis cardinality. -/
namespace QubitOracle.AdaptiveDesign.TracelessHermitianDimension
open GlobalPFSICHermitian
open scoped BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

theorem hermitian_finrank (n : ℕ) : Module.finrank ℝ (HermitianSpace n)=n^2 := by
  let f : HSMatrix n →ₗ[ℝ] selfAdjoint (HSMatrix n) := imaginaryPart
  have h := LinearMap.finrank_range_add_finrank_ker f
  have hr : LinearMap.range f=⊤ := LinearMap.range_eq_top.mpr imaginaryPart_surjective
  have hk : LinearMap.ker f=selfAdjoint.submodule ℝ (HSMatrix n) := ker_imaginaryPart
  rw [hr,hk,finrank_top] at h
  have hd : Module.finrank ℝ (HSMatrix n)=2*n^2 := by
    change Module.finrank ℝ (Matrix (Fin n) (Fin n) ℂ)=_
    simp [Module.finrank_matrix,Complex.finrank_real_complex,pow_two]
    ring
  rw [hd] at h
  change Module.finrank ℝ (HermitianSpace n)+Module.finrank ℝ (HermitianSpace n)=2*n^2 at h
  omega

def traceMap (n : ℕ) : HermitianSpace n →ₗ[ℝ] ℝ where
  toFun A := (Matrix.trace (toMatrix A)).re
  map_add' A B := by simp [Matrix.trace_add]
  map_smul' c A := by simp [Matrix.trace_smul]

def identity (n : ℕ) : HermitianSpace n := ofMatrix 1 Matrix.isHermitian_one

@[simp] theorem trace_identity (n : ℕ) : traceMap n (identity n)=(n:ℝ) := by
  simp [traceMap,identity,Matrix.trace]

theorem trace_surjective (n : ℕ) (hn : 0<n) : Function.Surjective (traceMap n) := by
  intro r
  refine ⟨(r/(n:ℝ)) • identity n,?_⟩
  rw [map_smul,trace_identity]
  change r/(n:ℝ)*(n:ℝ)=r
  exact div_mul_cancel₀ _ (by exact_mod_cast hn.ne')

def traceless (n : ℕ) : Submodule ℝ (HermitianSpace n) := (traceMap n).ker

theorem traceless_finrank (n : ℕ) (hn : 0<n) :
    Module.finrank ℝ (traceless n)=n^2-1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (traceMap n)
  rw [LinearMap.range_eq_top.mpr (trace_surjective n hn),finrank_top,
    Module.finrank_self,hermitian_finrank] at h
  change 1+Module.finrank ℝ (traceless n)=n^2 at h
  omega

def tracelessBasis (n : ℕ) (hn : 0<n) : Module.Basis (Fin (n^2-1)) ℝ (traceless n) :=
  (Module.finBasis ℝ (traceless n)).reindex (finCongr (traceless_finrank n hn))

end
end QubitOracle.AdaptiveDesign.TracelessHermitianDimension
