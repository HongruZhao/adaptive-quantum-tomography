import QubitOracle.Paper.ElementaryPVMBases
import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel

/-! Ambient identification and real spanning for the exact, nonredundant
coordinate/real-pair/imaginary-pair bases of Appendix S4.1.
No identification certificate is assumed.
-/
namespace QubitOracle.AdaptiveDesign.ElementaryPVMIdentification
open QubitOracle.Paper ProjectiveStateGeometry ElementaryReferenceAlgebra ElementaryPVMBases
open GlobalPFSIC (coordinate)
open GlobalPFSICHermitian
open scoped BigOperators ComplexOrder InnerProductSpace
noncomputable section
set_option maxHeartbeats 1500000

def basisVector {D : ℕ} (l : BasisLabel D) (k : Fin D) : Fin D → ℂ :=
  fun i => basisMatrix l i k

theorem coordinate_vector {D : ℕ} (k : Fin D) :
    basisVector (.inl ()) k = coordinate k := by
  funext i
  simp [basisVector, basisMatrix, coordinate, Matrix.one_apply, Pi.single_apply, eq_comm]

theorem pair_first {D : ℕ} (p : OrderedPair D) (b : Bool) :
    basisVector (.inr (b,p)) p.val.1 =
      balanced (coordinate p.val.1) ((if b then Complex.I else 1) • coordinate p.val.2) :=
  pairVectors_first _ _ (ne_of_lt p.property) _

theorem pair_second {D : ℕ} (p : OrderedPair D) (b : Bool) :
    basisVector (.inr (b,p)) p.val.2 =
      balanced (coordinate p.val.1) (-((if b then Complex.I else 1) • coordinate p.val.2)) :=
  pairVectors_second _ _ _

theorem trace_coordinate_outer {D : ℕ} (A : Matrix (Fin D) (Fin D) ℂ)
    (r s : Fin D) :
    Matrix.trace (A * Matrix.vecMulVec (coordinate r) (star (coordinate s))) = A s r := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply,
    coordinate, Pi.single_apply]

theorem basis_separates {D : ℕ} (A : Matrix (Fin D) (Fin D) ℂ)
    (h : ∀ l k, Matrix.trace (A * rankOneDensity (basisVector l k)) = 0) : A = 0 := by
  have hdiag (r : Fin D) : A r r = 0 := by
    have hr := h (.inl ()) r
    rw [coordinate_vector] at hr
    exact (trace_coordinate_outer A r r).symm.trans hr
  have hupper (r s : Fin D) (hrs : r < s) : A r s = 0 ∧ A s r = 0 := by
    let p : OrderedPair D := ⟨(r,s),hrs⟩
    have hR := congrArg (fun M => Matrix.trace (A * M))
      (real_pair_difference (coordinate r) (coordinate s))
    have hI := congrArg (fun M => Matrix.trace (A * M))
      (imaginary_pair_difference (coordinate r) (coordinate s))
    have hrp := h (.inr (false,p)) r
    have hrm := h (.inr (false,p)) s
    have hip := h (.inr (true,p)) r
    have him := h (.inr (true,p)) s
    rw [pair_first p false] at hrp
    rw [pair_second p false] at hrm
    rw [pair_first p true] at hip
    rw [pair_second p true] at him
    simp only [Bool.false_eq_true, ↓reduceIte, one_smul, p] at hrp hrm
    simp only [↓reduceIte, p] at hip him
    simp only [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_add, Matrix.trace_add,
      Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, trace_coordinate_outer,
      hrp, hrm] at hR
    simp only [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.trace_smul,
      smul_eq_mul, trace_coordinate_outer, hip, him, sub_self] at hI
    have he : A r s - A s r = 0 :=
      (mul_eq_zero.mp hI.symm).resolve_left Complex.I_ne_zero
    constructor
    · linear_combination (hR.symm + he) / 2
    · linear_combination (hR.symm - he) / 2
  ext r s
  change A r s = 0
  rcases lt_trichotomy r s with hrs | hrs | hrs
  · exact (hupper r s hrs).1
  · subst s; exact hdiag r
  · exact (hupper s r hrs).2

def basisEffect {D : ℕ} (o : BasisLabel D × Fin D) : HermitianSpace D :=
  ofMatrix (rankOneDensity (basisVector o.1 o.2)) (density_positive _).isHermitian

theorem effects_separate {D : ℕ} (A : HermitianSpace D)
    (h : ∀ o, ⟪basisEffect o,A⟫_ℝ = 0) : A = 0 := by
  apply toMatrix_injective
  apply basis_separates
  intro l k
  have hh := congrArg Complex.ofReal (h (l,k))
  rw [complex_inner_eq_trace] at hh
  exact hh

theorem effects_span {D : ℕ} :
    Submodule.span ℝ (Set.range (@basisEffect D)) = ⊤ := by
  rw [← Submodule.orthogonal_eq_bot_iff]
  apply (Submodule.eq_bot_iff _).mpr
  intro A hA
  apply effects_separate A
  intro o
  exact Submodule.inner_right_of_mem_orthogonal
    (Submodule.subset_span (Set.mem_range_self o)) hA

theorem every_hermitian_is_real_combination {D : ℕ} (A : HermitianSpace D) :
    ∃ c : BasisLabel D × Fin D → ℝ, ∑ o, c o • basisEffect o = A := by
  apply (Submodule.mem_span_range_iff_exists_fun ℝ).mp
  rw [effects_span]
  trivial

end
end QubitOracle.AdaptiveDesign.ElementaryPVMIdentification
