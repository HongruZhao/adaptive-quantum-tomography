import QubitOracle.AdaptiveDesign.CoerciveLeastSquares
import QubitOracle.AdaptiveDesign.FiniteFrameCoercivity
import QubitOracle.AdaptiveDesign.GlobalPFSIC
import QubitOracle.AdaptiveDesign.GlobalPFSICIdentification
import QubitOracle.AdaptiveDesign.GlobalPFSICLibrary
/-! # Real Hilbert space of Hermitian matrices for the physical PFSIC model -/
namespace QubitOracle.AdaptiveDesign.GlobalPFSICHermitian

open scoped BigOperators InnerProductSpace ComplexOrder
noncomputable section

/-- A separate type prevents the Frobenius norm from changing matrix instances
used elsewhere in the project. -/
def HSMatrix (n : Nat) := Matrix (Fin n) (Fin n) ℂ

instance (n : Nat) : Ring (HSMatrix n) := inferInstanceAs (Ring (Matrix (Fin n) (Fin n) ℂ))
instance (n : Nat) : Algebra ℂ (HSMatrix n) :=
  inferInstanceAs (Algebra ℂ (Matrix (Fin n) (Fin n) ℂ))
instance (n : Nat) : StarRing (HSMatrix n) :=
  inferInstanceAs (StarRing (Matrix (Fin n) (Fin n) ℂ))
instance (n : Nat) : StarModule ℂ (HSMatrix n) :=
  inferInstanceAs (StarModule ℂ (Matrix (Fin n) (Fin n) ℂ))
instance (n : Nat) : NormedAddCommGroup (HSMatrix n) :=
  Matrix.toMatrixNormedAddCommGroup (1 : Matrix (Fin n) (Fin n) ℂ) Matrix.PosDef.one
instance (n : Nat) : InnerProductSpace ℂ (HSMatrix n) :=
  Matrix.toMatrixInnerProductSpace (1 : Matrix (Fin n) (Fin n) ℂ) Matrix.PosSemidef.one
instance (n : Nat) : InnerProductSpace ℝ (HSMatrix n) :=
  InnerProductSpace.complexToReal
instance (n : Nat) : StarModule ℝ (HSMatrix n) :=
  inferInstanceAs (StarModule ℝ (Matrix (Fin n) (Fin n) ℂ))
instance (n : Nat) : FiniteDimensional ℝ (HSMatrix n) :=
  inferInstanceAs (FiniteDimensional ℝ (Matrix (Fin n) (Fin n) ℂ))

/-- The physical real vector space; trace-one and positivity are properties
of a state, rather than restrictions on a linear regression parameter space. -/
def HermitianSpace (n : Nat) := ↥(selfAdjoint.submodule ℝ (HSMatrix n))

instance (n : Nat) : NormedAddCommGroup (HermitianSpace n) :=
  Submodule.normedAddCommGroup (selfAdjoint.submodule ℝ (HSMatrix n))
instance (n : Nat) : InnerProductSpace ℝ (HermitianSpace n) :=
  Submodule.innerProductSpace (selfAdjoint.submodule ℝ (HSMatrix n))

/-- The ordinary complex matrix underlying a real Hermitian vector. -/
def toMatrix {n : Nat} (A : HermitianSpace n) : Matrix (Fin n) (Fin n) ℂ := A.1

theorem toMatrix_isHermitian {n : Nat} (A : HermitianSpace n) : (toMatrix A).IsHermitian := by
  exact A.2

/-- Embed a matrix with its proved Hermitian property. -/
def ofMatrix {n : Nat} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    HermitianSpace n := ⟨A, hA⟩

@[simp] theorem toMatrix_ofMatrix {n : Nat} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) : toMatrix (ofMatrix A hA) = A := rfl

@[simp] theorem toMatrix_add {n : Nat} (A B : HermitianSpace n) :
    toMatrix (A+B) = toMatrix A + toMatrix B := rfl
@[simp] theorem toMatrix_smul {n : Nat} (c : ℝ) (A : HermitianSpace n) :
    toMatrix (c • A) = c • toMatrix A := rfl

theorem inner_eq_trace {n : Nat} (A B : HermitianSpace n) :
    ⟪A, B⟫_ℝ = (Matrix.trace (toMatrix B * toMatrix A)).re := by
  change (Matrix.trace (toMatrix B * 1 * (toMatrix A).conjTranspose)).re = _
  rw [Matrix.mul_one, (toMatrix_isHermitian A).eq]

/-- Linear conversion to ordinary matrix coordinates. -/
def toMatrixLinear (n : Nat) : HermitianSpace n →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := toMatrix
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem toMatrix_injective {n : Nat} : Function.Injective (@toMatrix n) := by
  intro A B h
  exact Subtype.ext h

instance (n : Nat) : FiniteDimensional ℝ (HermitianSpace n) :=
  FiniteDimensional.of_injective (toMatrixLinear n) toMatrix_injective

theorem toMatrix_continuous (n : Nat) : Continuous (@toMatrix n) :=
  (toMatrixLinear n).continuous_of_finiteDimensional

theorem complex_inner_eq_trace {n : Nat} (A B : HermitianSpace n) :
    (⟪A, B⟫_ℝ : ℂ) = Matrix.trace (toMatrix B * toMatrix A) := by
  rw [inner_eq_trace]
  apply Complex.conj_eq_iff_re.mp
  change star (Matrix.trace (toMatrix B * toMatrix A)) = _
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
    (toMatrix_isHermitian A).eq, (toMatrix_isHermitian B).eq, Matrix.trace_mul_comm]

open GlobalPFSIC in
theorem trace_mul_projector {n : Nat} (A : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin n → ℂ) : Matrix.trace (A * projector v) = quadratic A v := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, projector_apply, quadratic]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- Reference POVM effects as vectors in the real Hermitian parameter space. -/
def effectVector {d : Nat} (hd : 0 < d) (o : GlobalPFSIC.Outcome d) : HermitianSpace (d+1) :=
  ofMatrix (GlobalPFSIC.effect o) (GlobalPFSIC.effect_posSemidef hd o).isHermitian

@[simp] theorem toMatrix_effectVector {d : Nat} (hd : 0 < d) (o : GlobalPFSIC.Outcome d) :
    toMatrix (effectVector hd o) = GlobalPFSIC.effect o := rfl

/-- The real Hilbert inner product is the physical Born linear functional. -/
theorem effectVector_inner_complex {d : Nat} (hd : 0 < d)
    (o : GlobalPFSIC.Outcome d) (A : HermitianSpace (d+1)) :
    (⟪effectVector hd o, A⟫_ℝ : ℂ) =
      (GlobalPFSIC.effectWeight d : ℂ) *
        GlobalPFSIC.quadratic (toMatrix A) (GlobalPFSIC.measurementVector o) := by
  rw [complex_inner_eq_trace, toMatrix_effectVector, GlobalPFSIC.effect,
    Matrix.mul_smul, Matrix.trace_smul, trace_mul_projector]
  rfl

/-- The actual finite POVM separates the real Hermitian coordinates. -/
theorem effectVector_separates {d : Nat} (hd : 0 < d)
    (A : HermitianSpace (d+1))
    (hA : ∀ o, ⟪effectVector hd o, A⟫_ℝ = 0) : A = 0 := by
  apply toMatrix_injective
  change toMatrix A = 0
  apply (GlobalPFSIC.quadratic_measurementVector_eq_zero_iff hd (toMatrix A)).mp
  intro o
  have h := effectVector_inner_complex hd o A
  rw [hA o, Complex.ofReal_zero] at h
  have hc : (GlobalPFSIC.effectWeight d : ℂ) ≠ 0 := by
    exact_mod_cast (GlobalPFSIC.effectWeight_pos d hd).ne'
  exact (mul_eq_zero.mp h.symm).resolve_left hc

/-- The required positive regression-frame constant is a proved consequence
of the explicit physical effect construction. -/
theorem referenceFrame_coercive {d : Nat} (hd : 0 < d) :
    ∃ κ : ℝ, 0 < κ ∧ CoerciveLeastSquares.Coercive
      (FiniteFrameCoercivity.frameOperator (effectVector hd)) κ :=
  FiniteFrameCoercivity.exists_positive_coercivity_of_separating
    (effectVector hd) (effectVector_separates hd)

/-- Matrix conjugation acts linearly on the real Hermitian parameter space. -/
def conjugationLinear {n : Nat} (U : Matrix (Fin n) (Fin n) ℂ) :
    HermitianSpace n →ₗ[ℝ] HermitianSpace n where
  toFun A := ofMatrix (U * toMatrix A * U.conjTranspose) (by
    change (U * toMatrix A * U.conjTranspose).conjTranspose = _
    simp [Matrix.conjTranspose_mul, (toMatrix_isHermitian A).eq, Matrix.mul_assoc])
  map_add' A B := by
    apply toMatrix_injective
    change U * (toMatrix A + toMatrix B) * U.conjTranspose =
      U * toMatrix A * U.conjTranspose + U * toMatrix B * U.conjTranspose
    simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c A := by
    apply toMatrix_injective
    change U * (c • toMatrix A) * U.conjTranspose = c • (U * toMatrix A * U.conjTranspose)
    simp [Matrix.mul_smul, Matrix.smul_mul]

@[simp] theorem toMatrix_conjugationLinear {n : Nat}
    (U : Matrix (Fin n) (Fin n) ℂ) (A : HermitianSpace n) :
    toMatrix (conjugationLinear U A) = U * toMatrix A * U.conjTranspose := rfl

private theorem unitary_trace_conjugation {n : Nat}
    (U A : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Matrix.trace (U * A * U.conjTranspose) = Matrix.trace A := by
  have hu : U.conjTranspose * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hu, Matrix.one_mul]

theorem conjugationLinear_inner {n : Nat}
    (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (A B : HermitianSpace n) :
    ⟪conjugationLinear U A, conjugationLinear U B⟫_ℝ = ⟪A, B⟫_ℝ := by
  rw [inner_eq_trace, inner_eq_trace, toMatrix_conjugationLinear, toMatrix_conjugationLinear]
  have hu : U.conjTranspose * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have heq : (U * toMatrix B * U.conjTranspose) * (U * toMatrix A * U.conjTranspose) =
      U * (toMatrix B * toMatrix A) * U.conjTranspose := by
    calc
      _ = U * toMatrix B * (U.conjTranspose * U) * toMatrix A * U.conjTranspose := by
        noncomm_ring
      _ = _ := by rw [hu]; simp [Matrix.mul_assoc]
  rw [heq, unitary_trace_conjugation U _ hU]

/-- Physical unitary conjugation as a real linear isometry equivalence. -/
def conjugationIsometry {n : Nat} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    HermitianSpace n ≃ₗᵢ[ℝ] HermitianSpace n where
  toLinearEquiv :=
    { conjugationLinear U with
      invFun := conjugationLinear U.conjTranspose
      left_inv := by
        intro A
        apply toMatrix_injective
        change U.conjTranspose * (U * toMatrix A * U.conjTranspose) * U.conjTranspose.conjTranspose = toMatrix A
        rw [Matrix.conjTranspose_conjTranspose]
        have hu : U.conjTranspose * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
        calc
          _ = (U.conjTranspose * U) * toMatrix A * (U.conjTranspose * U) := by noncomm_ring
          _ = _ := by simp [hu]
      right_inv := by
        intro A
        apply toMatrix_injective
        change U * (U.conjTranspose * toMatrix A * U.conjTranspose.conjTranspose) * U.conjTranspose = toMatrix A
        rw [Matrix.conjTranspose_conjTranspose]
        have hu : U * U.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.mp hU
        calc
          _ = (U * U.conjTranspose) * toMatrix A * (U * U.conjTranspose) := by noncomm_ring
          _ = _ := by simp [hu] }
  norm_map' := (LinearMap.norm_map_iff_inner_map_map (conjugationLinear U)).2
    (conjugationLinear_inner U hU)

@[simp] theorem toMatrix_conjugationIsometry {n : Nat}
    (U : Matrix (Fin n) (Fin n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (A : HermitianSpace n) :
    toMatrix (conjugationIsometry U hU A) = U * toMatrix A * U.conjTranspose := rfl

/-- The transported physical effects have one common positive frame constant
for every dimension and every adaptively selected unitary. -/
theorem transportedFrame_uniform_coercivity {d : Nat} (hd : 0 < d) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
      (hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ),
      CoerciveLeastSquares.Coercive (FiniteFrameCoercivity.frameOperator
        (fun o => conjugationIsometry U hU (effectVector hd o))) κ := by
  obtain ⟨κ, hκ, hframe⟩ := referenceFrame_coercive hd
  exact ⟨κ, hκ, fun U hU => FiniteFrameCoercivity.coercivity_preserved_by_isometry
    (conjugationIsometry U hU) (effectVector hd) κ hframe⟩

end
end QubitOracle.AdaptiveDesign.GlobalPFSICHermitian
