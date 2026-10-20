import QubitOracle.AdaptiveDesign.GlobalPFSICBornModel
import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel
import QubitOracle.AdaptiveDesign.GlobalPFSICLibrary
import QubitOracle.AdaptiveDesign.GlobalPFSICTransport
import QubitOracle.AdaptiveDesign.P2AdaptiveTheorem
import QubitOracle.AdaptiveDesign.PVMGeometry
import QubitOracle.AdaptiveDesign.PureFiniteAtlas
import QubitOracle.AdaptiveDesign.PureMatrixController
import QubitOracle.AdaptiveDesign.QuantumFidelityBridges
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.OneQubitBlochPhysicalState
import QubitOracle.Paper.OneQubitDensityMatrixBlochRepresentation
import QubitOracle.Paper.QuantumDistances
import QubitOracle.Paper.QubitFoundations
/-! The concrete parameter types describe the physical models in the
paper: the closed Bloch ball, and all Hermitian trace-one projectors. -/
namespace QubitOracle.AdaptiveDesign.PhysicalModelCharacterization
open QubitOracle QubitOracle.Paper GlobalPFSIC GlobalPFSICHermitian PureMatrixController P2Adaptive TangentGLS
open scoped BigOperators ComplexOrder InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

theorem qubit_positive_iff (theta : Fin 3 → ℝ) :
    (qubitDensityMatrix theta).PosSemidef ↔ blochNormSq theta ≤ 1 := by
  constructor
  · intro hp
    have hd := (Complex.nonneg_iff.mp hp.det_nonneg).1
    rw [QuantumFidelityBridges.qubit_det] at hd
    simp only [Complex.ofReal_re] at hd
    linarith
  · exact qubitDensityMatrix_posSemidef_of_blochNormSq_le_one theta

theorem physical_bloch_coordinates_in_ball (rho : FiniteDensityMatrix (Fin 2)) :
    blochNormSq (finiteDensityMatrixBlochCoordinates rho) ≤ 1 := by
  apply (qubit_positive_iff _).mp
  rw [← finiteDensityMatrix_eq_qubitDensityMatrix]
  exact rho.pos

/-- Trace one and idempotence single out a rank-one projector among
Hermitian matrices. Positivity is a consequence, not an extra premise. -/
theorem hermitian_projector_is_pure {d : ℕ} (A : HermitianSpace (d+1))
    (hi : toMatrix A*toMatrix A=toMatrix A) (ht : Matrix.trace (toMatrix A)=1) :
    ∃ h : PureVector d, A=(pureParameter d h).val := by
  classical
  let M := toMatrix A
  let hM := toMatrix_isHermitian A
  let eigenvals := hM.eigenvalues
  have hdiag := congrArg (Unitary.conjStarAlgAut ℂ _ (star hM.eigenvectorUnitary)) hi
  rw [map_mul,hM.conjStarAlgAut_star_eigenvectorUnitary] at hdiag
  have hsquare (i : Fin (d+1)) : eigenvals i^2=eigenvals i := by
    have hh := congrArg (fun B : Matrix (Fin (d+1)) (Fin (d+1)) ℂ => (B i i).re) hdiag
    simpa [Matrix.diagonal_mul_diagonal,pow_two,eigenvals] using hh
  have hbin (i : Fin (d+1)) : eigenvals i=0 ∨ eigenvals i=1 := by
    have hh : eigenvals i*(eigenvals i-1)=0 := by nlinarith [hsquare i]
    exact (mul_eq_zero.mp hh).imp_right sub_eq_zero.mp
  have hnonneg (i : Fin (d+1)) : 0 ≤ eigenvals i := by rcases hbin i with h|h <;> simp [h]
  have hsum : ∑ i, eigenvals i=1 := by
    have hh' := congrArg Complex.re hM.trace_eq_sum_eigenvalues
    rw [ht] at hh'
    simpa [eigenvals] using hh'.symm
  have hex : ∃ i, eigenvals i=1 := by
    by_contra hh
    push_neg at hh
    have hz : ∀ i, eigenvals i=0 := fun i => (hbin i).resolve_right (hh i)
    simp [hz] at hsum
  obtain ⟨i,hi1⟩ := hex
  have herase : ∑ j ∈ Finset.univ.erase i, eigenvals j=0 := by
    have hh := Finset.sum_erase_add (s := Finset.univ) (f := eigenvals) (Finset.mem_univ i)
    rw [hi1,hsum] at hh
    linarith
  have hother (j : Fin (d+1)) (hj : j ≠ i) : eigenvals j=0 := by
    have hh := Finset.single_le_sum (s := Finset.univ.erase i) (fun k _ => hnonneg k)
      (Finset.mem_erase.mpr ⟨hj,Finset.mem_univ j⟩)
    rw [herase] at hh
    exact le_antisymm hh (hnonneg j)
  have hd : Matrix.diagonal (fun j => (eigenvals j:ℂ))=projector (coordinate i) := by
    ext j k
    by_cases hj : j=i <;> by_cases hk : k=i
    · subst j; subst k; simp [projector,Matrix.vecMulVec_apply,coordinate,hi1]
    · subst j; simp [projector,Matrix.vecMulVec_apply,coordinate,Matrix.diagonal_apply,Ne.symm hk,hk]
    · subst k; simp [projector,Matrix.vecMulVec_apply,coordinate,Matrix.diagonal_apply,hj]
    · simp [projector,Matrix.vecMulVec_apply,coordinate,Matrix.diagonal_apply,hj,hk,hother j hj]
  let U : GlobalPFSICBorn.Action d := ⟨hM.eigenvectorUnitary.val,hM.eigenvectorUnitary.property⟩
  refine ⟨basisPureVector U i,?_⟩
  apply toMatrix_injective
  rw [basisPureVector_parameter,PVMGeometry.basisEffect_matrix]
  rw [hM.spectral_theorem]
  change Unitary.conjStarAlgAut ℂ _ hM.eigenvectorUnitary (Matrix.diagonal (fun j => (eigenvals j:ℂ)))=_
  rw [hd,Unitary.conjStarAlgAut_apply]
  change U.matrix*projector (coordinate i)*U.matrix.conjTranspose=projector (fun k => U.matrix k i)
  rw [← projector_mulVec]
  congr 1
  funext k
  simp [coordinate,Matrix.mulVec_single_one]

end
end QubitOracle.AdaptiveDesign.PhysicalModelCharacterization
