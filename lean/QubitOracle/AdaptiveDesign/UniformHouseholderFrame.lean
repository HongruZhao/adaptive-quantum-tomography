-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMGeneralGeometry

/-! The explicit real Householder exploitation matrix mentioned in the
paper. It is the same exact completion used by the controller, evaluated
at the known uniform real unit vector. -/
namespace QubitOracle.AdaptiveDesign.UniformHouseholderFrame
open QubitOracle QubitOracle.Paper
open scoped BigOperators ComplexOrder
noncomputable section
set_option maxHeartbeats 1000000

def amplitude (d : ℕ) : ℝ := 1 / Real.sqrt (d+1:ℝ)
def uniformVector (d : ℕ) : Fin (d+1) → ℂ := fun _ => (amplitude d : ℂ)

theorem amplitude_pos (d : ℕ) : 0 < amplitude d := by unfold amplitude; positivity

theorem uniformVector_normalized (d : ℕ) :
    ∑ i, Complex.normSq (uniformVector d i) = 1 := by
  simp only [uniformVector, Complex.normSq_ofReal, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have he : (d+1:ℝ)*(amplitude d)^2 = 1 := by
    unfold amplitude
    rw [div_pow, Real.sq_sqrt (by positivity)]
    field_simp
  simpa only [Nat.cast_add, Nat.cast_one, pow_two] using he

theorem uniform_phase (d : ℕ) : ExactHouseholder.phase (uniformVector d 0) = 1 := by
  have ha := amplitude_pos d
  simp [ExactHouseholder.phase, uniformVector, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ha, ha.ne']

theorem matrix_im_zero (d : ℕ) (i j : Fin (d+1)) :
    (ExactHouseholder.matrix (uniformVector d) i j).im = 0 := by
  classical
  have hphase : ExactHouseholder.phase (amplitude d : ℂ) = 1 := uniform_phase d
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
    simp [ExactHouseholder.matrix, uniform_phase, ExactHouseholder.lineProjector,
      ExactHouseholder.vector, uniformVector, GlobalPFSIC.projector_apply,
      GlobalPFSIC.coordinate, Matrix.smul_apply, Matrix.one_apply, Pi.single_apply,
      Complex.mul_im, Complex.mul_re, hphase, hi, hj, apply_ite]

def matrix (d : ℕ) : Matrix (Fin (d+1)) (Fin (d+1)) ℝ :=
  fun i j => (ExactHouseholder.matrix (uniformVector d) i j).re

theorem matrix_orthogonal (d : ℕ) : matrix d ∈ Matrix.orthogonalGroup (Fin (d+1)) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i j
  have hh := congrArg (fun A : Matrix (Fin (d+1)) (Fin (d+1)) ℂ => (A i j).re)
    (Matrix.mem_unitaryGroup_iff.mp
      (ExactHouseholder.matrix_unitary (uniformVector d) (uniformVector_normalized d)))
  simpa [matrix, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
    Complex.mul_re, matrix_im_zero, Matrix.one_apply, apply_ite] using hh

theorem matrix_uniformFirstRow (d : ℕ) (k : Fin (d+1)) :
    matrix d 0 k = 1 / Real.sqrt (d+1:ℝ) := by
  have hs : (ExactHouseholder.matrix (uniformVector d)).conjTranspose =
      ExactHouseholder.matrix (uniformVector d) := by
    simp [ExactHouseholder.matrix, uniform_phase, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_add, ExactHouseholder.lineProjector_selfadjoint]
  have he := congrArg (fun A : Matrix (Fin (d+1)) (Fin (d+1)) ℂ => (A 0 k).re) hs
  have hc := congrFun (ExactHouseholder.matrix_firstColumn (uniformVector d)) k
  change (ExactHouseholder.matrix (uniformVector d) 0 k).re = _
  rw [← he]
  simpa [Matrix.conjTranspose_apply, hc, uniformVector, amplitude]

def frame (d : ℕ) : OracleFrame d :=
  ⟨matrix d, matrix_orthogonal d, matrix_uniformFirstRow d⟩

/-- Instantiates the general PVM procedure with the explicit matrix,
without changing any exploration basis or identification assumption. -/
def withHouseholder {d : ℕ} (L : PVMGeneralGeometry.ExplorationLibrary d) :
    PVMGeneralGeometry.ExplorationLibrary d :=
  PVMGeneralGeometry.withExploitationFrame L (frame d)

@[simp] theorem withHouseholder_frame {d : ℕ} (L : PVMGeneralGeometry.ExplorationLibrary d) :
    (withHouseholder L).exploitationFrame = frame d := rfl

end
end QubitOracle.AdaptiveDesign.UniformHouseholderFrame

-/
