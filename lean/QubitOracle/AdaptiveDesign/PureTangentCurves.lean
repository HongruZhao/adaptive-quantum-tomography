import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel
import QubitOracle.AdaptiveDesign.PureMatrixController
import QubitOracle.AdaptiveDesign.TangentGLSGeometry
import QubitOracle.AdaptiveDesign.TangentGLSRetraction
import QubitOracle.Paper.PureStateFoundations
/-! Every intrinsic tangent matrix is the derivative of an actual smooth
curve of rank-one, trace-one projectors. This proves the prose assertion
used to relate directional and coordinate SLDs in Section 2.4.
-/
namespace QubitOracle.AdaptiveDesign.PureTangentCurves
open QubitOracle QubitOracle.Paper TangentGLS GlobalPFSICHermitian PureMatrixController
open scoped BigOperators ComplexOrder InnerProductSpace Matrix.Norms.Elementwise
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

def curve {d : ℕ} (h : PureVector d) (A : tangentSpace h) (s : ℝ) :
    Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  (1+s^2*‖tangentVector h A‖^2)⁻¹ •
    (rankOneDensity h.val + s • toMatrix A.val +
      s^2 • (toMatrix A.val * rankOneDensity h.val * toMatrix A.val))

theorem tangentVector_real_smul {d : ℕ} (h : PureVector d) (A : tangentSpace h) (s : ℝ) :
    tangentVector h (s • A) = s • tangentVector h A := by
  ext i
  change ((s • toMatrix A.val).mulVec h.val) i = s • ((toMatrix A.val).mulVec h.val) i
  simp only [Matrix.smul_mulVec, Pi.smul_apply]

theorem curve_is_update {d : ℕ} (h : PureVector d) (A : tangentSpace h) (s : ℝ) :
    curve h A s = updatedState h (s • A) := by
  rw [updatedState_matrix_formula, tangentVector_real_smul, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  change curve h A s = (1+s^2*‖tangentVector h A‖^2)⁻¹ •
    (rankOneDensity h.val+s • toMatrix A.val+
      (s • toMatrix A.val)*rankOneDensity h.val*(s • toMatrix A.val))
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [curve, pow_two]

theorem curve_zero {d : ℕ} (h : PureVector d) (A : tangentSpace h) :
    curve h A 0 = rankOneDensity h.val := by simp [curve]

theorem curve_physical {d : ℕ} (h : PureVector d) (A : tangentSpace h) (s : ℝ) :
    (curve h A s).IsHermitian ∧ curve h A s * curve h A s = curve h A s ∧
      Matrix.trace (curve h A s) = 1 := by
  rw [curve_is_update]
  exact ⟨(updatedState_physical h (s • A)).1.isHermitian,
    (updatedState_physical h (s • A)).2.2,(updatedState_physical h (s • A)).2.1⟩

theorem curve_smooth {d : ℕ} (h : PureVector d) (A : tangentSpace h) :
    ContDiff ℝ ⊤ (curve h A) := by
  unfold curve
  have hd : ContDiff ℝ ⊤ (fun s : ℝ => 1+s^2*‖tangentVector h A‖^2) := by fun_prop
  have hi := hd.inv (fun s => ne_of_gt (by positivity : 0 < 1+s^2*‖tangentVector h A‖^2))
  have hn : ContDiff ℝ ⊤ (fun s : ℝ => rankOneDensity h.val + s • toMatrix A.val +
      s^2 • (toMatrix A.val * rankOneDensity h.val * toMatrix A.val)) := by fun_prop
  simpa only [Pi.smul_apply, Pi.inv_apply] using! hi.smul hn

theorem curve_hasDerivAt_zero {d : ℕ} (h : PureVector d) (A : tangentSpace h) :
    HasDerivAt (curve h A) (toMatrix A.val) 0 := by
  have hs : HasDerivAt (fun s : ℝ => s^2) 0 0 := by
    simpa using hasDerivAt_pow 2 (0:ℝ)
  have hd : HasDerivAt (fun s : ℝ => (1+s^2*‖tangentVector h A‖^2)⁻¹) 0 0 := by
    simpa using! ((hasDerivAt_const 0 (1:ℝ)).add (hs.mul_const (‖tangentVector h A‖^2))).inv (by simp)
  have hn : HasDerivAt (fun s : ℝ => rankOneDensity h.val+s • toMatrix A.val+
      s^2 • (toMatrix A.val*rankOneDensity h.val*toMatrix A.val)) (toMatrix A.val) 0 := by
    simpa using! ((hasDerivAt_const 0 (rankOneDensity h.val)).add
      ((hasDerivAt_id (0:ℝ)).smul_const (toMatrix A.val))).add
      (hs.smul_const (toMatrix A.val*rankOneDensity h.val*toMatrix A.val))
  simpa only [curve, zero_pow (by decide : 2 ≠ 0), zero_mul, add_zero, inv_one,
    zero_smul, one_smul, zero_add] using! hd.smul hn

theorem every_tangent_is_smooth_curve_derivative {d : ℕ} (h : PureVector d) (A : tangentSpace h) :
    ∃ γ : ℝ → Matrix (Fin (d+1)) (Fin (d+1)) ℂ,
      ContDiff ℝ ⊤ γ ∧ γ 0 = rankOneDensity h.val ∧
      (∀ s, (γ s).IsHermitian ∧ γ s * γ s = γ s ∧ Matrix.trace (γ s) = 1) ∧
      HasDerivAt γ (toMatrix A.val) 0 :=
  ⟨curve h A,curve_smooth h A,curve_zero h A,curve_physical h A,curve_hasDerivAt_zero h A⟩

end
end QubitOracle.AdaptiveDesign.PureTangentCurves
