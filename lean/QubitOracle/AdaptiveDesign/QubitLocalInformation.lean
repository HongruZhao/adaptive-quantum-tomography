import QubitOracle.AdaptiveDesign.P1WeightedInformation
import QubitOracle.AdaptiveDesign.PhysicalModelCharacterization
import Mathlib.Analysis.InnerProductSpace.LinearMap
import QubitOracle.AdaptiveDesign.QuantumFidelityBridges
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.MixedAxisFisher
import QubitOracle.Paper.QubitFoundations
/-! Exact qubit eigenvalues and a uniform local Lipschitz bound for
single-axis Fisher information, independent of the chosen axis. -/
namespace QubitOracle.AdaptiveDesign.QubitLocalInformation
open QubitOracle QubitOracle.Paper
open scoped BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

theorem qubit_eigenvalues (theta : Fin 3 → ℝ) (h : (qubitDensityMatrix theta).IsHermitian) :
    let r := Real.sqrt (blochNormSq theta)
    (h.eigenvalues 0=(1+r)/2 ∧ h.eigenvalues 1=(1-r)/2) ∨
    (h.eigenvalues 0=(1-r)/2 ∧ h.eigenvalues 1=(1+r)/2) := by
  dsimp only
  have hsum : h.eigenvalues 0+h.eigenvalues 1=1 := by
    have hh := congrArg Complex.re h.trace_eq_sum_eigenvalues
    rw [qubitDensityMatrix_trace] at hh
    simpa [Fin.sum_univ_two] using hh.symm
  have hprod : h.eigenvalues 0*h.eigenvalues 1=(1-blochNormSq theta)/4 := by
    have hh := congrArg Complex.re h.det_eq_prod_eigenvalues
    rw [QuantumFidelityBridges.qubit_det] at hh
    simpa [Fin.prod_univ_two] using hh.symm
  have hs : Real.sqrt (blochNormSq theta)^2=blochNormSq theta :=
    Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (theta i)))
  have h1 : h.eigenvalues 1=1-h.eigenvalues 0 := by linarith
  rw [h1] at hprod
  have hz : (h.eigenvalues 0-(1+Real.sqrt (blochNormSq theta))/2)*
      (h.eigenvalues 0-(1-Real.sqrt (blochNormSq theta))/2)=0 := by nlinarith
  rcases mul_eq_zero.mp hz with hh|hh
  · left
    constructor <;> linarith
  · right
    constructor <;> linarith

theorem reciprocal_lipschitz (p q r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hp : |p| ≤ r) (hq : |q| ≤ r) :
    |(1-p^2)⁻¹-(1-q^2)⁻¹| ≤ (2/(1-r^2)^2)*|p-q| := by
  have hd : 0 < 1-r^2 := by nlinarith
  have hp2 : p^2 ≤ r^2 := by
    simpa [← pow_two,sq_abs] using mul_le_mul hp hp (abs_nonneg p) hr
  have hq2 : q^2 ≤ r^2 := by
    simpa [← pow_two,sq_abs] using mul_le_mul hq hq (abs_nonneg q) hr
  have hp0 : 0 < 1-p^2 := by linarith
  have hq0 : 0 < 1-q^2 := by linarith
  have he : (1-p^2)⁻¹-(1-q^2)⁻¹=(p^2-q^2)/((1-p^2)*(1-q^2)) := by field_simp; ring
  have hn : |p^2-q^2| ≤ 2*|p-q| := by
    rw [show p^2-q^2=(p-q)*(p+q) by ring,abs_mul]
    have hh : |p+q| ≤ 2 := (abs_add_le p q).trans (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hh (abs_nonneg (p-q))]
  have hden : (1-r^2)^2 ≤ (1-p^2)*(1-q^2) := by
    simpa [pow_two] using mul_le_mul (show 1-r^2 ≤ 1-p^2 by linarith)
      (show 1-r^2 ≤ 1-q^2 by linarith) hd.le hp0.le
  rw [he,abs_div,abs_of_pos (mul_pos hp0 hq0)]
  calc
    _ ≤ (2*|p-q|)/((1-p^2)*(1-q^2)) := div_le_div_of_nonneg_right hn (mul_pos hp0 hq0).le
    _ ≤ (2*|p-q|)/(1-r^2)^2 := div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hd) hden
    _ = _ := by ring

def axisInformation {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (theta a : E) : E →L[ℝ] E :=
  (1-⟪a,theta⟫_ℝ^2)⁻¹ • InnerProductSpace.rankOne ℝ a a

theorem axisInformation_lipschitz {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (theta eta a : E) (ha : ‖a‖=1) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (ht : ‖theta‖ ≤ r) (he : ‖eta‖ ≤ r) :
    ‖axisInformation theta a-axisInformation eta a‖ ≤ (2/(1-r^2)^2)*‖theta-eta‖ := by
  have hp : |⟪a,theta⟫_ℝ| ≤ r := (abs_real_inner_le_norm a theta).trans (by simpa [ha] using ht)
  have hq : |⟪a,eta⟫_ℝ| ≤ r := (abs_real_inner_le_norm a eta).trans (by simpa [ha] using he)
  have hdiff : |⟪a,theta⟫_ℝ-⟪a,eta⟫_ℝ| ≤ ‖theta-eta‖ := by
    simpa [inner_sub_right,ha] using abs_real_inner_le_norm a (theta-eta)
  simp only [axisInformation,← sub_smul,norm_smul,InnerProductSpace.norm_rankOne,ha,mul_one,Real.norm_eq_abs]
  exact (reciprocal_lipschitz _ _ r hr hr1 hp hq).trans
    (mul_le_mul_of_nonneg_left hdiff (by positivity))

/-- The operator in the Lipschitz theorem is exactly the binary Born
Fisher matrix used by the adaptive mixed-qubit protocol. -/
theorem axisInformation_matrix (theta a : Fin 3 → ℝ) :
    (Matrix.toEuclideanLin (mixedAxisFisher theta a)).toContinuousLinearMap=
      axisInformation (WithLp.toLp 2 theta) (WithLp.toLp 2 a) := by
  ext x i
  simp [axisInformation,InnerProductSpace.rankOne_apply,Matrix.toEuclideanLin_apply,
    mixedAxisFisher,blochDot,blochOuter,Matrix.mulVec, dotProduct,
    EuclideanSpace.inner_eq_star_dotProduct,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

end
end QubitOracle.AdaptiveDesign.QubitLocalInformation
