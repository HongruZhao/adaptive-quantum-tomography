import QubitOracle.AdaptiveDesign.PureSmoothChartEndpoints
import QubitOracle.AdaptiveDesign.PureSLDMetric

/-! Identification of the pushed-forward Gaussian covariance with twice
the inverse SLD metric in any invertible local coordinate system. -/
namespace QubitOracle.AdaptiveDesign.PureChartCovariance
open QubitOracle QubitOracle.Paper PureMatrixController P2Adaptive
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
variable {d : ℕ}
abbrev Coordinates (d : ℕ) := EuclideanSpace ℝ (TangentIndex d)

def qfiOperator (J : Coordinates d ≃L[ℝ] Coordinates d) : Coordinates d →L[ℝ] Coordinates d :=
  J.symm.toContinuousLinearMap.adjoint.comp J.symm.toContinuousLinearMap

def inverseQfiOperator (J : Coordinates d ≃L[ℝ] Coordinates d) : Coordinates d →L[ℝ] Coordinates d :=
  J.toContinuousLinearMap.comp J.toContinuousLinearMap.adjoint

theorem qfi_inverse (J : Coordinates d ≃L[ℝ] Coordinates d) :
    (qfiOperator J).comp (inverseQfiOperator J) = ContinuousLinearMap.id ℝ _ ∧
    (inverseQfiOperator J).comp (qfiOperator J) = ContinuousLinearMap.id ℝ _ := by
  constructor
  · unfold qfiOperator inverseQfiOperator
    rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc J.symm.toContinuousLinearMap,
      ContinuousLinearEquiv.coe_symm_comp_coe, ContinuousLinearMap.id_comp,
      ← ContinuousLinearMap.adjoint_comp, ContinuousLinearEquiv.coe_comp_coe_symm,
      ContinuousLinearMap.adjoint_id]
  · unfold qfiOperator inverseQfiOperator
    rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc J.toContinuousLinearMap.adjoint,
      ← ContinuousLinearMap.adjoint_comp, ContinuousLinearEquiv.coe_symm_comp_coe,
      ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_comp,
      ContinuousLinearEquiv.coe_comp_coe_symm]

theorem qfi_is_sld (truth : PureVector d) (J : Coordinates d ≃L[ℝ] Coordinates d)
    (u v : Coordinates d) :
    PureSLDMetric.metricFromSLD truth (PureSLDMetric.normalizedLift truth (J.symm u))
      (PureSLDMetric.normalizedLift truth (J.symm v)) = ⟪u,qfiOperator J v⟫_ℝ := by
  rw [PureSLDMetric.normalized_metric]
  symm
  exact ContinuousLinearMap.adjoint_inner_right J.symm.toContinuousLinearMap _ _

theorem covariance_normalized (u v : Coordinates d) :
    covarianceBilin (multivariateGaussian 0 ((2:ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) u v =
      2*⟪u,v⟫_ℝ := by
  rw [covarianceBilin_multivariateGaussian (Matrix.PosSemidef.one.smul (by norm_num : (0:ℝ) ≤ 2))]
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  rw [dotProduct_comm]

/-- The Gaussian in the smooth-chart limit has covariance operator `2 H⁻¹`.
The inverse here is proved on both sides above, rather than named by fiat. -/
theorem covariance_eq_twice_inverse_qfi (J : Coordinates d ≃L[ℝ] Coordinates d)
    (u v : Coordinates d) :
    covarianceBilin
      ((multivariateGaussian 0 ((2:ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))).map J)
      u v = 2*⟪u,inverseQfiOperator J v⟫_ℝ := by
  change covarianceBilin
    ((multivariateGaussian 0 ((2:ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))).map J.toContinuousLinearMap)
    u v = _
  rw [covarianceBilin_map IsGaussian.memLp_two_id J.toContinuousLinearMap,
    covariance_normalized]
  congr 1
  unfold inverseQfiOperator
  exact ContinuousLinearMap.adjoint_inner_left J.toContinuousLinearMap _ _

end
end QubitOracle.AdaptiveDesign.PureChartCovariance
