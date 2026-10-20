import QubitOracle.AdaptiveDesign.PureAmplitudeLoss

/-! Exact Frobenius identities behind the intrinsic correction. These
identities concern the implemented projector and normalization maps. -/
namespace QubitOracle.AdaptiveDesign.TangentGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive
open scoped BigOperators InnerProductSpace Matrix.Norms.Frobenius
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

theorem tangentProjector_norm_sq {d : ℕ} (h : PureVector d)
    (B : HermitianSpace (d+1)) :
    ‖tangentProjector h B‖^2 = 2*‖trueCoordinate h B‖^2 := by
  rw [← real_inner_self_eq_norm_sq, ← trueLift_coordinate, trueLift_inner,
    trueCoordinate_lift, real_inner_self_eq_norm_sq]

theorem preliminaryError_normal_norm_sq {d : ℕ} (h truth : PureVector d) :
    ‖((pureParameter d h).val-(pureParameter d truth).val)-
      (preliminaryTangentError h truth).val‖^2 =
    ‖(pureParameter d h).val-(pureParameter d truth).val‖^4/2 := by
  let e := (pureParameter d h).val-(pureParameter d truth).val
  let q := ⟪(pureParameter d h).val,(pureParameter d truth).val⟫_ℝ
  have hp : (preliminaryTangentError h truth).val = tangentProjector h e := rfl
  have he : ‖e‖^2 = 2-2*q := by
    dsimp [e,q]
    rw [norm_sub_sq_real, pureParameter_norm, pureParameter_norm]
    ring
  have ht : ‖tangentProjector h e‖^2 = 2*(q-q^2) := by
    rw [tangentProjector_norm_sq]
    have hc := trueCoordinate_norm_sq h (pureParameter d truth).val
      (pureProjector_idempotent truth)
    have hneg : e = -((pureParameter d truth).val-(pureParameter d h).val) := by
      dsimp [e]; abel
    rw [hneg, map_neg, norm_neg, hc]
  have hi : ⟪e,tangentProjector h e⟫_ℝ = ‖tangentProjector h e‖^2 := by
    calc
      _ = 2*‖trueCoordinate h e‖^2 := by
        rw [← trueLift_coordinate, real_inner_comm, trueLift_inner,
          real_inner_self_eq_norm_sq]
      _ = _ := (tangentProjector_norm_sq h e).symm
  change ‖e-(preliminaryTangentError h truth).val‖^2 = ‖e‖^4/2
  rw [hp, norm_sub_sq_real, hi, ht]
  nlinarith [sq_nonneg (‖e‖^2-(2-2*q))]

theorem preliminaryError_normal_norm {d : ℕ} (h truth : PureVector d) :
    ‖((pureParameter d h).val-(pureParameter d truth).val)-
      (preliminaryTangentError h truth).val‖ =
    ‖(pureParameter d h).val-(pureParameter d truth).val‖^2/Real.sqrt 2 := by
  have hs := preliminaryError_normal_norm_sq h truth
  have hr : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  apply (eq_div_iff hp.ne').mpr
  apply (sq_eq_sq₀ (mul_nonneg (norm_nonneg _) hp.le) (sq_nonneg _)).mp
  rw [mul_pow, hr]
  nlinarith only [hs]

theorem tangent_trace_zero {d : ℕ} (h : PureVector d) (A : tangentSpace h) :
    Matrix.trace (rankOneDensity h.val*toMatrix A.val) = 0 := by
  have hh := congrArg Matrix.trace (tangent_sandwich_zero h A)
  rw [Matrix.trace_mul_cycle, pureProjector_idempotent, Matrix.trace_zero] at hh
  exact hh

theorem updatedState_overlap {d : ℕ} (h : PureVector d) (A : tangentSpace h) :
    ⟪(pureParameter d h).val,(pureParameter d (updatedPureVector h A)).val⟫_ℝ =
      (1+‖tangentVector h A‖^2)⁻¹ := by
  rw [inner_eq_trace]
  change (Matrix.trace (updatedState h A*rankOneDensity h.val)).re = _
  rw [updatedState_matrix_formula, Matrix.smul_mul, Matrix.add_mul, Matrix.add_mul,
    pureProjector_idempotent]
  have hz : toMatrix A.val*rankOneDensity h.val*toMatrix A.val*rankOneDensity h.val = 0 := by
    calc
      _ = toMatrix A.val*(rankOneDensity h.val*toMatrix A.val*rankOneDensity h.val) := by
        noncomm_ring
      _ = 0 := by rw [tangent_sandwich_zero, Matrix.mul_zero]
  rw [hz, add_zero, Matrix.trace_smul, Matrix.trace_add,
    rankOneDensity_trace_eq_one _ h.property, Matrix.trace_mul_comm (toMatrix A.val),
    tangent_trace_zero, add_zero]
  simp only [Complex.real_smul, mul_one, Complex.ofReal_re]

theorem updatedState_displacement_sq {d : ℕ} (h : PureVector d) (A : tangentSpace h) :
    ‖updatedState h A-rankOneDensity h.val‖^2 =
      2*‖tangentVector h A‖^2/(1+‖tangentVector h A‖^2) := by
  have hm : ‖updatedState h A-rankOneDensity h.val‖ =
      ‖(pureParameter d (updatedPureVector h A)).val-(pureParameter d h).val‖ :=
    toMatrix_norm ((pureParameter d (updatedPureVector h A)).val-(pureParameter d h).val)
  rw [hm, norm_sub_sq_real, pureParameter_norm, pureParameter_norm,
    real_inner_comm, updatedState_overlap]
  field_simp [show (1+‖tangentVector h A‖^2) ≠ 0 by positivity]
  ring

theorem tangent_norm_sq {d : ℕ} (h : PureVector d) (A : tangentSpace h) :
    ‖A‖^2 = 2*‖tangentVector h A‖^2 := by
  let P := rankOneDensity h.val
  let B := toMatrix A.val
  have ht : P*B+B*P = B := (tangentSpace_mem h A.val).mp A.property
  have htr : Matrix.trace (B*B) = 2*Matrix.trace (B*P*B) := by
    calc
      _ = Matrix.trace ((P*B+B*P)*B) := by rw [ht]
      _ = Matrix.trace (P*B*B)+Matrix.trace (B*P*B) := by
        rw [Matrix.add_mul, Matrix.trace_add]
      _ = _ := by rw [Matrix.trace_mul_cycle P B B]; ring
  have hv : (Matrix.trace (B*P*B)).re = ‖tangentVector h A‖^2 := by
    have hm := GlobalPFSIC.projector_mulVec B h.val
    rw [(toMatrix_isHermitian A.val).eq] at hm
    change GlobalPFSIC.projector (B.mulVec h.val) = B*P*B at hm
    rw [← hm, EuclideanSpace.norm_sq_eq]
    simp [GlobalPFSIC.projector, Matrix.vecMulVec, Matrix.trace, Matrix.diag,
      Complex.re_sum, Complex.mul_conj, Complex.ofReal_re, tangentVector,
      WithLp.ofLp_toLp, Complex.sq_norm, B]
  change ‖A.val‖^2 = _
  rw [← real_inner_self_eq_norm_sq, inner_eq_trace]
  change (Matrix.trace (B*B)).re = _
  rw [htr]
  norm_num [Complex.mul_re, hv]

theorem updatedState_displacement_le {d : ℕ} (h : PureVector d) (A : tangentSpace h) :
    ‖updatedState h A-rankOneDensity h.val‖ ≤ ‖A‖ := by
  have hs := updatedState_displacement_sq h A
  have hb : 2*‖tangentVector h A‖^2/(1+‖tangentVector h A‖^2) ≤
      2*‖tangentVector h A‖^2 :=
    div_le_self (by positivity) (le_add_of_nonneg_right (sq_nonneg _))
  have hn := tangent_norm_sq h A
  nlinarith [norm_nonneg (updatedState h A-rankOneDensity h.val), norm_nonneg A]

end
end QubitOracle.AdaptiveDesign.TangentGLS
