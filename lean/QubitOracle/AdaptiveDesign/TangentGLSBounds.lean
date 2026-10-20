import QubitOracle.AdaptiveDesign.TangentGLSProjection
import QubitOracle.AdaptiveDesign.TangentGLSRetraction

/-! Quantitative bounds for the actual intrinsic GLS update. -/

namespace QubitOracle.AdaptiveDesign.TangentGLS

open QubitOracle.Paper GlobalPFSICHermitian PureMatrixController
open scoped BigOperators InnerProductSpace ComplexOrder Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

theorem toMatrix_norm {n : ℕ} (A : HermitianSpace n) : ‖toMatrix A‖ = ‖A‖ := by
  let B : Matrix (Fin n) (Fin n) ℂ := toMatrix A
  have hfrob : ‖toMatrix A‖ ^ 2 = ∑ i : Fin n, ∑ j : Fin n, ‖B i j‖ ^ 2 := by
    calc
      _ = ((∑ i : Fin n, ∑ j : Fin n, ‖B i j‖ ^ 2) ^ (1/2 : ℝ)) ^ 2 :=
        congrArg (fun r : ℝ => r^2) (Matrix.frobenius_norm_def B)
      _ = _ := by
        rw [← Real.sqrt_eq_rpow]
        simp only [Real.rpow_two]
        exact Real.sq_sqrt (Finset.sum_nonneg fun i _ =>
          Finset.sum_nonneg fun j _ => sq_nonneg ‖B i j‖)
  have hs : ‖toMatrix A‖ ^ 2 = ‖A‖ ^ 2 := by
    rw [hfrob, ← real_inner_self_eq_norm_sq A, inner_eq_trace]
    have hherm (i j : Fin n) : toMatrix A j i = star (toMatrix A i j) := by
      have h := congrFun (congrFun (toMatrix_isHermitian A).eq j) i
      exact h.symm
    change (∑ i : Fin n, ∑ j : Fin n, ‖toMatrix A i j‖^2) =
      (Matrix.trace (toMatrix A * toMatrix A)).re
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hherm i j]
    simp [Complex.mul_conj, Complex.sq_norm]
  nlinarith [norm_nonneg (toMatrix A), norm_nonneg A]

theorem pureParameter_norm {d : ℕ} (h : PureVector d) :
    ‖(P2Adaptive.pureParameter d h).val‖ = 1 := by
  have hs : ‖(P2Adaptive.pureParameter d h).val‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_eq_trace]
    change (Matrix.trace (rankOneDensity h.val * rankOneDensity h.val)).re = 1
    rw [pureProjector_idempotent, rankOneDensity_trace_eq_one _ h.property]
    rfl
  nlinarith [norm_nonneg (P2Adaptive.pureParameter d h).val]

theorem pureProjector_norm {d : ℕ} (h : PureVector d) :
    ‖rankOneDensity h.val‖ = 1 :=
  (toMatrix_norm (P2Adaptive.pureParameter d h).val).trans (pureParameter_norm h)

theorem preliminaryError_norm_le_two {d : ℕ} (h truth : PureVector d) :
    ‖(P2Adaptive.pureParameter d h).val - (P2Adaptive.pureParameter d truth).val‖ ≤ 2 := by
  simpa only [pureParameter_norm, one_add_one_eq_two] using
    norm_sub_le (P2Adaptive.pureParameter d h).val (P2Adaptive.pureParameter d truth).val

theorem preliminaryTangentError_norm_le {d : ℕ} (h truth : PureVector d) :
    ‖preliminaryTangentError h truth‖ ≤
      ‖(P2Adaptive.pureParameter d h).val - (P2Adaptive.pureParameter d truth).val‖ := by
  exact (tangentSpace h).norm_orthogonalProjectionOnto_apply_le _

theorem preliminaryError_normal_bound {d : ℕ} (h truth : PureVector d) :
    ‖((P2Adaptive.pureParameter d h).val - (P2Adaptive.pureParameter d truth).val) -
        (preliminaryTangentError h truth).val‖ ≤
      3 * ‖(P2Adaptive.pureParameter d h).val - (P2Adaptive.pureParameter d truth).val‖ ^ 2 := by
  let e := rankOneDensity h.val - rankOneDensity truth.val
  have he : ‖e‖ =
      ‖(P2Adaptive.pureParameter d h).val - (P2Adaptive.pureParameter d truth).val‖ :=
    toMatrix_norm ((P2Adaptive.pureParameter d h).val - (P2Adaptive.pureParameter d truth).val)
  rw [← toMatrix_norm (((P2Adaptive.pureParameter d h).val -
    (P2Adaptive.pureParameter d truth).val) - (preliminaryTangentError h truth).val)]
  change ‖(rankOneDensity h.val - rankOneDensity truth.val) -
    toMatrix (preliminaryTangentError h truth).val‖ ≤ _
  rw [preliminaryError_normal_quadratic]
  have hsq : ‖e * e‖ ≤ ‖e‖ ^ 2 := by simpa [pow_two] using Matrix.frobenius_norm_mul e e
  have hp : ‖rankOneDensity h.val * (e * e) * rankOneDensity h.val‖ ≤ ‖e‖ ^ 2 := by
    calc
      _ ≤ ‖rankOneDensity h.val * (e * e)‖ * ‖rankOneDensity h.val‖ :=
        Matrix.frobenius_norm_mul _ _
      _ = ‖rankOneDensity h.val * (e * e)‖ := by rw [pureProjector_norm, mul_one]
      _ ≤ ‖rankOneDensity h.val‖ * ‖e * e‖ := Matrix.frobenius_norm_mul _ _
      _ ≤ ‖e‖ ^ 2 := by simpa only [pureProjector_norm, one_mul] using hsq
  have ht := norm_sub_le
    (rankOneDensity h.val * (e * e) * rankOneDensity h.val +
      rankOneDensity h.val * (e * e) * rankOneDensity h.val) (e * e)
  have ha := norm_add_le (rankOneDensity h.val * (e * e) * rankOneDensity h.val)
    (rankOneDensity h.val * (e * e) * rankOneDensity h.val)
  change ‖(rankOneDensity h.val * (e * e) * rankOneDensity h.val +
    rankOneDensity h.val * (e * e) * rankOneDensity h.val) - e * e‖ ≤ _
  rw [← he]
  linarith

theorem tangentVector_norm_le {d : ℕ} (h : PureVector d) (A : tangentSpace h) :
    ‖tangentVector h A‖ ≤ ‖A‖ := by
  have hb := Matrix.frobenius_norm_mul (toMatrix A.val) (Matrix.replicateCol Unit h.val)
  rw [← Matrix.replicateCol_mulVec, Matrix.frobenius_norm_replicateCol,
    Matrix.frobenius_norm_replicateCol] at hb
  change ‖tangentVector h A‖ ≤ ‖toMatrix A.val‖ * ‖pureVector h‖ at hb
  rw [pureVector_norm, toMatrix_norm, mul_one] at hb
  exact hb

/-- The normalization error is quadratic uniformly for small tangent steps. -/
theorem updatedState_remainder_bound {d : ℕ} (h : PureVector d) (A : tangentSpace h)
    (hA : ‖A‖ ≤ 1) :
    ‖updatedState h A - (rankOneDensity h.val + toMatrix A.val)‖ ≤ 3 * ‖A‖^2 := by
  have hs : 0 ≤ ‖tangentVector h A‖^2 := sq_nonneg _
  have hc : (1 + ‖tangentVector h A‖^2)⁻¹ ≤ 1 := by
    exact (inv_le_one₀ (by positivity)).mpr (by linarith)
  have hquad : ‖toMatrix A.val * rankOneDensity h.val * toMatrix A.val‖ ≤ ‖A‖^2 := by
    calc
      _ ≤ (‖toMatrix A.val‖ * ‖rankOneDensity h.val‖) * ‖toMatrix A.val‖ :=
        (Matrix.frobenius_norm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (Matrix.frobenius_norm_mul _ _) (norm_nonneg _))
      _ = _ := by rw [pureProjector_norm, toMatrix_norm]; simp [pow_two]
  have hbase : ‖rankOneDensity h.val + toMatrix A.val‖ ≤ 2 := by
    have hb := norm_add_le (rankOneDensity h.val) (toMatrix A.val)
    rw [pureProjector_norm, toMatrix_norm] at hb
    change ‖rankOneDensity h.val + toMatrix A.val‖ ≤ 1 + ‖A‖ at hb
    exact hb.trans (by linarith)
  have hv : ‖tangentVector h A‖^2 ≤ ‖A‖^2 := by
    nlinarith [tangentVector_norm_le h A, norm_nonneg A, norm_nonneg (tangentVector h A)]
  rw [updatedState_exact_remainder, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (by positivity))]
  have hb := norm_sub_le (toMatrix A.val * rankOneDensity h.val * toMatrix A.val)
    ((‖tangentVector h A‖^2) • (rankOneDensity h.val + toMatrix A.val))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs] at hb
  calc
    _ ≤ ‖toMatrix A.val * rankOneDensity h.val * toMatrix A.val -
        (‖tangentVector h A‖^2) • (rankOneDensity h.val + toMatrix A.val)‖ := by
      exact mul_le_of_le_one_left (norm_nonneg _) hc
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hbase hs]

/-- A global quadratic bound also covers exceptionally large corrections. -/
theorem updatedState_remainder_bound_global {d : ℕ} (h : PureVector d) (A : tangentSpace h) :
    ‖updatedState h A - (rankOneDensity h.val + toMatrix A.val)‖ ≤ 3 * ‖A‖^2 := by
  by_cases hA : ‖A‖ ≤ 1
  · exact updatedState_remainder_bound h A hA
  · have hn : 1 ≤ ‖A‖ := (lt_of_not_ge hA).le
    have hR : ‖updatedState h A‖ = 1 := pureProjector_norm (updatedPureVector h A)
    have hb := norm_sub_le (updatedState h A) (rankOneDensity h.val + toMatrix A.val)
    have hp := norm_add_le (rankOneDensity h.val) (toMatrix A.val)
    rw [hR] at hb
    rw [pureProjector_norm, toMatrix_norm] at hp
    change ‖rankOneDensity h.val + toMatrix A.val‖ ≤ 1 + ‖A‖ at hp
    nlinarith [sq_nonneg (‖A‖-1)]

def tangentProjector {d : ℕ} (h : PureVector d) :
    HermitianSpace (d+1) →L[ℝ] HermitianSpace (d+1) := (tangentSpace h).starProjection

theorem tangentProjector_apply {d : ℕ} (h : PureVector d) (A : HermitianSpace (d+1)) :
    tangentProjector h A = tangentProjectionVector h A :=
  tangentProjectionVector_eq_projection h A

theorem tangentProjector_norm_le {d : ℕ} (h : PureVector d) : ‖tangentProjector h‖ ≤ 1 :=
  (tangentSpace h).starProjection_norm_le

/-- Changing the preliminary ray changes its tangent projector at most
linearly; no eigenvector phase or complement frame is involved. -/
theorem tangentProjector_difference_bound {d : ℕ} (h truth : PureVector d)
    (A : HermitianSpace (d+1)) :
    ‖tangentProjector h A - tangentProjector truth A‖ ≤
      6 * ‖(P2Adaptive.pureParameter d h).val - (P2Adaptive.pureParameter d truth).val‖ * ‖A‖ := by
  let P := rankOneDensity h.val
  let Q := rankOneDensity truth.val
  let e := P-Q
  let B := toMatrix A
  have hP : ‖P‖ = 1 := pureProjector_norm h
  have hQ : ‖Q‖ = 1 := pureProjector_norm truth
  have he : ‖e‖ = ‖(P2Adaptive.pureParameter d h).val - (P2Adaptive.pureParameter d truth).val‖ :=
    toMatrix_norm ((P2Adaptive.pureParameter d h).val - (P2Adaptive.pureParameter d truth).val)
  have hB : ‖B‖ = ‖A‖ := toMatrix_norm A
  have heq : tangentProjectionMatrix h A - tangentProjectionMatrix truth A =
      e*B + B*e - ((e*B*P + Q*B*e) + (e*B*P + Q*B*e)) := by
    dsimp [tangentProjectionMatrix, P, Q, e, B]
    noncomm_ring
  have h1 : ‖e*B‖ ≤ ‖e‖*‖B‖ := Matrix.frobenius_norm_mul _ _
  have h2 : ‖B*e‖ ≤ ‖e‖*‖B‖ := by simpa only [mul_comm] using Matrix.frobenius_norm_mul B e
  have h3 : ‖e*B*P‖ ≤ ‖e‖*‖B‖ := by
    simpa only [hP, mul_one] using (Matrix.frobenius_norm_mul (e*B) P).trans
      (mul_le_mul_of_nonneg_right h1 (norm_nonneg P))
  have h4 : ‖Q*B*e‖ ≤ ‖e‖*‖B‖ := by
    have hb := (Matrix.frobenius_norm_mul (Q*B) e).trans
      (mul_le_mul_of_nonneg_right (Matrix.frobenius_norm_mul Q B) (norm_nonneg e))
    simpa only [hQ, one_mul, mul_comm] using hb
  rw [← toMatrix_norm (tangentProjector h A - tangentProjector truth A),
    tangentProjector_apply, tangentProjector_apply]
  change ‖tangentProjectionMatrix h A - tangentProjectionMatrix truth A‖ ≤ _
  rw [heq, ← he, ← hB]
  have ha := norm_add_le (e*B) (B*e)
  have hb := norm_add_le (e*B*P) (Q*B*e)
  have hc := norm_add_le (e*B*P + Q*B*e) (e*B*P + Q*B*e)
  have hd := norm_sub_le (e*B + B*e) ((e*B*P + Q*B*e) + (e*B*P + Q*B*e))
  nlinarith

theorem tangentProjector_lipschitz {d : ℕ} (h truth : PureVector d) :
    ‖tangentProjector h - tangentProjector truth‖ ≤
      6 * ‖(P2Adaptive.pureParameter d h).val - (P2Adaptive.pureParameter d truth).val‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact tangentProjector_difference_bound h truth

end
end QubitOracle.AdaptiveDesign.TangentGLS
