import QubitOracle.AdaptiveDesign.GeneralWeightedOracle

/-! The matrix optimization behind the weighted Gill--Massar constant.
Positive weights have an explicit positive-definite minimizer. -/
namespace QubitOracle.AdaptiveDesign.WeightedInformationOptimization
open Matrix
open scoped BigOperators MatrixOrder
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem trace_inner (X Y : Matrix ι ι ℝ) :
    (X.transpose*Y).trace = ∑ ij : ι×ι, X ij.1 ij.2*Y ij.1 ij.2 := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem trace_cauchy_schwarz (X Y : Matrix ι ι ℝ) :
    (X.transpose*Y).trace^2 ≤ (X.transpose*X).trace*(Y.transpose*Y).trace := by
  simp only [trace_inner]
  simpa only [pow_two] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun ij : ι×ι => X ij.1 ij.2) (fun ij : ι×ι => Y ij.1 ij.2)

theorem sqrt_posDef {A : Matrix ι ι ℝ} (hA : A.PosDef) : (CFC.sqrt A).PosDef := by
  have hp := (CFC.sqrt_nonneg A).posSemidef
  apply hp.posDef_iff_det_ne_zero.mpr
  intro hz
  have hsq := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hd := congrArg Matrix.det hsq
  rw [Matrix.det_mul,hz,zero_mul] at hd
  exact hA.det_pos.ne' hd.symm

theorem sqrt_transpose (A : Matrix ι ι ℝ) : (CFC.sqrt A).transpose = CFC.sqrt A := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (CFC.sqrt_nonneg A).posSemidef.isHermitian.eq

theorem weighted_trace_product (A B : Matrix ι ι ℝ) (hA : A.PosSemidef) (hB : B.PosDef) :
    (CFC.sqrt A).trace^2 ≤ (A*B⁻¹).trace*B.trace := by
  let S := CFC.sqrt A
  let T := CFC.sqrt B
  have hS : S.transpose=S := sqrt_transpose A
  have hT : T.transpose=T := sqrt_transpose B
  have hS2 : S*S=A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  have hT2 : T*T=B := CFC.sqrt_mul_sqrt_self B hB.posSemidef.nonneg
  have hTp := sqrt_posDef hB
  have hTi : T*T⁻¹=1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hTp.det_pos.ne')
  have hTi' : T⁻¹*T=1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hTp.det_pos.ne')
  have hTis : T⁻¹.transpose=T⁻¹ := by rw [Matrix.transpose_nonsing_inv,hT]
  have hTi2 : T⁻¹*T⁻¹=B⁻¹ := by
    symm
    apply Matrix.inv_eq_right_inv
    rw [← hT2]
    calc
      _ = T*(T*T⁻¹)*T⁻¹ := by noncomm_ring
      _ = 1 := by rw [hTi,mul_one,hTi]
  have hcross : ((T⁻¹*S).transpose*T).trace=S.trace := by
    rw [Matrix.transpose_mul,hS,hTis,Matrix.mul_assoc,hTi',mul_one]
  have hnorm : ((T⁻¹*S).transpose*(T⁻¹*S)).trace=(A*B⁻¹).trace := by
    rw [Matrix.transpose_mul,hS,hTis]
    calc
      _ = (S*(T⁻¹*T⁻¹)*S).trace := by congr 1; noncomm_ring
      _ = (S*B⁻¹*S).trace := by rw [hTi2]
      _ = _ := by rw [Matrix.trace_mul_cycle,hS2]
  have hh := trace_cauchy_schwarz (T⁻¹*S) T
  rw [hcross,hnorm,hT,hT2] at hh
  exact hh

theorem weighted_trace_lower (A B : Matrix ι ι ℝ) (hA : A.PosSemidef) (hB : B.PosDef)
    (b : ℝ) (hb : 0 < b) (hbudget : B.trace ≤ b) :
    (CFC.sqrt A).trace^2/b ≤ (A*B⁻¹).trace := by
  apply (div_le_iff₀ hb).mpr
  have hp : 0 ≤ (A*B⁻¹).trace := by
    have hps := (hB.inv.posSemidef.mul_mul_conjTranspose_same (CFC.sqrt A)).trace_nonneg
    rw [Matrix.conjTranspose_eq_transpose_of_trivial,sqrt_transpose,Matrix.trace_mul_cycle,
      CFC.sqrt_mul_sqrt_self A hA.nonneg] at hps
    exact hps
  exact (weighted_trace_product A B hA hB).trans
    (mul_le_mul_of_nonneg_left hbudget hp)

def minimizer (A : Matrix ι ι ℝ) (b : ℝ) : Matrix ι ι ℝ :=
  (b/(CFC.sqrt A).trace) • CFC.sqrt A

theorem minimizer_properties [Nonempty ι] (A : Matrix ι ι ℝ) (hA : A.PosDef)
    (b : ℝ) (hb : 0 < b) :
    (minimizer A b).PosDef ∧ (minimizer A b).trace=b ∧
      (A*(minimizer A b)⁻¹).trace=(CFC.sqrt A).trace^2/b := by
  let S := CFC.sqrt A
  have hS := sqrt_posDef hA
  have hs : 0 < S.trace := hS.trace_pos
  have hS2 : S*S=A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hSi : S*S⁻¹=1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hS.det_pos.ne')
  have hSinv : (minimizer A b)⁻¹ = (S.trace/b) • S⁻¹ := by
    apply Matrix.inv_eq_right_inv
    unfold minimizer
    change ((b/S.trace) • S)*((S.trace/b) • S⁻¹) = 1
    rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,hSi]
    have he : (b/S.trace)*(S.trace/b)=1 := by field_simp
    rw [he,one_smul]
  refine ⟨hS.smul (div_pos hb hs),?_,?_⟩
  · change ((b/S.trace) • S).trace=b
    rw [Matrix.trace_smul,smul_eq_mul]
    field_simp
  · change (A*(minimizer A b)⁻¹).trace=S.trace^2/b
    rw [hSinv,Matrix.mul_smul,Matrix.trace_smul,smul_eq_mul,← hS2]
    rw [Matrix.mul_assoc,hSi,mul_one]
    ring

theorem minimizer_optimal [Nonempty ι] (A : Matrix ι ι ℝ) (hA : A.PosDef)
    (b : ℝ) (hb : 0 < b) (B : Matrix ι ι ℝ) (hB : B.PosDef) (hbudget : B.trace ≤ b) :
    (A*(minimizer A b)⁻¹).trace ≤ (A*B⁻¹).trace := by
  rw [(minimizer_properties A hA b hb).2.2]
  exact weighted_trace_lower A B hA.posSemidef hB b hb hbudget

theorem congruence_posDef (A R : Matrix ι ι ℝ) (hA : A.PosDef) (hR : R.PosDef) :
    (R*A*R).PosDef := by
  have hs : R.transpose=R := by simpa using hR.isHermitian.eq
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,hs] using
    hA.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hR.isUnit)

theorem inverse_congruence (R B : Matrix ι ι ℝ) (hR : R.PosDef) (hB : B.PosDef) :
    (R*B*R)⁻¹=R⁻¹*B⁻¹*R⁻¹ := by
  have hRi := Matrix.mul_nonsing_inv R (isUnit_iff_ne_zero.mpr hR.det_pos.ne')
  have hBi := Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hB.det_pos.ne')
  apply Matrix.inv_eq_right_inv
  calc
    _ = R*B*(R*R⁻¹)*B⁻¹*R⁻¹ := by noncomm_ring
    _ = R*(B*B⁻¹)*R⁻¹ := by rw [hRi,mul_one]; noncomm_ring
    _ = 1 := by rw [hBi,mul_one,hRi]

theorem whitened_trace (W B R : Matrix ι ι ℝ) (hB : B.PosDef) (hR : R.PosDef) :
    ((R*W*R)*(R*B*R)⁻¹).trace=(W*B⁻¹).trace := by
  rw [inverse_congruence R B hR hB]
  have hRi := Matrix.mul_nonsing_inv R (isUnit_iff_ne_zero.mpr hR.det_pos.ne')
  have hiR := Matrix.nonsing_inv_mul R (isUnit_iff_ne_zero.mpr hR.det_pos.ne')
  calc
    _ = (R*W*(R*R⁻¹)*B⁻¹*R⁻¹).trace := by congr 1; noncomm_ring
    _ = (R*(W*B⁻¹)*R⁻¹).trace := by rw [hRi,mul_one]; congr 1; noncomm_ring
    _ = _ := by rw [Matrix.trace_mul_cycle,hiR,one_mul]

/-- The weighted information bound in the paper's original coordinates,
with the canonical positive inverse square root of the quantum metric. -/
theorem gillMassar_weighted (W H information : Matrix ι ι ℝ)
    (hW : W.PosSemidef) (hH : H.PosDef) (hI : information.PosDef)
    (b : ℝ) (hb : 0 < b) (hbudget : (H⁻¹*information).trace ≤ b) :
    FiniteRegularOracle.oracleConstant W H b ≤ (W*information⁻¹).trace := by
  let R := CFC.sqrt (H⁻¹)
  have hR : R.PosDef := sqrt_posDef hH.inv
  have hRT : R.transpose=R := sqrt_transpose _
  have hA : (R*W*R).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,hRT] using
      hW.mul_mul_conjTranspose_same R
  have hB : (R*information*R).PosDef := congruence_posDef information R hI hR
  have htr : (R*information*R).trace=(H⁻¹*information).trace := by
    rw [Matrix.trace_mul_cycle,CFC.sqrt_mul_sqrt_self _ hH.inv.posSemidef.nonneg]
  have hh := weighted_trace_lower (R*W*R) (R*information*R) hA hB b hb (by rwa [htr])
  rwa [whitened_trace W information R hI hR] at hh

end
end QubitOracle.AdaptiveDesign.WeightedInformationOptimization
