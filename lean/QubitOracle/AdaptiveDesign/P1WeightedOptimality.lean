import QubitOracle.AdaptiveDesign.P1WeightedCovariance

/-! Both sharp P1 design criteria, against every regular finite qubit POVM.
These are inverse-information criteria; no expected-risk or minimax limit is
silently inferred from a pointwise central limit theorem. -/
namespace QubitOracle.AdaptiveDesign.P1Weighted
open QubitOracle QubitOracle.Paper
open scoped BigOperators MatrixOrder
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

theorem inverse_trace_bound (S Q : Mat) (hS : S.transpose = S) (hQ : Q.PosDef)
    (hbudget : (S*S*Q).trace ≤ 1) : S.trace^2 ≤ Q⁻¹.trace := by
  let T := CFC.sqrt Q
  have ht := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Q)
  have hT : T.transpose = T := by
    simpa only [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial] using ht.isHermitian
  have hT2 : T*T = Q := by
    simpa only [pow_two] using CFC.sq_sqrt Q hQ.posSemidef.nonneg
  have hdet : IsUnit T.det := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hh := congrArg Matrix.det hT2
    simp only [Matrix.det_mul,hz,zero_mul] at hh
    exact hQ.det_pos.ne' hh.symm
  have hTi : T*T⁻¹=1 := Matrix.mul_nonsing_inv _ hdet
  have hTi' : T⁻¹*T=1 := Matrix.nonsing_inv_mul _ hdet
  have hTis : T⁻¹.transpose=T⁻¹ := by
    simpa only [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial] using ht.inv.isHermitian
  have hTi2 : T⁻¹*T⁻¹=Q⁻¹ := by
    symm
    apply Matrix.inv_eq_right_inv
    rw [← hT2]
    calc
      _ = T*(T*T⁻¹)*T⁻¹ := by noncomm_ring
      _ = 1 := by rw [hTi,mul_one,hTi]
  let X := S*T
  let Y := T⁻¹
  have hxy : (X.transpose*Y).trace = S.trace := by
    dsimp [X,Y]
    rw [Matrix.transpose_mul,hT,hS,Matrix.trace_mul_cycle,hTi',one_mul]
  have hxx : (X.transpose*X).trace = (S*S*Q).trace := by
    dsimp [X]
    rw [Matrix.transpose_mul,hT,hS]
    have he : (T*S)*(S*T) = T*(S*S)*T := by noncomm_ring
    rw [he,Matrix.trace_mul_cycle,hT2,Matrix.trace_mul_comm]
  have hyy : (Y.transpose*Y).trace = Q⁻¹.trace := by
    dsimp [Y]
    rw [hTis,hTi2]
  have hcs := frobeniusInner_sq_le X Y
  have hy := frobeniusSq_nonneg Y
  rw [← trace_transpose_mul_eq_frobeniusInner,hxy] at hcs
  change S.trace^2 ≤ frobeniusInner X X * frobeniusInner Y Y at hcs
  rw [← trace_transpose_mul_eq_frobeniusInner,← trace_transpose_mul_eq_frobeniusInner,hxx,hyy] at hcs
  change 0 ≤ frobeniusInner Y Y at hy
  rw [← trace_transpose_mul_eq_frobeniusInner,hyy] at hy
  nlinarith [mul_le_mul_of_nonneg_right hbudget hy]

def sldInverseRoot (r : Fin 3 → ℝ) : Mat := affine r 1 (-(1+mixedRadialGap r)⁻¹)

theorem sldInverseRoot_sq (r : Fin 3 → ℝ) (hr : blochNormSq r < 1) :
    sldInverseRoot r * sldInverseRoot r = qubitSLDFisherInv r := by
  have hs := mixedRadialGap_pos r hr
  have hn : blochNormSq r = 1-mixedRadialGap r^2 := by linarith [gap_sq r hr]
  rw [sldInverseRoot,affine_mul]
  have hb : 1 * -(1+mixedRadialGap r)⁻¹ + -(1+mixedRadialGap r)⁻¹*1 +
      -(1+mixedRadialGap r)⁻¹ * -(1+mixedRadialGap r)⁻¹ * blochNormSq r = -1 := by
    rw [hn]
    field_simp
    ring
  rw [hb]
  ext i j
  simp [affine,qubitSLDFisherInv,blochOuter,Matrix.one_apply]
  ring

theorem outer_trace (r : Fin 3 → ℝ) : (blochOuter r).trace = blochNormSq r := by
  simp [Matrix.trace,blochOuter,blochNormSq,pow_two]

theorem sldInverseRoot_trace (r : Fin 3 → ℝ) (hr : blochNormSq r < 1) :
    (sldInverseRoot r).trace = 2+mixedRadialGap r := by
  have hs := mixedRadialGap_pos r hr
  have hn : blochNormSq r = 1-mixedRadialGap r^2 := by linarith [gap_sq r hr]
  simp only [sldInverseRoot,affine,Matrix.trace_add,Matrix.trace_smul,Matrix.trace_one,outer_trace,smul_eq_mul]
  norm_num
  rw [hn]
  field_simp
  ring

def frobeniusCriterion (M : Mat) : ℝ := (1/2:ℝ)*M⁻¹.trace

theorem finite_qubitPOVM_frobenius_lower_bound (r : Fin 3 → ℝ) (hr : blochNormSq r < 1)
    {O : Type} [Fintype O] (P : QubitBlochPOVM O) (hP : (qubitClassicalFisher r P).PosDef) :
    (2+mixedRadialGap r)^2/2 ≤ frobeniusCriterion (qubitClassicalFisher r P) := by
  have hb : ((sldInverseRoot r)*(sldInverseRoot r)*qubitClassicalFisher r P).trace ≤ 1 := by
    rw [sldInverseRoot_sq r hr]
    exact qubit_interior_gillMassar r P hr
  have hh := inverse_trace_bound (sldInverseRoot r) (qubitClassicalFisher r P)
    (affine_transpose r _ _) hP hb
  rw [sldInverseRoot_trace r hr] at hh
  unfold frobeniusCriterion
  linarith

theorem covariance_frobenius_value (r : Fin 3 → ℝ) (hr : blochNormSq r < 1) :
    (covarianceTarget .frobenius r).trace = (2+mixedRadialGap r)^2 := by
  have he : covarianceTarget .frobenius r = (2+mixedRadialGap r) • sldInverseRoot r := by
    unfold covarianceTarget sldInverseRoot affine
    module
  rw [he,Matrix.trace_smul,sldInverseRoot_trace r hr]
  simp [pow_two]

theorem frobeniusTarget_value (r : Fin 3 → ℝ) (hr : blochNormSq r < 1) :
    frobeniusCriterion (informationTarget .frobenius r) = (2+mixedRadialGap r)^2/2 := by
  rw [frobeniusCriterion,← covariance_eq_information_inv .frobenius r hr,covariance_frobenius_value r hr]
  ring

def designCriterion (loss : Loss) (r : Fin 3 → ℝ) (M : Mat) : ℝ :=
  match loss with
  | .bures => P1.buresDesignCriterion r M
  | .frobenius => frobeniusCriterion M

/-- Both P1 information targets minimize the corresponding local covariance
criterion over all finite single-copy qubit POVMs with nonsingular Fisher information. -/
theorem informationTarget_optimal (loss : Loss) (r : Fin 3 → ℝ) (hr : blochNormSq r < 1)
    {O : Type} [Fintype O] (P : QubitBlochPOVM O) (hP : (qubitClassicalFisher r P).PosDef) :
    designCriterion loss r (informationTarget loss r) ≤ designCriterion loss r (qubitClassicalFisher r P) := by
  cases loss with
  | bures => exact P1.mixedBuresTarget_optimal_over_finite_qubitPOVM r hr P hP
  | frobenius =>
    change frobeniusCriterion (informationTarget .frobenius r) ≤ _
    rw [frobeniusTarget_value r hr]
    exact finite_qubitPOVM_frobenius_lower_bound r hr P hP

end
end QubitOracle.AdaptiveDesign.P1Weighted
