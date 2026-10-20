import QubitOracle.AdaptiveDesign.ProjectiveStateManifold
import QubitOracle.AdaptiveDesign.PureTangentCurves
import QubitOracle.AdaptiveDesign.PureTangentDimension

set_option autoImplicit false

/-! Definition A.4 with the manuscript's Fubini--Study normalization.
The other geometry definitions use the actual projective quotient,
induced matrix topology, smooth charts, matrix tangent space and
normalization retraction imported above. -/
namespace QubitOracle.Paper.MainPaperGeometry
open QubitOracle QubitOracle.Paper QubitOracle.AdaptiveDesign
open GlobalPFSICHermitian PureMatrixController P2Adaptive TangentGLS
open Filter
open scoped InnerProductSpace Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

/-- A velocity of a locally defined pure-state curve satisfies the
matrix tangent equation. The projector identity is required only near
zero, matching the local curve definition in Appendix A.3. -/
theorem local_projector_curve_velocity {d : ℕ} (h : PureVector d)
    (gamma : ℝ → HermitianSpace (d+1)) (A : HermitianSpace (d+1))
    (hzero : gamma 0 = (pureParameter d h).val)
    (hprojector : ∀ᶠ s in 𝓝 (0 : ℝ),
      toMatrix (gamma s) * toMatrix (gamma s) = toMatrix (gamma s))
    (hderiv : HasDerivAt gamma A 0) : A ∈ tangentSpace h := by
  apply (tangentSpace_mem h A).mpr
  ext i j
  let L (i j : Fin (d+1)) : HermitianSpace (d+1) →L[ℝ] ℂ :=
    (ContinuousLinearMap.proj j).comp ((ContinuousLinearMap.proj i).comp
      (toMatrixLinear (d+1)).toContinuousLinearMap)
  have hd (i j : Fin (d+1)) :
      HasDerivAt (fun s => toMatrix (gamma s) i j) (toMatrix A i j) 0 :=
    (L i j).hasFDerivAt.comp_hasDerivAt 0 hderiv
  have hm := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => (hd i k).mul (hd k j))
  have he : (fun s => ∑ k, toMatrix (gamma s) i k * toMatrix (gamma s) k j) =ᶠ[𝓝 (0 : ℝ)]
      (fun s => toMatrix (gamma s) i j) := by
    filter_upwards [hprojector] with s hs
    exact congrArg (fun M : Matrix (Fin (d+1)) (Fin (d+1)) ℂ => M i j) hs
  have ht := (hm.congr_of_eventuallyEq he.symm).unique (hd i j)
  rw [hzero] at ht
  simp only [Finset.sum_add_distrib] at ht
  change (∑ x, toMatrix A i x * rankOneDensity h.val x j) +
    (∑ x, rankOneDensity h.val i x * toMatrix A x j) = toMatrix A i j at ht
  simpa only [Pi.mul_apply, Matrix.add_apply, Matrix.mul_apply,
    Finset.sum_add_distrib, add_comm] using ht

/-- The restriction of one half of the ambient Frobenius pairing to the
real tangent space. This is a continuous real bilinear form. -/
def fubiniStudy {d : ℕ} (h : PureVector d) :
    tangentSpace h →L[ℝ] tangentSpace h →L[ℝ] ℝ :=
  (1/2 : ℝ) • innerSL ℝ

theorem fubiniStudy_apply {d : ℕ} (h : PureVector d) (A B : tangentSpace h) :
    fubiniStudy h A B = (1/2 : ℝ) * ⟪A.val, B.val⟫_ℝ := rfl

theorem fubiniStudy_symmetric {d : ℕ} (h : PureVector d) (A B : tangentSpace h) :
    fubiniStudy h A B = fubiniStudy h B A := by
  rw [fubiniStudy_apply, fubiniStudy_apply, real_inner_comm]

theorem fubiniStudy_positive {d : ℕ} (h : PureVector d) (A : tangentSpace h) (hA : A ≠ 0) :
    0 < fubiniStudy h A A := by
  change 0 < (1/2 : ℝ) * ⟪A, A⟫_ℝ
  exact mul_pos (by norm_num) (real_inner_self_pos.mpr hA)

theorem quantumInformation_eq_four_fubiniStudy {d : ℕ} (h : PureVector d)
    (A B : tangentSpace h) :
    PureSLDMetric.metricFromSLD h A B = 4 * fubiniStudy h A B := by
  rw [PureSLDMetric.metricFromSLD_eq, fubiniStudy_apply]
  ring

/-- The metric coefficients are smooth in every smooth inverse chart
with open coordinate domain. Together with positivity above, this gives
the Riemannian smoothness assertion in Definition A.4. -/
theorem fubiniStudy_coordinate_smooth {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → HermitianSpace (d+1)) (U : Set E) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (u v : E) :
    ContDiffOn ℝ ∞ (fun theta => (1/2 : ℝ) *
      ⟪fderiv ℝ f theta u, fderiv ℝ f theta v⟫_ℝ) U := by
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  have hu : ContDiffOn ℝ ∞ (fun theta => fderiv ℝ f theta u) U :=
    hd.clm_apply contDiffOn_const
  have hv : ContDiffOn ℝ ∞ (fun theta => fderiv ℝ f theta v) U :=
    hd.clm_apply contDiffOn_const
  exact contDiffOn_const.mul (hu.inner ℝ hv)

theorem tangentVector_add {d : ℕ} (h : PureVector d) (A B : tangentSpace h) :
    tangentVector h (A+B) = tangentVector h A + tangentVector h B := by
  ext i
  change ((toMatrix (A.val+B.val)).mulVec h.val) i =
    ((toMatrix A.val).mulVec h.val) i + ((toMatrix B.val).mulVec h.val) i
  simp only [toMatrix_add, Matrix.add_mulVec, Pi.add_apply]

theorem tangent_inner_horizontal {d : ℕ} (h : PureVector d) (A B : tangentSpace h) :
    ⟪A.val, B.val⟫_ℝ = 2 * ⟪tangentVector h A, tangentVector h B⟫_ℝ := by
  have hab := tangent_norm_sq h (A+B)
  rw [tangentVector_add, norm_add_sq_real, norm_add_sq_real] at hab
  have ha := tangent_norm_sq h A
  have hb := tangent_norm_sq h B
  change ⟪A, B⟫_ℝ = _
  nlinarith

theorem fubiniStudy_horizontal {d : ℕ} (h : PureVector d) (A B : tangentSpace h) :
    fubiniStudy h A B = ⟪tangentVector h A, tangentVector h B⟫_ℝ := by
  rw [fubiniStudy_apply, tangent_inner_horizontal]
  ring

theorem fubiniStudy_horizontal_complex {d : ℕ} (h : PureVector d) (A B : tangentSpace h) :
    fubiniStudy h A B = (⟪tangentVector h A, tangentVector h B⟫_ℂ).re := by
  rw [fubiniStudy_horizontal]
  simp only [PiLp.inner_apply, Complex.re_sum, real_inner_eq_re_inner (𝕜 := ℂ)]
  rfl

/-- Definition A.6 is smooth in the entire tangent increment, not merely
along a particular scalar curve. Its denominator is everywhere positive. -/
theorem normalization_retraction_smooth {d : ℕ} (h : PureVector d) :
    ContDiff ℝ ∞ (updatedState h) := by
  let L : tangentSpace h →L[ℝ] Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
    (toMatrixLinear (d+1)).toContinuousLinearMap.comp (tangentSpace h).subtypeL
  have hl : ContDiff ℝ ∞ L := L.contDiff
  have hnorm : ContDiff ℝ ∞ (fun A : tangentSpace h => ⟪A,A⟫_ℝ) :=
    contDiff_id.inner ℝ contDiff_id
  have hd : ContDiff ℝ ∞ (fun A : tangentSpace h => 1+‖A‖^2/2) := by
    simpa only [real_inner_self_eq_norm_sq] using (contDiff_const.add (hnorm.div_const 2))
  have hi := hd.inv (fun A => ne_of_gt (by positivity : 0 < 1+‖A‖^2/2))
  have hn : ContDiff ℝ ∞ (fun A : tangentSpace h =>
      rankOneDensity h.val+L A+L A*rankOneDensity h.val*L A) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    simp only [Matrix.add_apply, Matrix.mul_apply]
    fun_prop
  convert hi.smul hn using 1
  funext A
  exact updatedState_intrinsic h A

/-- A smooth ambient extension of the retraction on the tangent bundle.
On the bundle it equals `updatedState`; it also varies smoothly with the
base projector, as required by the joint definition of a retraction. -/
def ambientRetraction {d : ℕ}
    (x : HermitianSpace (d+1) × HermitianSpace (d+1)) :
    Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  (1+‖x.2‖^2/2)⁻¹ •
    (toMatrix x.1+toMatrix x.2+toMatrix x.2*toMatrix x.1*toMatrix x.2)

theorem normalization_retraction_joint_smooth {d : ℕ} :
    ContDiff ℝ ∞ (@ambientRetraction d) := by
  let L : HermitianSpace (d+1) →L[ℝ] Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
    (toMatrixLinear (d+1)).toContinuousLinearMap
  have hP : ContDiff ℝ ∞ (fun x : HermitianSpace (d+1) × HermitianSpace (d+1) =>
      L x.1) := L.contDiff.comp contDiff_fst
  have hA : ContDiff ℝ ∞ (fun x : HermitianSpace (d+1) × HermitianSpace (d+1) =>
      L x.2) := L.contDiff.comp contDiff_snd
  have hnorm : ContDiff ℝ ∞
      (fun x : HermitianSpace (d+1) × HermitianSpace (d+1) => ⟪x.2,x.2⟫_ℝ) :=
    contDiff_snd.inner ℝ contDiff_snd
  have hd : ContDiff ℝ ∞
      (fun x : HermitianSpace (d+1) × HermitianSpace (d+1) => 1+‖x.2‖^2/2) := by
    simpa only [real_inner_self_eq_norm_sq] using contDiff_const.add (hnorm.div_const 2)
  have hi := hd.inv (fun x => ne_of_gt (by positivity : 0 < 1+‖x.2‖^2/2))
  have hn : ContDiff ℝ ∞
      (fun x : HermitianSpace (d+1) × HermitianSpace (d+1) =>
        L x.1+L x.2+L x.2*L x.1*L x.2) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    simp only [Matrix.add_apply, Matrix.mul_apply]
    fun_prop
  exact hi.smul hn

theorem ambientRetraction_tangent {d : ℕ} (h : PureVector d) (A : tangentSpace h) :
    ambientRetraction ((pureParameter d h).val, A.val) = updatedState h A := by
  exact (updatedState_intrinsic h A).symm

/-- The full derivative at zero is the tangent inclusion, giving the
identity on tangent matrices in Definition A.6. -/
theorem normalization_retraction_derivative {d : ℕ} (h : PureVector d) :
    HasFDerivAt (updatedState h)
      ((toMatrixLinear (d+1)).toContinuousLinearMap.comp (tangentSpace h).subtypeL) 0 := by
  have hd := (normalization_retraction_smooth h).differentiable (by norm_num) 0
  have he : fderiv ℝ (updatedState h) 0 =
      (toMatrixLinear (d+1)).toContinuousLinearMap.comp (tangentSpace h).subtypeL := by
    apply ContinuousLinearMap.ext
    intro A
    have hf : HasFDerivAt (updatedState h) (fderiv ℝ (updatedState h) 0) ((0:ℝ) • A) := by
      simpa only [zero_smul] using hd.hasFDerivAt
    have hc := hf.comp_hasDerivAt 0
      ((hasDerivAt_id (0:ℝ)).smul_const A)
    have hh : (fun s : ℝ => updatedState h (s • A)) = PureTangentCurves.curve h A := by
      funext s
      exact (PureTangentCurves.curve_is_update h A s).symm
    have hc' : HasDerivAt (fun s : ℝ => updatedState h (s • A))
        ((fderiv ℝ (updatedState h) 0) A) 0 := by
      simpa only [Function.comp_def, id_eq, one_smul] using hc
    rw [hh] at hc'
    exact hc'.unique (PureTangentCurves.curve_hasDerivAt_zero h A)
  rw [← he]
  exact hd.hasFDerivAt

end
end QubitOracle.Paper.MainPaperGeometry
