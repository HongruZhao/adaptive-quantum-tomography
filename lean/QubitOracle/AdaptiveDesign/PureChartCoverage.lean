import QubitOracle.AdaptiveDesign.GeneralPOVMBorn
import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel
import QubitOracle.AdaptiveDesign.GlobalPFSICLibrary
import QubitOracle.AdaptiveDesign.GlobalPFSICTransport
import QubitOracle.AdaptiveDesign.P2AdaptiveTheorem
import QubitOracle.AdaptiveDesign.P2BornFisherIdentification
import QubitOracle.AdaptiveDesign.PureAmplitudeChart
import QubitOracle.AdaptiveDesign.PureAmplitudeLoss
import QubitOracle.AdaptiveDesign.PureMatrixController
import QubitOracle.AdaptiveDesign.TangentGLSCoordinates
import QubitOracle.AdaptiveDesign.TangentGLSGeometry
import QubitOracle.Paper.PureStateFoundations
import QubitOracle.RankOneLosses
import QubitOracle.TwoBasis
/-! The amplitude chart covers exactly the pure rays with nonzero overlap
with its centre. In particular, the inverse used by the statistical
endpoints is a genuine local coordinate map in both directions. -/
namespace QubitOracle.AdaptiveDesign.TangentGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive
open scoped BigOperators InnerProductSpace ComplexOrder
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

theorem projector_column_identity {d : ℕ} (h : Fin (d+1) → ℂ) (i j : Fin (d+1)) :
    GlobalPFSIC.projector h i j * GlobalPFSIC.projector h 0 0 =
      GlobalPFSIC.projector h i 0 * GlobalPFSIC.projector h 0 j := by
  simp only [GlobalPFSIC.projector_apply]
  ring

theorem hermitian_diagonal_real {d : ℕ} (A : HermitianSpace (d+1)) (i : Fin (d+1)) :
    ((toMatrix A i i).re : ℂ) = toMatrix A i i := by
  have hh := congrArg Complex.im (congrFun (congrFun (toMatrix_isHermitian A).eq i) i)
  apply Complex.ext
  · simp
  · simp only [Matrix.conjTranspose_apply,Complex.star_def,Complex.conj_im] at hh
    simp only [Complex.ofReal_im]
    linarith

theorem referenceChart_reconstruction {d : ℕ} (A : HermitianSpace (d+1))
    (hA : toMatrix A * toMatrix A = toMatrix A)
    (hrank : ∀ i j, toMatrix A i j * toMatrix A 0 0 = toMatrix A i 0 * toMatrix A 0 j)
    (hp : 0 < (toMatrix A 0 0).re) :
    referenceChartMatrix ((Real.sqrt (toMatrix A 0 0).re)⁻¹ • ((2:ℝ) • referenceCoordinate d A)) = A := by
  let p := (toMatrix A 0 0).re
  let s := Real.sqrt p
  let u := s⁻¹ • ((2:ℝ) • referenceCoordinate d A)
  have hs : 0 < s := Real.sqrt_pos.mpr hp
  have hs2 : s^2 = p := Real.sq_sqrt hp.le
  have hn : tangentRadiusSq u = 4*(1-p) := by
    rw [show tangentRadiusSq u = ‖u‖^2 by
      rw [EuclideanSpace.real_norm_sq_eq]; rfl]
    dsimp only [u]
    rw [norm_smul,norm_smul,mul_pow,mul_pow,Real.norm_eq_abs,Real.norm_eq_abs,
      sq_abs,sq_abs,inv_pow,hs2,referenceCoordinate_norm_sq A hA]
    dsimp only [p]
    field_simp [hp.ne']
    ring
  have hhead : Real.sqrt (1-tangentRadiusSq u/4)=s := by
    rw [hn]
    congr 1
    ring
  have hcol : ∀ i, toMatrix (referenceChartMatrix u) i 0 = toMatrix A i 0 := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change (Real.sqrt (1-tangentRadiusSq u/4) : ℂ) * star (Real.sqrt (1-tangentRadiusSq u/4) : ℂ) = _
      rw [hhead]
      rw [Complex.star_def,Complex.conj_ofReal,← pow_two,← Complex.ofReal_pow,hs2]
      exact hermitian_diagonal_real A 0
    · have hh : toMatrix A j.succ 0 = star (toMatrix A 0 j.succ) :=
        (congrFun (congrFun (toMatrix_isHermitian A).eq j.succ) 0).symm
      change (chartState u j.succ)*star (chartState u 0) = _
      simp only [chartState,Fin.cases_zero,Fin.cases_succ,hhead,Complex.star_def,Complex.conj_ofReal]
      rw [hh]
      apply Complex.ext <;>
        simp [u,referenceCoordinate,referenceCoordinateLinear,GeneralPOVM.matrixGradient,
          Complex.mul_re,Complex.mul_im,Complex.star_def] <;> field_simp [hs.ne'] <;> ring
  have hrow : ∀ j, toMatrix (referenceChartMatrix u) 0 j = toMatrix A 0 j := by
    intro j
    have hB := congrFun (congrFun (toMatrix_isHermitian (referenceChartMatrix u)).eq 0) j
    have hC := congrFun (congrFun (toMatrix_isHermitian A).eq 0) j
    simp only [Matrix.conjTranspose_apply,hcol] at hB hC
    exact hB.symm.trans hC
  apply toMatrix_injective
  ext i j
  apply mul_right_cancel₀ (show toMatrix A 0 0 ≠ 0 by
    rw [← hermitian_diagonal_real A 0]; exact_mod_cast hp.ne')
  calc
    _ = toMatrix (referenceChartMatrix u) i j * toMatrix (referenceChartMatrix u) 0 0 := by rw [hcol]
    _ = toMatrix (referenceChartMatrix u) i 0 * toMatrix (referenceChartMatrix u) 0 j :=
      projector_column_identity (chartState u) i j
    _ = _ := by rw [hcol,hrow,hrank]

theorem chart_amplitudeCoordinates {d : ℕ} (truth h : PureVector d)
    (hp : 0 < ⟪(pureParameter d truth).val,(pureParameter d h).val⟫_ℝ) :
    trueChartMatrix truth (amplitudeCoordinates truth (pureParameter d h).val) =
      (pureParameter d h).val := by
  let U := conjugationIsometry (trueFrame d truth) (trueFrame_unitary d truth)
  let A := U.symm (pureParameter d h).val
  let v := (trueFrame d truth).conjTranspose.mulVec h.val
  have hmat : toMatrix A = GlobalPFSIC.projector v := by
    change (trueFrame d truth).conjTranspose * GlobalPFSIC.projector h.val *
      (trueFrame d truth).conjTranspose.conjTranspose = _
    exact (GlobalPFSIC.projector_mulVec _ _).symm
  have hv : pureStateNormSq v = 1 := by
    change pureStateNormSq ((trueFrame d truth).conjTranspose.mulVec h.val) = 1
    have hU : (trueFrame d truth).conjTranspose ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ := by
      apply Matrix.mem_unitaryGroup_iff'.mpr
      change (trueFrame d truth).conjTranspose.conjTranspose * (trueFrame d truth).conjTranspose = 1
      rw [Matrix.conjTranspose_conjTranspose]
      exact Matrix.mem_unitaryGroup_iff.mp (trueFrame_unitary d truth)
    rw [pureStateNormSq_unitary_mulVec _ hU]
    exact h.property
  have hA : toMatrix A * toMatrix A = toMatrix A := by
    rw [hmat]
    exact pureProjector_idempotent (⟨v,hv⟩ : PureVector d)
  have hrank : ∀ i j, toMatrix A i j * toMatrix A 0 0 = toMatrix A i 0 * toMatrix A 0 j := by
    simp only [hmat]
    exact projector_column_identity v
  have hP : (pureParameter d truth).val = U (pureParameter d (knownReference d)).val :=
    (trueFrame_referenceParameter truth).symm
  have hov : ⟪(pureParameter d truth).val,(pureParameter d h).val⟫_ℝ = (toMatrix A 0 0).re := by
    calc
      _ = ⟪U (pureParameter d (knownReference d)).val,U A⟫_ℝ := by
        rw [← hP]; dsimp only [A]; rw [U.apply_symm_apply]
      _ = _ := by rw [U.inner_map_map,reference_overlap]
  have hc : trueCoordinate truth ((pureParameter d h).val-(pureParameter d truth).val) =
      referenceCoordinate d A := by
    change referenceCoordinate d (U.symm ((pureParameter d h).val-(pureParameter d truth).val)) = _
    rw [hP,map_sub,U.symm_apply_apply,map_sub,referenceCoordinate_reference,sub_zero]
  change U (referenceChartMatrix (amplitudeCoordinates truth (pureParameter d h).val)) = _
  rw [amplitudeCoordinates,hov,hc,referenceChart_reconstruction A hA hrank (hov ▸ hp)]
  exact U.apply_symm_apply _

theorem amplitudeCoordinates_in_domain {d : ℕ} (truth h : PureVector d)
    (hp : 0 < ⟪(pureParameter d truth).val,(pureParameter d h).val⟫_ℝ) :
    tangentRadiusSq (amplitudeCoordinates truth (pureParameter d h).val) < 4 := by
  rw [show tangentRadiusSq (amplitudeCoordinates truth (pureParameter d h).val) =
      ‖amplitudeCoordinates truth (pureParameter d h).val‖^2 by
    rw [EuclideanSpace.real_norm_sq_eq]; rfl,
    amplitudeCoordinates_norm_sq truth h hp]
  linarith

end
end QubitOracle.AdaptiveDesign.TangentGLS
