import QubitOracle.AdaptiveDesign.LibraryUnweightedMoments

/-! The optional POVM's unweighted frame is scalar on the true tangent
space, including absence of coupling to all normal Hermitian directions. -/
namespace QubitOracle.AdaptiveDesign.LibraryUnweighted
open QubitOracle QubitOracle.Paper GlobalPFSIC GlobalPFSICHermitian TangentGLS
open FiniteFrameCoercivity
open scoped BigOperators InnerProductSpace Matrix.Norms.Elementwise
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

lemma referenceCoordinate_effect {d : ℕ} (hd : 0 < d) (o : Outcome d) :
    referenceCoordinate d (effectVector hd o) =
      WithLp.toLp 2 (referenceGradient (measurementPOVM d hd) o) := rfl

def diagonalEffect {d : ℕ} (hd : 0 < d) (b : Bool) (v : LibraryIndex d) :
    HermitianSpace (d+1) := effectVector hd (b,0,v)-
      referenceLift d (referenceCoordinate d (effectVector hd (b,0,v)))

lemma effect_decomposition {d : ℕ} (hd : 0 < d) (b : Bool) (s : Fin 4) (v : LibraryIndex d) :
    effectVector hd (b,s,v) = diagonalEffect hd b v+
      referenceLift d (referenceCoordinate d (effectVector hd (b,s,v))) := by
  apply toMatrix_injective
  change effect (b,s,v) = effect (b,0,v)-
    referenceTangentMatrix (referenceCoordinate d (effectVector hd (b,0,v)))+
      referenceTangentMatrix (referenceCoordinate d (effectVector hd (b,s,v)))
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  all_goals
    fin_cases s <;>
    simp [effectVector, ofMatrix, diagonalEffect, referenceLift, referenceLiftLinear, referenceTangentMatrix,
      referenceCoordinate, referenceCoordinateLinear, GeneralPOVM.matrixGradient,
      effect, measurementVector, liftVector, projector_apply, phase4,
      toMatrix, Complex.mul_re, Complex.mul_im, Complex.ext_iff] <;> constructor <;> ring

lemma referenceCoordinate_effect_phase_sum {d : ℕ} (hd : 0 < d) (b : Bool) (v : LibraryIndex d) :
    ∑ s : Fin 4, referenceCoordinate d (effectVector hd (b,s,v)) = 0 := by
  ext x
  simp only [referenceCoordinate_effect, WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_toLp,
    measurementPOVM_referenceGradient, ← Finset.mul_sum, phaseCoordinate_sum, mul_zero,
    PiLp.zero_apply]

lemma reference_gram {d : ℕ} (hd : 0 < d) :
    gramCLM (fun o : Outcome d => referenceCoordinate d (effectVector hd o)) (fun _ => 1) =
      (gramConstant d/2) • (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (TangentIndex d))) := by
  have h := gramCLM_eq_matrix (fun _ : Outcome d => (1:ℝ))
    (fun o => referenceCoordinate d (effectVector hd o))
  simp only [inv_one] at h
  have he : GeneralPOVM.weightedGram (fun _ : Outcome d => (1:ℝ))
      (fun o => (referenceCoordinate d (effectVector hd o)).ofLp) =
        gram (1 : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) := by
    ext x y
    simp only [GeneralPOVM.weightedGram_apply, GeneralPOVM.safeRatio_eq_div, div_one, gram,
      referenceCoordinate_effect, WithLp.ofLp_toLp, transportedGradient, transportedEffect,
      Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
    rfl
  rw [he, gram_at_alignment hd _ (by simp) (by simp [controllerTrueOverlapSq])] at h
  simpa only [map_smul, map_one, ContinuousLinearMap.one_def] using h

theorem referenceFrame_coordinate {d : ℕ} (hd : 0 < d) (A : HermitianSpace (d+1)) :
    referenceCoordinate d (frameOperator (effectVector hd) A) =
      gramConstant d • referenceCoordinate d A := by
  have hdiag : (∑ o : Outcome d,
      ⟪diagonalEffect hd o.1 o.2.2,A⟫_ℝ • referenceCoordinate d (effectVector hd o)) = 0 := by
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_eq_zero
    intro b _
    rw [Finset.sum_comm]
    simp only [← Finset.smul_sum, referenceCoordinate_effect_phase_sum, smul_zero, Finset.sum_const_zero]
  have he (o : Outcome d) : ⟪effectVector hd o,A⟫_ℝ =
      ⟪diagonalEffect hd o.1 o.2.2,A⟫_ℝ+
        2*⟪referenceCoordinate d (effectVector hd o),referenceCoordinate d A⟫_ℝ := by
    conv_lhs => rw [effect_decomposition hd o.1 o.2.1 o.2.2]
    rw [inner_add_left, referenceLift_inner]
  change referenceCoordinate d (∑ o, ⟪effectVector hd o,A⟫_ℝ • effectVector hd o) = _
  rw [map_sum (referenceCoordinate d)]
  simp only [ContinuousLinearMap.map_smul, he, add_smul, map_add,
    Finset.sum_add_distrib, hdiag, zero_add]
  have hh := congrArg (fun L : EuclideanSpace ℝ (TangentIndex d) →L[ℝ]
      EuclideanSpace ℝ (TangentIndex d) => (2:ℝ) • L (referenceCoordinate d A)) (reference_gram hd)
  simpa only [gramCLM_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    Finset.smul_sum, smul_smul, one_mul, mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)] using hh

theorem referenceFrame_projection {d : ℕ} (hd : 0 < d) (A : HermitianSpace (d+1)) :
    tangentProjector (PureMatrixController.knownReference d) (frameOperator (effectVector hd) A) =
      gramConstant d • tangentProjector (PureMatrixController.knownReference d) A := by
  rw [← referenceLift_coordinate, referenceFrame_coordinate, map_smul, referenceLift_coordinate]

end
end QubitOracle.AdaptiveDesign.LibraryUnweighted
