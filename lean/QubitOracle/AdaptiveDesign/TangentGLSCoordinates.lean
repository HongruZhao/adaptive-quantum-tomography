import QubitOracle.AdaptiveDesign.TangentGLSBounds
import QubitOracle.AdaptiveDesign.GeneralPOVMBorn

/-! Fixed, true-frame coordinates for the variance calculation. These maps
are used only in the proof; the estimator itself remains intrinsic. -/

namespace QubitOracle.AdaptiveDesign.TangentGLS

open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController
open scoped BigOperators InnerProductSpace ComplexOrder
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

def referenceCoordinateLinear (d : ℕ) : HermitianSpace (d+1) →ₗ[ℝ] EuclideanSpace ℝ (TangentIndex d) where
  toFun A := WithLp.toLp 2 (GeneralPOVM.matrixGradient (toMatrix A))
  map_add' A B := by
    ext i
    cases i <;> simp [GeneralPOVM.matrixGradient, toMatrix_add] <;> ring
  map_smul' c A := by
    ext i
    cases i <;> simp [GeneralPOVM.matrixGradient, toMatrix_smul, Complex.real_smul]

def referenceCoordinate (d : ℕ) : HermitianSpace (d+1) →L[ℝ] EuclideanSpace ℝ (TangentIndex d) :=
  (referenceCoordinateLinear d).toContinuousLinearMap

def referenceTangentMatrix {d : ℕ} (u : EuclideanSpace ℝ (TangentIndex d)) :
    Matrix (Fin (d+1)) (Fin (d+1)) ℂ :=
  fun i j => Fin.cases (Fin.cases 0 (fun j => (u (.inl j) : ℂ) - Complex.I * u (.inr j)) j)
    (fun i => Fin.cases ((u (.inl i) : ℂ) + Complex.I * u (.inr i)) (fun _ => 0) j) i

theorem referenceTangentMatrix_hermitian {d : ℕ} (u : EuclideanSpace ℝ (TangentIndex d)) :
    (referenceTangentMatrix u).IsHermitian := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [referenceTangentMatrix, Matrix.conjTranspose_apply, star_add, star_sub, star_mul] <;> ring

def referenceLiftLinear (d : ℕ) : EuclideanSpace ℝ (TangentIndex d) →ₗ[ℝ] HermitianSpace (d+1) where
  toFun u := ofMatrix (referenceTangentMatrix u) (referenceTangentMatrix_hermitian u)
  map_add' u v := by
    apply toMatrix_injective
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [referenceTangentMatrix, toMatrix_add, mul_add] <;> ring
  map_smul' c u := by
    apply toMatrix_injective
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [referenceTangentMatrix, toMatrix_smul, Complex.real_smul, mul_add, mul_sub] <;> ring

def referenceLift (d : ℕ) : EuclideanSpace ℝ (TangentIndex d) →L[ℝ] HermitianSpace (d+1) :=
  (referenceLiftLinear d).toContinuousLinearMap

theorem referenceCoordinate_lift (d : ℕ) (u : EuclideanSpace ℝ (TangentIndex d)) :
    referenceCoordinate d (referenceLift d u) = u := by
  ext i
  cases i <;> simp [referenceCoordinate, referenceCoordinateLinear, referenceLift, referenceLiftLinear,
    GeneralPOVM.matrixGradient, referenceTangentMatrix, Complex.mul_re, Complex.mul_im]

theorem referenceLift_coordinate (d : ℕ) (A : HermitianSpace (d+1)) :
    referenceLift d (referenceCoordinate d A) = tangentProjector (knownReference d) A := by
  apply toMatrix_injective
  rw [tangentProjector_apply]
  change referenceTangentMatrix (referenceCoordinate d A) = tangentProjectionMatrix (knownReference d) A
  have hh (j : Fin d) : toMatrix A j.succ 0 = star (toMatrix A 0 j.succ) := by
    exact (congrFun (congrFun (toMatrix_isHermitian A).eq j.succ) 0).symm
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  all_goals simp [referenceTangentMatrix, referenceCoordinate, referenceCoordinateLinear,
    GeneralPOVM.matrixGradient, tangentProjectionMatrix, knownReference, rankOneDensity,
    Matrix.mul_apply, Fin.sum_univ_succ, Pi.single_apply, hh]
  all_goals apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

theorem referenceLift_inner (d : ℕ) (u : EuclideanSpace ℝ (TangentIndex d))
    (A : HermitianSpace (d+1)) :
    ⟪referenceLift d u,A⟫_ℝ = 2 * ⟪u,referenceCoordinate d A⟫_ℝ := by
  have hh (j : Fin d) : toMatrix A j.succ 0 = star (toMatrix A 0 j.succ) := by
    exact (congrFun (congrFun (toMatrix_isHermitian A).eq j.succ) 0).symm
  rw [inner_eq_trace]
  change (Matrix.trace (toMatrix A * referenceTangentMatrix u)).re = _
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, referenceTangentMatrix, Fin.sum_univ_succ,
    hh, Complex.re_sum, Complex.mul_re, Complex.mul_im, PiLp.inner_apply,
    referenceCoordinate, referenceCoordinateLinear, GeneralPOVM.matrixGradient,
    Fintype.sum_sum_type, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.mul_sum, Finset.sum_mul, real_inner_comm]
  ring

def conjugateMatrix {d : ℕ} (U A : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) := U*A*U.conjTranspose

theorem conjugateMatrix_add {d : ℕ} (U A B : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    conjugateMatrix U (A+B) = conjugateMatrix U A + conjugateMatrix U B := by
  simp [conjugateMatrix, Matrix.mul_add, Matrix.add_mul]

theorem conjugateMatrix_sub {d : ℕ} (U A B : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    conjugateMatrix U (A-B) = conjugateMatrix U A - conjugateMatrix U B := by
  simp [conjugateMatrix, Matrix.mul_sub, Matrix.sub_mul]

theorem conjugateMatrix_mul {d : ℕ} (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ) (A B : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    conjugateMatrix U (A*B) = conjugateMatrix U A * conjugateMatrix U B := by
  have hu : U.conjTranspose*U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  unfold conjugateMatrix
  symm
  calc
    _ = U*A*(U.conjTranspose*U)*B*U.conjTranspose := by noncomm_ring
    _ = _ := by rw [hu]; simp [Matrix.mul_assoc]

theorem tangentProjector_transport {d : ℕ} (h g : PureVector d)
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ)
    (hray : conjugateMatrix U (rankOneDensity h.val) = rankOneDensity g.val)
    (A : HermitianSpace (d+1)) :
    conjugationIsometry U hU (tangentProjector h A) =
      tangentProjector g (conjugationIsometry U hU A) := by
  apply toMatrix_injective
  rw [tangentProjector_apply, tangentProjector_apply]
  change conjugateMatrix U (tangentProjectionMatrix h A) =
    tangentProjectionMatrix g (conjugationIsometry U hU A)
  unfold tangentProjectionMatrix
  change conjugateMatrix U (rankOneDensity h.val * toMatrix A + toMatrix A * rankOneDensity h.val -
    (rankOneDensity h.val * toMatrix A * rankOneDensity h.val +
     rankOneDensity h.val * toMatrix A * rankOneDensity h.val)) =
    rankOneDensity g.val * conjugateMatrix U (toMatrix A) +
      conjugateMatrix U (toMatrix A) * rankOneDensity g.val -
      (rankOneDensity g.val * conjugateMatrix U (toMatrix A) * rankOneDensity g.val +
       rankOneDensity g.val * conjugateMatrix U (toMatrix A) * rankOneDensity g.val)
  simp only [conjugateMatrix_add, conjugateMatrix_sub, conjugateMatrix_mul U hU, hray]

theorem trueFrame_reference_ray {d : ℕ} (truth : PureVector d) :
    conjugateMatrix (P2Adaptive.trueFrame d truth) (rankOneDensity (knownReference d).val) =
      rankOneDensity truth.val := by
  have h0 : GlobalPFSIC.frameProjector (1 : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) =
      rankOneDensity (knownReference d).val := by
    ext i j
    simp [GlobalPFSIC.frameProjector, GlobalPFSIC.projector, knownReference,
      rankOneDensity, Pi.single_apply, Matrix.vecMulVec, Matrix.one_apply]
  have h := GlobalPFSIC.frameProjector_mul (P2Adaptive.trueFrame d truth) (1 : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
  rw [Matrix.mul_one, P2Adaptive.trueFrame_projector, h0] at h
  exact h.symm

def trueCoordinate {d : ℕ} (truth : PureVector d) :
    HermitianSpace (d+1) →L[ℝ] EuclideanSpace ℝ (TangentIndex d) :=
  (referenceCoordinate d).comp
    (conjugationIsometry (P2Adaptive.trueFrame d truth) (P2Adaptive.trueFrame_unitary d truth)).symm.toContinuousLinearMap

def trueLift {d : ℕ} (truth : PureVector d) :
    EuclideanSpace ℝ (TangentIndex d) →L[ℝ] HermitianSpace (d+1) :=
  (conjugationIsometry (P2Adaptive.trueFrame d truth) (P2Adaptive.trueFrame_unitary d truth)).toContinuousLinearMap.comp
    (referenceLift d)

theorem trueCoordinate_lift {d : ℕ} (truth : PureVector d) (u : EuclideanSpace ℝ (TangentIndex d)) :
    trueCoordinate truth (trueLift truth u) = u := by
  let U := conjugationIsometry (P2Adaptive.trueFrame d truth) (P2Adaptive.trueFrame_unitary d truth)
  change referenceCoordinate d (U.symm (U (referenceLift d u))) = u
  rw [U.symm_apply_apply, referenceCoordinate_lift]

theorem trueLift_coordinate {d : ℕ} (truth : PureVector d) (A : HermitianSpace (d+1)) :
    trueLift truth (trueCoordinate truth A) = tangentProjector truth A := by
  let U := conjugationIsometry (P2Adaptive.trueFrame d truth) (P2Adaptive.trueFrame_unitary d truth)
  change U (referenceLift d (referenceCoordinate d (U.symm A))) = _
  rw [referenceLift_coordinate]
  exact (tangentProjector_transport (knownReference d) truth _ _ (trueFrame_reference_ray truth)
    (U.symm A)).trans (by rw [U.apply_symm_apply])

theorem trueLift_inner {d : ℕ} (truth : PureVector d) (u : EuclideanSpace ℝ (TangentIndex d))
    (A : HermitianSpace (d+1)) :
    ⟪trueLift truth u,A⟫_ℝ = 2*⟪u,trueCoordinate truth A⟫_ℝ := by
  change ⟪conjugationIsometry (P2Adaptive.trueFrame d truth) (P2Adaptive.trueFrame_unitary d truth)
    (referenceLift d u),A⟫_ℝ = _
  rw [FiniteFrameCoercivity.transported_measurement, referenceLift_inner]
  rfl

theorem trueCoordinate_projection {d : ℕ} (truth : PureVector d) (A : HermitianSpace (d+1)) :
    trueCoordinate truth (tangentProjector truth A) = trueCoordinate truth A := by
  rw [← trueLift_coordinate, trueCoordinate_lift]

theorem trueCoordinate_responseVector {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (truth : PureVector d) (U : GlobalPFSICBorn.Action d) (y : O) :
    trueCoordinate truth (GeneralPOVM.responseVector P U y) = WithLp.toLp 2
      (GeneralPOVM.gradient P ((P2Adaptive.trueFrame d truth).conjTranspose * U.matrix) y) := by
  have heq : toMatrix ((conjugationIsometry (P2Adaptive.trueFrame d truth)
      (P2Adaptive.trueFrame_unitary d truth)).symm (GeneralPOVM.responseVector P U y)) =
    GeneralPOVM.effect P ((P2Adaptive.trueFrame d truth).conjTranspose * U.matrix) y := by
    change (P2Adaptive.trueFrame d truth).conjTranspose * (GeneralPOVM.effect P U.matrix y) *
      (P2Adaptive.trueFrame d truth).conjTranspose.conjTranspose = _
    rw [Matrix.conjTranspose_conjTranspose, GeneralPOVM.effect_relativeFrame]
  change WithLp.toLp 2 (GeneralPOVM.matrixGradient (toMatrix
    ((conjugationIsometry (P2Adaptive.trueFrame d truth) (P2Adaptive.trueFrame_unitary d truth)).symm
      (GeneralPOVM.responseVector P U y)))) = _
  rw [heq]
  rfl

end
end QubitOracle.AdaptiveDesign.TangentGLS
