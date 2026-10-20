import QubitOracle.AdaptiveDesign.SharpTangentGeometry
import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel
import QubitOracle.AdaptiveDesign.GlobalPFSICLibrary
import QubitOracle.AdaptiveDesign.NearestPureEigenvector
import QubitOracle.AdaptiveDesign.P2AdaptiveTheorem
import QubitOracle.AdaptiveDesign.PureMatrixController
import QubitOracle.AdaptiveDesign.TangentGLSBounds
import QubitOracle.AdaptiveDesign.TangentGLSGeometry
import QubitOracle.AdaptiveDesign.TangentGLSProjection
import QubitOracle.AdaptiveDesign.TangentGLSWeightExpansion
import QubitOracle.Paper.PureStateFoundations
/-! A global quadratic first-order expansion of the actual nearest pure
projector. Commutation of the fitted spectral projector replaces a
local choice of eigenvector and an unproved spectral perturbation input. -/
namespace QubitOracle.AdaptiveDesign.PureMatrixController
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian P2Adaptive TangentGLS
open scoped BigOperators InnerProductSpace ComplexOrder Matrix.Norms.Frobenius
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem nearestProjector_commutes {d : ℕ} (A : HermitianSpace (d+1)) :
    toMatrix A * projectedMatrix d (toMatrix A) = projectedMatrix d (toMatrix A) * toMatrix A := by
  let h := nearestVector d (toMatrix A)
  let r : ℝ := ⨆ v : {v : EuclideanSpace ℂ (Fin (d+1)) // v ≠ 0},
    (hermitianOperator A).rayleighQuotient v.val
  have he : (toMatrix A).mulVec h.val = (r:ℂ) • h.val := by
    have hh := (nearestVector_leadingEigenvector A).apply_eq_smul
    exact congrArg WithLp.ofLp hh
  have hleft : toMatrix A * rankOneDensity h.val = (r:ℂ) • rankOneDensity h.val := by
    ext i j
    change (∑ k, toMatrix A i k*(h.val k*star (h.val j))) =
      (r:ℂ)*(h.val i*star (h.val j))
    calc
      _ = ((toMatrix A).mulVec h.val i)*star (h.val j) := by
        simp only [Matrix.mulVec,dotProduct,Finset.sum_mul,mul_assoc]
      _ = _ := by rw [he]; simp only [Pi.smul_apply,smul_eq_mul,mul_assoc]
  have hright := congrArg Matrix.conjTranspose hleft
  have hHerm : (rankOneDensity h.val).conjTranspose=rankOneDensity h.val :=
    (GlobalPFSIC.projector_posSemidef h.val).isHermitian.eq
  simp only [Matrix.conjTranspose_mul,hHerm,
    (toMatrix_isHermitian A).eq,Matrix.conjTranspose_smul,Complex.star_def,
    Complex.conj_ofReal] at hright
  exact hleft.trans hright.symm

def matrixCommutator {d : ℕ} (A B : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) := A*B-B*A

theorem matrixCommutator_norm_le {d : ℕ} (A B : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    ‖matrixCommutator A B‖ ≤ 2*‖A‖*‖B‖ := by
  have hh := norm_sub_le (A*B) (B*A)
  have h1 := Matrix.frobenius_norm_mul A B
  have h2 := Matrix.frobenius_norm_mul B A
  dsimp only [matrixCommutator]
  nlinarith

theorem tangentProjector_doubleCommutator {d : ℕ} (truth : PureVector d)
    (B : HermitianSpace (d+1)) :
    toMatrix (tangentProjector truth B) =
      matrixCommutator (rankOneDensity truth.val)
        (matrixCommutator (rankOneDensity truth.val) (toMatrix B)) := by
  rw [tangentProjector_apply]
  change tangentProjectionMatrix truth B = _
  unfold tangentProjectionMatrix matrixCommutator
  have hp := pureProjector_idempotent truth
  simp only [Matrix.mul_sub,Matrix.sub_mul,← Matrix.mul_assoc,hp]
  noncomm_ring [hp]

theorem nearestProjector_tangent_remainder {d : ℕ} (truth : PureVector d)
    (A : HermitianSpace (d+1)) :
    ‖tangentProjector truth ((pureParameter d (nearestVector d (toMatrix A))).val-
      (pureParameter d truth).val-(A-(pureParameter d truth).val))‖ ≤
      8*‖A-(pureParameter d truth).val‖^2 := by
  let P := rankOneDensity truth.val
  let R := projectedMatrix d (toMatrix A)
  let E := toMatrix A-P
  have hc : matrixCommutator (toMatrix A) R=0 := by
    rw [matrixCommutator,nearestProjector_commutes,sub_self]
  have he : matrixCommutator P (matrixCommutator P (R-P-E)) =
      -matrixCommutator P (matrixCommutator E (R-P)) := by
    dsimp only [matrixCommutator,E] at hc ⊢
    have hh : (toMatrix A)*R = R*(toMatrix A) := sub_eq_zero.mp hc
    noncomm_ring [hh]
  have hp : ‖P‖=1 := pureProjector_norm truth
  have hR : ‖R-P‖ ≤ 2*‖E‖ := projectedMatrix_error_le_two d truth (toMatrix A)
  rw [← toMatrix_norm,tangentProjector_doubleCommutator]
  change ‖matrixCommutator P (matrixCommutator P (R-P-E))‖ ≤ _
  rw [he,norm_neg]
  have h1 := matrixCommutator_norm_le P (matrixCommutator E (R-P))
  have h2 := matrixCommutator_norm_le E (R-P)
  rw [hp] at h1
  have h3 := mul_le_mul_of_nonneg_left hR (show 0 ≤ 2*‖E‖ by positivity)
  have hnorm : ‖E‖=‖A-(pureParameter d truth).val‖ := toMatrix_norm (A-(pureParameter d truth).val)
  rw [← hnorm]
  nlinarith

theorem nearestProjector_expansion {d : ℕ} (truth : PureVector d)
    (A : HermitianSpace (d+1)) :
    ‖(pureParameter d (nearestVector d (toMatrix A))).val-(pureParameter d truth).val-
      tangentProjector truth (A-(pureParameter d truth).val)‖ ≤
      20*‖A-(pureParameter d truth).val‖^2 := by
  let R := (pureParameter d (nearestVector d (toMatrix A))).val
  let P := (pureParameter d truth).val
  have ht := nearestProjector_tangent_remainder truth A
  have hn := preliminaryError_normal_bound truth (nearestVector d (toMatrix A))
  have hdist : ‖R-P‖ ≤ 2*‖A-P‖ := by
    rw [← toMatrix_norm (R-P),← toMatrix_norm (A-P)]
    exact projectedMatrix_error_le_two d truth (toMatrix A)
  have hn' : ‖R-P-tangentProjector truth (R-P)‖ ≤ 3*‖R-P‖^2 := by
    have hneg : P-R=-(R-P) := by abel
    change ‖P-R-tangentProjector truth (P-R)‖ ≤ 3*‖P-R‖^2 at hn
    rw [hneg,map_neg,show -(R-P)- -(tangentProjector truth (R-P)) =
      -(R-P-tangentProjector truth (R-P)) by abel,norm_neg,norm_neg] at hn
    exact hn
  have he : R-P-tangentProjector truth (A-P) =
      (R-P-tangentProjector truth (R-P))+tangentProjector truth (R-P-(A-P)) := by
    simp only [map_sub]; abel
  change ‖R-P-tangentProjector truth (A-P)‖ ≤ _
  rw [he]
  have hb := norm_add_le (R-P-tangentProjector truth (R-P))
    (tangentProjector truth (R-P-(A-P)))
  nlinarith [norm_nonneg (R-P),norm_nonneg (A-P)]

end
end QubitOracle.AdaptiveDesign.PureMatrixController
