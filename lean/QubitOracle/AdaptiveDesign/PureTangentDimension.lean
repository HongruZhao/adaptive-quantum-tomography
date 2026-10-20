import QubitOracle.AdaptiveDesign.GeneralPOVMModel
import QubitOracle.AdaptiveDesign.GlobalPFSICBornModel
import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel
import QubitOracle.AdaptiveDesign.IntrinsicInformationGeometry
import QubitOracle.AdaptiveDesign.P2AdaptiveTheorem
import QubitOracle.AdaptiveDesign.PureMatrixController
import QubitOracle.AdaptiveDesign.PureSLDMetric
import QubitOracle.AdaptiveDesign.SharpTangentGeometry
import QubitOracle.AdaptiveDesign.TangentGLSBounds
import QubitOracle.AdaptiveDesign.TangentGLSCoordinates
import QubitOracle.AdaptiveDesign.TangentGLSGeometry
import QubitOracle.AdaptiveDesign.TangentGLSRetraction
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.PureStateFoundations
import QubitOracle.TwoBasis
/-! Concrete tangent dimension and simultaneous rotation invariance.
The coordinate equivalence is constructed, not supplied as a dimension
or manifold assumption. -/
namespace QubitOracle.AdaptiveDesign.TangentGLS
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive
open scoped BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

def tangentCoordinateEquiv {d : ℕ} (h : PureVector d) :
    tangentSpace h ≃ₗ[ℝ] EuclideanSpace ℝ (TangentIndex d) where
  toFun A := trueCoordinate h A.val
  invFun u := ⟨trueLift h u,PureSLDMetric.trueLift_mem h u⟩
  left_inv A := by
    apply Subtype.ext
    change trueLift h (trueCoordinate h A.val)=A.val
    rw [trueLift_coordinate]
    exact Submodule.starProjection_eq_self_iff.mpr A.property
  right_inv u := trueCoordinate_lift h u
  map_add' A B := map_add (trueCoordinate h) A.val B.val
  map_smul' c A := map_smul (trueCoordinate h) c A.val

theorem tangent_finrank {d : ℕ} (h : PureVector d) :
    Module.finrank ℝ (tangentSpace h)=2*d := by
  rw [(tangentCoordinateEquiv h).finrank_eq]
  simp [TangentIndex,Fintype.card_sum]
  omega

def measurementFisher {E O : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fintype O] (features : O → E) (state A B : E) : ℝ :=
  ∑ y, (⟪features y,A⟫_ℝ * ⟪features y,B⟫_ℝ) / ⟪features y,state⟫_ℝ

theorem measurementFisher_isometry {E F O : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [Fintype O]
    (U : E ≃ₗᵢ[ℝ] F) (features : O → E) (state A B : E) :
    measurementFisher (fun y => U (features y)) (U state) (U A) (U B)=
      measurementFisher features state A B := by
  simp only [measurementFisher,U.inner_map_map]

theorem measurementFisher_actual {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (truth : PureVector d) (U : GlobalPFSICBorn.Action d)
    (A B : HermitianSpace (d+1)) :
    measurementFisher (GeneralPOVM.responseVector P U) (pureParameter d truth).val A B=
      IntrinsicInformationGeometry.fisherForm P truth U A B := rfl

theorem pure_metric_isometry {d : ℕ} (U : HermitianSpace (d+1) ≃ₗᵢ[ℝ] HermitianSpace (d+1))
    (A B : HermitianSpace (d+1)) : 2*⟪U A,U B⟫_ℝ=2*⟪A,B⟫_ℝ := by
  rw [U.inner_map_map]

theorem pure_metric_horizontal {d : ℕ} (h : PureVector d) (A : tangentSpace h) :
    PureSLDMetric.metricFromSLD h A A=4*‖tangentVector h A‖^2 := by
  rw [PureSLDMetric.metricFromSLD_eq,real_inner_self_eq_norm_sq]
  change 2*‖A‖^2=_
  rw [tangent_norm_sq]
  ring

theorem updatedState_intrinsic {d : ℕ} (h : PureVector d) (A : tangentSpace h) :
    updatedState h A=(1+‖A‖^2/2)⁻¹ •
      (rankOneDensity h.val+toMatrix A.val+
        toMatrix A.val*rankOneDensity h.val*toMatrix A.val) := by
  rw [updatedState_matrix_formula,tangent_norm_sq]
  congr 2
  ring

/-- The normalized update depends on the projector and tangent matrix,
not on the global phase of their unit-vector representative. -/
theorem updatedState_phase_invariant {d : ℕ} (h g : PureVector d)
    (A : tangentSpace h) (B : tangentSpace g)
    (hp : rankOneDensity h.val=rankOneDensity g.val) (hA : A.val=B.val) :
    updatedState h A=updatedState g B := by
  rw [updatedState_intrinsic,updatedState_intrinsic,hp]
  change (1+‖A.val‖^2/2)⁻¹ • _=(1+‖B.val‖^2/2)⁻¹ • _
  rw [hA]

end
end QubitOracle.AdaptiveDesign.TangentGLS
