import QubitOracle.AdaptiveDesign.GeneralPOVMAdaptive
import QubitOracle.AdaptiveDesign.GeneralPOVMModel
import QubitOracle.AdaptiveDesign.GeneralPOVMProbabilityLimits
import QubitOracle.AdaptiveDesign.GeneralPOVMTransport
import QubitOracle.AdaptiveDesign.GlobalPFSICBornModel
import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel
import QubitOracle.AdaptiveDesign.GlobalPFSICTransport
import QubitOracle.AdaptiveDesign.P2AdaptiveTheorem
import QubitOracle.AdaptiveDesign.PureMatrixController
import QubitOracle.AdaptiveDesign.TangentGLSAlgebra
import QubitOracle.AdaptiveDesign.TangentGLSAmbient
import QubitOracle.AdaptiveDesign.TangentGLSBounds
import QubitOracle.AdaptiveDesign.TangentGLSCoordinates
import QubitOracle.AdaptiveDesign.TangentGLSEstimator
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.AdaptiveTrajectoryExperiment
import QubitOracle.Paper.CompactLimitTransfer
import QubitOracle.Paper.PureStateFoundations
import QubitOracle.Paper.RankOneStageContinuity
import QubitOracle.TwoBasis
/-! The information operator in fixed coordinates and in the intrinsic
tangent space. The positive probability floor is included explicitly. -/

namespace QubitOracle.AdaptiveDesign.TangentGLS

open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive
open GeneralPOVM Filter MeasureTheory
open scoped BigOperators Topology ComplexOrder InnerProductSpace Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

theorem true_inner_projection {d : ℕ} (truth : PureVector d) (A B : HermitianSpace (d+1)) :
    ⟪A,tangentProjector truth B⟫_ℝ = 2*⟪trueCoordinate truth A,trueCoordinate truth B⟫_ℝ := by
  rw [← trueLift_coordinate, real_inner_comm, trueLift_inner, real_inner_comm]

theorem projected_gram_coordinates {d : ℕ} {R : Type*} [Fintype R]
    (truth : PureVector d) (f : R → HermitianSpace (d+1)) (w : R → ℝ) :
    (tangentProjector truth).comp ((gramCLM f w).comp (tangentProjector truth)) =
      (trueLift truth).comp (((2 : ℝ) • gramCLM (fun r => trueCoordinate truth (f r)) w).comp
        (trueCoordinate truth)) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, gramCLM_apply]
  simp_rw [true_inner_projection]
  simp only [map_sum, map_smul, ← trueLift_coordinate, ContinuousLinearMap.smul_apply,
    gramCLM_apply, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  ring

theorem gramCLM_eq_matrix {I O : Type} [Fintype I] [DecidableEq I] [Fintype O]
    (p : O → ℝ) (g : O → EuclideanSpace ℝ I) :
    gramCLM g (fun y => (p y)⁻¹) =
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := I)) (weightedGram p (fun y => (g y).ofLp)) := by
  ext x i
  rw [gramCLM_apply, Matrix.ofLp_toEuclideanCLM]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Matrix.mulVec, dotProduct,
    weightedGram_apply, safeRatio_eq_div, div_eq_mul_inv,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro j _
  ring

def informationLift {d : ℕ} (truth : PureVector d)
    (M : Matrix (TangentIndex d) (TangentIndex d) ℝ) :
    HermitianSpace (d+1) →L[ℝ] HermitianSpace (d+1) :=
  (trueLift truth).comp (((2 : ℝ) • (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := TangentIndex d)) M).comp (trueCoordinate truth))

theorem informationLift_half_identity {d : ℕ} (truth : PureVector d) :
    informationLift truth ((1/2 : ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)) =
      tangentProjector truth := by
  ext x
  simp only [informationLift, map_smul, map_one, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, smul_smul]
  norm_num
  exact trueLift_coordinate truth x

theorem informationLift_continuous {d : ℕ} (truth : PureVector d) : Continuous (informationLift truth) := by
  have hc : Continuous (fun M : Matrix (TangentIndex d) (TangentIndex d) ℝ => (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := TangentIndex d)) M) :=
    ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := TangentIndex d)).toAlgEquiv.toLinearEquiv.toLinearMap).continuous_of_finiteDimensional
  unfold informationLift
  fun_prop

def protectedFisher {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (floor : ℝ) (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    Matrix (TangentIndex d) (TangentIndex d) ℝ :=
  weightedGram (fun y => denominator floor (mass P U y)) (gradient P U)

theorem protectedFisher_continuous {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (floor : ℝ) (hf : 0 < floor) :
    Continuous (protectedFisher P floor) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [protectedFisher, weightedGram_apply, safeRatio_eq_div]
  apply continuous_finset_sum
  intro y _
  apply ((gradient_continuous P y i).mul (gradient_continuous P y j)).div
    ((mass_continuous P y).max continuous_const)
  exact fun U => (denominator_pos hf (mass P U y)).ne'

theorem protectedFisher_eq_fisher {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (floor : ℝ) (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hregular : ∀ y, floor ≤ mass P U y) : protectedFisher P floor U = fisher P U := by
  ext i j
  simp only [protectedFisher, weightedGram_apply, fisher, denominator, max_eq_left (hregular _)]

theorem protectedFisher_tendsto {d : ℕ} {O : Type} [Fintype O]
    (P : FinitePOVM (Fin (d+1)) O) (hF : FisherSymmetric P)
    (floor : ℝ) (hf : 0 < floor) (hfloor : ∀ y, floor ≤ referenceProbability P y)
    (controller : ℕ → Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (hU : ∀ n, controller n ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ)
    (h : Tendsto (fun n => controllerTrueOverlapSq (controller n)) atTop (𝓝 1)) :
    Tendsto (fun n => protectedFisher P floor (controller n)) atTop
      (𝓝 ((1/2 : ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) := by
  refine tendsto_of_compact_identified_fiber
    {U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ | U ∈ Matrix.unitaryGroup (Fin (d+1)) ℂ}
    isCompact_unitaryMatrices controller hU
    controllerTrueOverlapSq continuous_controllerTrueOverlapSq 1 h
    (protectedFisher P floor) _ ?_
  intro U hU hoverlap
  refine ⟨(protectedFisher_continuous P floor hf).continuousAt, ?_⟩
  rw [protectedFisher_eq_fisher P floor U (fun y => by
    rw [mass_of_overlap_one P U hU hoverlap]; exact hfloor y), fisher_of_overlap_one P hF U hU hoverlap]

theorem actual_protectedFisher_tendsto {d : ℕ} {O : Type} [Fintype O]
    [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P) (hF : FisherSymmetric P)
    (truth : PureVector d) (regularization : ℝ) (hr : 0 < regularization)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth,
      Tendsto (fun n => protectedFisher P (referenceFloor P)
        ((trueFrame d truth).conjTranspose * measurementFrame P hI regularization hr batchSize path n))
        atTop (𝓝 ((1/2 : ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) := by
  filter_upwards [adaptive_consistency P hI regularization hr truth batchSize hpositive] with path hp'
  have hproj : Tendsto (fun n => GlobalPFSIC.frameProjector
      (measurementFrame P hI regularization hr batchSize path n)) atTop
      (𝓝 (GlobalPFSIC.frameProjector (trueFrame d truth))) := by
    rw [trueFrame_projector]
    exact hp'.2.2
  have hrel := GlobalPFSIC.relative_overlap_tendsto (trueFrame d truth)
    (trueFrame_unitary d truth) (measurementFrame P hI regularization hr batchSize path) hproj
  apply protectedFisher_tendsto P hF (referenceFloor P) (referenceFloor_pos P hp)
    (fun y => ?_) _ (fun n => GlobalPFSIC.relative_unitary _ _ (trueFrame_unitary d truth)
      (measurementFrame_unitary P hI regularization hr batchSize path n)) hrel
  have hb := four_referenceFloor_le P y
  have hf := referenceFloor_pos P hp
  linarith

end
end QubitOracle.AdaptiveDesign.TangentGLS
