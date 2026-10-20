-- Section 5 proof route commented at the user request, 5 October 2026.
/-
import QubitOracle.AdaptiveDesign.PVMUniformMoments
import QubitOracle.AdaptiveDesign.PVMPilotBornFisherIdentification
import QubitOracle.AdaptiveDesign.PVMPilotResponse
import QubitOracle.AdaptiveDesign.TangentGLSInformation

/-! The unweighted tangent Gram and noise moments for the literal adaptive
PVM design converge to their balanced-pair values. -/
namespace QubitOracle.AdaptiveDesign.PVMPilotGLS
open QubitOracle QubitOracle.Paper GlobalPFSIC GlobalPFSICHermitian GlobalPFSICBorn
open PureMatrixController P2Adaptive TangentGLS PVMGeometry PVMPilotBorn PVMPilotSchedule
open PVMUniformMoments Filter MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace Topology Matrix.Norms.Elementwise
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
variable [PVMPilotSchedule.Schedule]
variable {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d]

lemma basis_probability_true (truth : PureVector d) (U : Action d) (k : Fin (d+1)) :
    basisProbability (pureParameter d truth) U k =
      fixedChartBasisProbability ((trueFrame d truth).conjTranspose*U.matrix) k := by
  unfold basisProbability
  rw [inner_eq_trace,basisEffect_matrix]
  change (Matrix.trace (rankOneDensity truth.val*projector _)).re = _
  rw [← trueFrame_projector d truth, P2Adaptive.trace_frameProjector_mul]
  have hh := projector_mulVec (trueFrame d truth).conjTranspose (fun i => U.matrix i k)
  rw [Matrix.conjTranspose_conjTranspose] at hh
  rw [← hh]
  change (((trueFrame d truth).conjTranspose*U.matrix) 0 k *
    star (((trueFrame d truth).conjTranspose*U.matrix) 0 k)).re = _
  simp [fixedChartBasisProbability,Complex.mul_re,Complex.normSq_apply]

lemma basis_coordinate (truth : PureVector d) (U : Action d) (k : Fin (d+1)) :
    trueCoordinate truth (basisEffect U k) =
      WithLp.toLp 2 (fixedChartBasisGradient ((trueFrame d truth).conjTranspose*U.matrix) k) := by
  change WithLp.toLp 2 (GeneralPOVM.matrixGradient
    ((trueFrame d truth).conjTranspose * toMatrix (basisEffect U k) *
      (trueFrame d truth).conjTranspose.conjTranspose)) = _
  rw [basisEffect_matrix, ← projector_mulVec]
  change WithLp.toLp 2 (GeneralPOVM.matrixGradient
    (projector (fun i => ((trueFrame d truth).conjTranspose*U.matrix) i k))) = _
  ext x
  cases x <;> simp [GeneralPOVM.matrixGradient, projector_apply, fixedChartBasisGradient,
    Complex.mul_re, Complex.mul_im] <;> ring

def coordinateGram (truth : PureVector d) (a : ℕ × Action d) :
    Matrix (TangentIndex d) (TangentIndex d) ℝ :=
  ∑ b : Setting d, settingWeight d a.1 b • basisGram
    ((trueFrame d truth).conjTranspose*(settingBasis a.2 b).matrix)

def coordinateMoment (truth : PureVector d) (a : ℕ × Action d) :
    Matrix (TangentIndex d) (TangentIndex d) ℝ :=
  ∑ b : Setting d, settingWeight d a.1 b • basisMoment
    ((trueFrame d truth).conjTranspose*(settingBasis a.2 b).matrix)

lemma coordinateGram_mixture (truth : PureVector d) (a : ℕ × Action d) :
    coordinateGram truth a = (1-epsilon a.1) • stageGram (PVMGeneralGeometry.exploitationFrame d)
      ((trueFrame d truth).conjTranspose*a.2.matrix)+epsilon a.1 •
        ((Fintype.card (PVMGeneralGeometry.ExplorationIndex d):ℝ)⁻¹ •
          ∑ l : PVMGeneralGeometry.ExplorationIndex d,
            basisGram ((trueFrame d truth).conjTranspose*(PVMGeneralGeometry.explorationBasis l).matrix)) := by
  rw [coordinateGram, Fintype.sum_sum_type]
  ext x y
  simp only [Fintype.sum_bool, settingWeight, settingBasis, stageGram,
    controllerChiBasis, controllerTauBasis, PVMGeneralGeometry.exploitationChiAction, PVMGeneralGeometry.exploitationTauAction,
    transportedChiBasis, transportedTauBasis, Matrix.mul_assoc,
    Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Finset.mul_sum]
  ring

lemma coordinateMoment_mixture (truth : PureVector d) (a : ℕ × Action d) :
    coordinateMoment truth a = (1-epsilon a.1) • stageMoment (PVMGeneralGeometry.exploitationFrame d)
      ((trueFrame d truth).conjTranspose*a.2.matrix)+epsilon a.1 •
        ((Fintype.card (PVMGeneralGeometry.ExplorationIndex d):ℝ)⁻¹ •
          ∑ l : PVMGeneralGeometry.ExplorationIndex d,
            basisMoment ((trueFrame d truth).conjTranspose*(PVMGeneralGeometry.explorationBasis l).matrix)) := by
  rw [coordinateMoment, Fintype.sum_sum_type]
  ext x y
  simp only [Fintype.sum_bool, settingWeight, settingBasis, stageMoment,
    controllerChiBasis, controllerTauBasis, PVMGeneralGeometry.exploitationChiAction, PVMGeneralGeometry.exploitationTauAction,
    transportedChiBasis, transportedTauBasis, Matrix.mul_assoc,
    Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Finset.mul_sum]
  ring

lemma actual_moment_limits (truth : PureVector d) (batchSize : ℕ → ℕ)
    (hpositive : ∀ j, 0 < batchSize j) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth),
      Tendsto (fun n => coordinateGram truth (n,(PVMPilotAdaptive.actualState d batchSize path n).action))
        atTop (𝓝 ((1/(2*(d+1:ℝ))) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) ∧
      Tendsto (fun n => coordinateMoment truth (n,(PVMPilotAdaptive.actualState d batchSize path n).action))
        atTop (𝓝 ((1/(2*(d+1:ℝ)^2)) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) := by
  filter_upwards [PVMPilotAdaptive.frozenController_ray_consistent d truth batchSize hpositive] with path hp
  have hproj : Tendsto (fun n => frameProjector (PVMPilotAdaptive.measurementFrame d batchSize path n))
      atTop (𝓝 (frameProjector (trueFrame d truth))) := by rwa [trueFrame_projector]
  have hrel := relative_overlap_tendsto (trueFrame d truth) (trueFrame_unitary d truth)
    (PVMPilotAdaptive.measurementFrame d batchSize path) hproj
  have hm := stage_moments_tendsto (PVMGeneralGeometry.exploitationFrame d)
    (fun n => (trueFrame d truth).conjTranspose*PVMPilotAdaptive.measurementFrame d batchSize path n)
    (fun n => relative_unitary _ _ (trueFrame_unitary d truth)
      (PVMPilotAdaptive.measurementFrame_unitary d batchSize path n)) hrel
  constructor
  · simp_rw [coordinateGram_mixture]
    have hh := (((show Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) from tendsto_const_nhds).sub
      epsilon_tendsto_zero).smul hm.1).add (epsilon_tendsto_zero.smul_const
        ((Fintype.card (PVMGeneralGeometry.ExplorationIndex d):ℝ)⁻¹ •
          ∑ l : PVMGeneralGeometry.ExplorationIndex d,
            basisGram ((trueFrame d truth).conjTranspose*(PVMGeneralGeometry.explorationBasis l).matrix)))
    simpa only [PVMPilotAdaptive.measurementFrame, sub_zero,one_smul,zero_smul,add_zero] using hh
  · simp_rw [coordinateMoment_mixture]
    have hh := (((show Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) from tendsto_const_nhds).sub
      epsilon_tendsto_zero).smul hm.2).add (epsilon_tendsto_zero.smul_const
        ((Fintype.card (PVMGeneralGeometry.ExplorationIndex d):ℝ)⁻¹ •
          ∑ l : PVMGeneralGeometry.ExplorationIndex d,
            basisMoment ((trueFrame d truth).conjTranspose*(PVMGeneralGeometry.explorationBasis l).matrix)))
    simpa only [PVMPilotAdaptive.measurementFrame, sub_zero,one_smul,zero_smul,add_zero] using hh

lemma basis_projectedGram (truth : PureVector d) (U : Action d) :
    (tangentProjector truth).comp ((gramCLM (basisEffect U) (fun _ => 1)).comp (tangentProjector truth)) =
      informationLift truth (basisGram ((trueFrame d truth).conjTranspose*U.matrix)) := by
  rw [projected_gram_coordinates]
  simp_rw [basis_coordinate]
  have he : gramCLM (fun k => WithLp.toLp 2 (fixedChartBasisGradient
      ((trueFrame d truth).conjTranspose*U.matrix) k)) (fun _ => 1) =
      (Matrix.toEuclideanCLM (𝕜:=ℝ) (n:=TangentIndex d))
        (basisGram ((trueFrame d truth).conjTranspose*U.matrix)) := by
    have h := gramCLM_eq_matrix (fun _ : Fin (d+1) => (1:ℝ))
      (fun k => WithLp.toLp 2 (fixedChartBasisGradient ((trueFrame d truth).conjTranspose*U.matrix) k))
    have hM : GeneralPOVM.weightedGram (fun _ : Fin (d+1) => (1:ℝ))
        (fixedChartBasisGradient ((trueFrame d truth).conjTranspose*U.matrix)) =
        basisGram ((trueFrame d truth).conjTranspose*U.matrix) := by
      ext x y
      simp only [GeneralPOVM.weightedGram_apply, GeneralPOVM.safeRatio_eq_div, div_one, basisGram]
    rw [hM] at h
    simpa only [inv_one] using h
  rw [he]
  rfl

end
end QubitOracle.AdaptiveDesign.PVMPilotGLS

-/
