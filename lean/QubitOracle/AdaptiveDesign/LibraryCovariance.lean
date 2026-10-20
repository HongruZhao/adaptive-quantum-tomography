import QubitOracle.AdaptiveDesign.PureChartDifferential
import QubitOracle.AdaptiveDesign.GlobalPFSIC
import QubitOracle.AdaptiveDesign.GlobalPFSICBornModel
import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel
import QubitOracle.AdaptiveDesign.GlobalPFSICLibrary
import QubitOracle.AdaptiveDesign.LibraryPureNormality
import QubitOracle.AdaptiveDesign.LibraryRidgeLinearization
import QubitOracle.AdaptiveDesign.LibraryScoreCLT
import QubitOracle.AdaptiveDesign.LibraryUnweightedMoments
import QubitOracle.AdaptiveDesign.P2AdaptiveTheorem
import QubitOracle.AdaptiveDesign.PureAmplitudeChart
import QubitOracle.AdaptiveDesign.PureChartCovariance
import QubitOracle.AdaptiveDesign.PureMatrixController
import QubitOracle.AdaptiveDesign.RidgeBatchSchedule
import QubitOracle.AdaptiveDesign.TangentGLSBounds
import QubitOracle.AdaptiveDesign.TangentGLSCoordinates
import QubitOracle.AdaptiveDesign.TangentGLSInformation
import QubitOracle.Paper.AdaptiveTrajectoryExperiment
import QubitOracle.TwoBasis
/-! The covariance stated in the supplement: in any invertible smooth
coordinate system it is gamma_D times the inverse actual SLD metric. -/
namespace QubitOracle.AdaptiveDesign.LibraryUnweighted
open QubitOracle QubitOracle.Paper GlobalPFSIC GlobalPFSICHermitian GlobalPFSICBorn
open PureMatrixController P2Adaptive TangentGLS Filter MeasureTheory ProbabilityTheory
open PureChartCovariance
open scoped BigOperators Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000

local instance libraryHermitianMeasurable (n : ℕ) : MeasurableSpace (HermitianSpace n) := borel _
local instance libraryHermitianBorel (n : ℕ) : BorelSpace (HermitianSpace n) := ⟨rfl⟩

def normalizedTangentLift {d : ℕ} (truth : PureVector d) :
    Coordinates d →L[ℝ] HermitianSpace (d+1) := (1/2:ℝ) • trueLift truth

lemma normalizedTangentLift_adjoint {d : ℕ} (truth : PureVector d) (A : HermitianSpace (d+1)) :
    (normalizedTangentLift truth).adjoint A=trueCoordinate truth A := by
  apply ext_inner_left ℝ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp only [normalizedTangentLift, ContinuousLinearMap.smul_apply, real_inner_smul_left,
    trueLift_inner]
  ring

lemma fullScore_lift {d : ℕ} (hd : 0 < d) (truth : PureVector d)
    (batchSize : ℕ → ℕ) (n : ℕ) (path : AdaptiveInfinitePath (Outcome d)) :
    normalizedTangentLift truth (fullScore hd truth batchSize n path) =
      (gramConstant d*Real.sqrt (n:ℝ))⁻¹ • tangentProjector truth (noiseSum hd truth batchSize n path) := by
  simp only [fullScore_coordinate, normalizedTangentLift, ContinuousLinearMap.smul_apply,
    map_smul, trueCoordinate_projection, trueLift_coordinate, smul_smul]
  module

theorem ambient_clt {d : ℕ} (hd : 0 < d) (truth : PureVector d)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    TendstoInDistribution
      (fun (n : ℕ) path => Real.sqrt (n:ℝ) • (pureEstimate hd batchSize n path-(pureParameter d truth).val))
      atTop (normalizedTangentLift truth)
      (fun _ => adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol hd batchSize) (pureParameter d truth))
      (multivariateGaussian 0 ((2*tangentVariance d) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) := by
  have hh := (fullScore_clt hd truth batchSize hpositive).continuous_comp (normalizedTangentLift truth).continuous
  apply tendstoInDistribution_of_tendstoInMeasure_sub _ _ hh
  · have hz := pure_linearization hd truth batchSize hpositive
    intro ε hε
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [Function.comp_def, fullScore_lift, Pi.sub_apply, Pi.zero_apply] using hz ε hε
  · intro n
    exact ((pureEstimate_measurable hd batchSize n).sub stronglyMeasurable_const).const_smul
      (Real.sqrt (n:ℝ)) |>.measurable.aemeasurable

lemma batch_horizons_tendsto (m : ℕ → ℕ) (hm : ∀ j, 0 < m j) :
    Tendsto (SequentialRidgeController.batchBoundary m) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop b] with J hJ
  exact hJ.trans (SequentialRidgeController.le_batchBoundary m hm J)

theorem completed_batch_amplitude_clt {d : ℕ} (hd : 0 < d) (truth : PureVector d)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    TendstoInDistribution
      (fun (J : ℕ) path => Real.sqrt ((SequentialRidgeController.batchBoundary batchSize J:ℕ):ℝ) •
        amplitudeCoordinates truth (pureEstimate hd batchSize (SequentialRidgeController.batchBoundary batchSize J) path))
      atTop id
      (fun _ => adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol hd batchSize) (pureParameter d truth))
      (multivariateGaussian 0 ((2*tangentVariance d) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) := by
  have hh := amplitude_clt hd truth batchSize hpositive
  exact { forall_aemeasurable := fun J => hh.forall_aemeasurable _
          aemeasurable_limit := hh.aemeasurable_limit
          tendsto := hh.tendsto.comp (batch_horizons_tendsto batchSize hpositive) }

theorem completed_batch_ambient_clt {d : ℕ} (hd : 0 < d) (truth : PureVector d)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    TendstoInDistribution
      (fun (J : ℕ) path => Real.sqrt ((SequentialRidgeController.batchBoundary batchSize J:ℕ):ℝ) •
        (pureEstimate hd batchSize (SequentialRidgeController.batchBoundary batchSize J) path-
          (pureParameter d truth).val)) atTop (normalizedTangentLift truth)
      (fun _ => adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol hd batchSize) (pureParameter d truth))
      (multivariateGaussian 0 ((2*tangentVariance d) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) := by
  have hh := ambient_clt hd truth batchSize hpositive
  exact { forall_aemeasurable := fun J => hh.forall_aemeasurable _
          aemeasurable_limit := hh.aemeasurable_limit
          tendsto := hh.tendsto.comp (batch_horizons_tendsto batchSize hpositive) }

theorem covariance_scalar {d : ℕ} (c : ℝ) (hc : 0 ≤ c) (u v : Coordinates d) :
    covarianceBilin (multivariateGaussian 0 (c • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) u v =
      c*⟪u,v⟫_ℝ := by
  rw [covarianceBilin_multivariateGaussian (Matrix.PosSemidef.one.smul hc)]
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  rw [dotProduct_comm]

theorem covariance_in_smoothChart {d : ℕ} (hd : 0 < d)
    (J : Coordinates d ≃L[ℝ] Coordinates d) (u v : Coordinates d) :
    covarianceBilin
      ((multivariateGaussian 0 ((2*tangentVariance d) •
        (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))).map J) u v =
      (2*tangentVariance d)*⟪u,inverseQfiOperator J v⟫_ℝ := by
  have hc : 0 ≤ 2*tangentVariance d := by
    rw [← variance_ratio hd]
    exact mul_nonneg (by norm_num) (div_nonneg (constants_positive hd).2.le (sq_nonneg _))
  change covarianceBilin
    ((multivariateGaussian 0 ((2*tangentVariance d) •
      (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))).map J.toContinuousLinearMap) u v = _
  rw [covarianceBilin_map IsGaussian.memLp_two_id J.toContinuousLinearMap, covariance_scalar _ hc]
  congr 1
  unfold inverseQfiOperator
  exact ContinuousLinearMap.adjoint_inner_left J.toContinuousLinearMap _ _

theorem covariance_in_ambientSpace {d : ℕ} (hd : 0 < d) (truth : PureVector d)
    (A B : HermitianSpace (d+1)) :
    covarianceBilin
      ((multivariateGaussian 0 ((2*tangentVariance d) •
        (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))).map (normalizedTangentLift truth)) A B =
      tangentVariance d*⟪A,tangentProjector truth B⟫_ℝ := by
  have hc : 0 ≤ 2*tangentVariance d := by
    rw [← variance_ratio hd]
    exact mul_nonneg (by norm_num) (div_nonneg (constants_positive hd).2.le (sq_nonneg _))
  rw [covarianceBilin_map IsGaussian.memLp_two_id (normalizedTangentLift truth),
    covariance_scalar _ hc, normalizedTangentLift_adjoint, normalizedTangentLift_adjoint,
    true_inner_projection]
  ring

theorem variance_excess {d : ℕ} (hd : 0 < d) :
    2*tangentVariance d-2 =
      2*(2*(d+1)-3)*(2*(d+1)-1)/(4*(d+1)-5)^2 ∧ 2 < 2*tangentVariance d := by
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
  have ha : 4*((d:ℝ)+1)-5 ≠ 0 := by linarith
  have he : 2*tangentVariance d-2 =
      2*(2*(d+1)-3)*(2*(d+1)-1)/(4*(d+1)-5)^2 := by
    unfold tangentVariance
    field_simp
    <;> ring
  refine ⟨he,?_⟩
  have hp : 0 < 2*(2*((d:ℝ)+1)-3)*(2*(d+1)-1)/(4*(d+1)-5)^2 := by
    apply div_pos
    · exact mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)
    · exact sq_pos_of_ne_zero ha
  linarith

theorem variance_qubit : 2*tangentVariance 1=8/3 := by norm_num [tangentVariance]
theorem variance_qutrit : 2*tangentVariance 2=128/49 := by norm_num [tangentVariance]

end
end QubitOracle.AdaptiveDesign.LibraryUnweighted
