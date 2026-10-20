import QubitOracle.AdaptiveDesign.PhasePairAdaptive
import QubitOracle.AdaptiveDesign.GeneralPOVMRootRate
import QubitOracle.AdaptiveDesign.EfficientBornScoreCLT
import QubitOracle.AdaptiveDesign.FiniteHistoryStatistics
import QubitOracle.AdaptiveDesign.GeneralPOVMAdaptive
import QubitOracle.AdaptiveDesign.GeneralPOVMModel
import QubitOracle.AdaptiveDesign.GeneralPOVMTransport
import QubitOracle.AdaptiveDesign.GlobalPFSICBornModel
import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel
import QubitOracle.AdaptiveDesign.P2AdaptiveTheorem
import QubitOracle.AdaptiveDesign.PhasePairPOVM
import QubitOracle.AdaptiveDesign.PureAmplitudeChart
import QubitOracle.AdaptiveDesign.PureChartCovariance
import QubitOracle.AdaptiveDesign.PureMatrixController
import QubitOracle.AdaptiveDesign.PureSLDMetric
import QubitOracle.AdaptiveDesign.PureSmoothChartEndpoints
import QubitOracle.AdaptiveDesign.RidgeBatchSchedule
import QubitOracle.AdaptiveDesign.TangentGLSBounds
import QubitOracle.AdaptiveDesign.TangentGLSCoordinates
import QubitOracle.AdaptiveDesign.TangentGLSEstimator
import QubitOracle.AdaptiveDesign.TangentGLSGeometry
import QubitOracle.AdaptiveDesign.TangentGLSInformation
import QubitOracle.AdaptiveDesign.TangentGLSNormalizedError
import QubitOracle.AdaptiveDesign.TangentGLSOptimalVariance
import QubitOracle.AdaptiveDesign.TangentGLSRecordIdentities
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.AdaptiveTrajectoryExperiment
import QubitOracle.Paper.MainPaperPureCharts
import QubitOracle.TwoBasis
set_option autoImplicit false

/-! The literal ambient projector Gaussian limit and its covariance,
and the completed-batch limit in genuine smooth local coordinates.
These statements concern the implemented all-record estimator. -/
namespace QubitOracle.Paper.MainPaperPureLimits
open QubitOracle QubitOracle.Paper QubitOracle.AdaptiveDesign
open GlobalPFSICHermitian PureMatrixController P2Adaptive TangentGLS GeneralPOVM
open Filter MeasureTheory ProbabilityTheory
open scoped Topology InnerProductSpace BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

local instance hermitianMeasurable (n : ℕ) : MeasurableSpace (HermitianSpace n) := borel _
local instance hermitianBorel (n : ℕ) : BorelSpace (HermitianSpace n) := ⟨rfl⟩

abbrev Coordinates (d : ℕ) := PureChartCovariance.Coordinates d

abbrev gaussian (d : ℕ) : Measure (Coordinates d) :=
  multivariateGaussian 0 ((2 : ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))

def tangentLift {d : ℕ} (truth : PureVector d) : Coordinates d →L[ℝ] HermitianSpace (d+1) :=
  (1/2 : ℝ) • trueLift truth

def limitLaw {d : ℕ} (truth : PureVector d) : Measure (HermitianSpace (d+1)) :=
  (gaussian d).map (tangentLift truth)

theorem tangentLift_adjoint {d : ℕ} (truth : PureVector d) (A : HermitianSpace (d+1)) :
    (tangentLift truth).adjoint A = trueCoordinate truth A := by
  apply ext_inner_left ℝ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp only [tangentLift, smul_apply, real_inner_smul_left, trueLift_inner]
  ring

theorem limitLaw_gaussian {d : ℕ} (truth : PureVector d) : IsGaussian (limitLaw truth) := by
  unfold limitLaw gaussian
  infer_instance

theorem limitLaw_mean {d : ℕ} (truth : PureVector d) :
    ∫ A, A ∂limitLaw truth = 0 := by
  rw [limitLaw, ContinuousLinearMap.integral_id_map]
  · simp [gaussian]
  · exact IsGaussian.integrable_id

theorem limitLaw_covariance {d : ℕ} (truth : PureVector d) (A B : HermitianSpace (d+1)) :
    covarianceBilin (limitLaw truth) A B = ⟪A, tangentProjector truth B⟫_ℝ := by
  rw [limitLaw, covarianceBilin_map IsGaussian.memLp_two_id (tangentLift truth)]
  rw [show gaussian d = multivariateGaussian 0
    ((2 : ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)) from rfl,
    PureChartCovariance.covariance_normalized, tangentLift_adjoint, tangentLift_adjoint,
    true_inner_projection]

theorem limitLaw_tangent_covariance {d : ℕ} (truth : PureVector d) (A B : tangentSpace truth) :
    covarianceBilin (limitLaw truth) A.val B.val = ⟪A, B⟫_ℝ := by
  rw [limitLaw_covariance]
  change ⟪A.val, (tangentSpace truth).starProjection B.val⟫_ℝ = _
  rw [Submodule.starProjection_eq_self_iff.mpr B.property]
  rfl

theorem limitLaw_tangent_support {d : ℕ} (truth : PureVector d) :
    ∀ᵐ A ∂limitLaw truth, A ∈ tangentSpace truth := by
  unfold limitLaw
  apply (ae_map_iff (tangentLift truth).measurable.aemeasurable
    (tangentSpace truth).closed_of_finiteDimensional.measurableSet).2
  filter_upwards [] with u
  exact (tangentSpace truth).smul_mem (1/2 : ℝ) (PureSLDMetric.trueLift_mem truth u)

theorem batch_horizons_tendsto (m : ℕ → ℕ) (hm : ∀ j, 0 < m j) :
    Tendsto (SequentialRidgeController.batchBoundary m) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop b] with j hj
  exact hj.trans (SequentialRidgeController.le_batchBoundary m hm j)

variable {d : ℕ} {O : Type} [Fintype O]
  [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]

theorem lifted_score
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P)
    (truth : PureVector d) (regularization : ℝ) (hr : 0 < regularization)
    (batchSize : ℕ → ℕ) (n : ℕ) (path : AdaptiveInfinitePath O) :
    tangentLift truth (EfficientBornScoreCLT.fullScore P hI truth regularization hr batchSize n path) =
      (Real.sqrt (n : ℝ))⁻¹ • tangentProjector truth
        (actualScoreSum P hI truth (referenceFloor P) regularization hr batchSize n path) := by
  rw [fullScore_eq_coordinate]
  simp only [tangentLift, smul_apply, map_smul,
    trueCoordinate_projection, trueLift_coordinate, smul_smul]
  congr 1
  ring

/-- The ambient Gaussian assertion in Theorem 4.2, previously available
only through a coordinate CLT and a separate projector linearization. -/
theorem ambient_clt
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P)
    (hF : FisherSymmetric P) (truth : PureVector d)
    (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    TendstoInDistribution
      (fun (n : ℕ) path => Real.sqrt (n : ℝ) •
        ((pureParameter d (actualEstimate P hI hp regularization ridge hr hη batchSize path n)).val-
          (pureParameter d truth).val))
      atTop (tangentLift truth)
      (fun _ => adaptiveInfiniteTrajectoryMeasure (adaptiveProtocol P hI regularization hr batchSize) truth)
      (gaussian d) := by
  have hh := (EfficientBornScoreCLT.fullScore_clt P hI hp hF truth regularization hr batchSize
    hpositive).continuous_comp (tangentLift truth).continuous
  apply tendstoInDistribution_of_tendstoInMeasure_sub _ _ hh
  · have hz := actualProjectorError_linearization P hI hp hF truth regularization ridge hr hη
      batchSize hpositive
    intro ε hε
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [Function.comp_def, lifted_score, actualProjectorError,
      Pi.sub_apply, Pi.zero_apply] using hz ε hε
  · intro n
    exact (FiniteHistoryStatistics.actualStatistic_stronglyMeasurable P hI regularization hr batchSize n
      (fun raw data => Real.sqrt (n : ℝ) •
        ((pureParameter d (estimateFromRaw raw data (referenceFloor P) ridge
          (referenceFloor_pos P hp) hη)).val-(pureParameter d truth).val))).measurable.aemeasurable

theorem phasePair_completed_ambient_clt
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P)
    (hR : PhasePair.RankOne P) (truth : PureVector d)
    (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    TendstoInDistribution
      (fun (j : ℕ) path => Real.sqrt (SequentialRidgeController.batchBoundary batchSize j : ℝ) •
        ((pureParameter d (actualEstimate (PhasePair.paired P) (PhasePair.paired_identifying P hI)
          (PhasePair.paired_regular P hp) regularization ridge hr hη batchSize path
          (SequentialRidgeController.batchBoundary batchSize j))).val-(pureParameter d truth).val))
      atTop (tangentLift truth)
      (fun _ => adaptiveInfiniteTrajectoryMeasure
        (adaptiveProtocol (PhasePair.paired P) (PhasePair.paired_identifying P hI)
          regularization hr batchSize) truth) (gaussian d) := by
  have hh := ambient_clt (PhasePair.paired P) (PhasePair.paired_identifying P hI)
    (PhasePair.paired_regular P hp) (PhasePair.paired_fisher_of_rankOne P hp hR)
    truth regularization ridge hr hη batchSize hpositive
  exact { forall_aemeasurable := fun j => hh.forall_aemeasurable _
          aemeasurable_limit := hh.aemeasurable_limit
          tendsto := hh.tendsto.comp (batch_horizons_tendsto batchSize hpositive) }

theorem phasePair_completed_chart_clt
    (P : FinitePOVM (Fin (d+1)) O) (hI : Identifying P) (hp : Regular P)
    (hR : PhasePair.RankOne P) (truth : PureVector d)
    (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j)
    (C : MainPaperPureCharts.SmoothCoordinates d) :
    TendstoInDistribution
      (fun (j : ℕ) path => Real.sqrt (SequentialRidgeController.batchBoundary batchSize j : ℝ) •
        (C.extension (amplitudeCoordinates truth
          (pureParameter d (actualEstimate (PhasePair.paired P) (PhasePair.paired_identifying P hI)
            (PhasePair.paired_regular P hp) regularization ridge hr hη batchSize path
            (SequentialRidgeController.batchBoundary batchSize j))).val)-C.change 0))
      atTop C.derivativeEquiv
      (fun _ => adaptiveInfiniteTrajectoryMeasure
        (adaptiveProtocol (PhasePair.paired P) (PhasePair.paired_identifying P hI)
          regularization hr batchSize) truth) (gaussian d) := by
  have hh := phasePair_smoothChart_optimalVariance P hI hp hR truth regularization ridge hr hη
    batchSize hpositive C.extension C.extension_measurable C.derivativeEquiv.toContinuousLinearMap
    C.extension_hasDerivative
  simp only [C.extension_zero] at hh
  exact { forall_aemeasurable := fun j => hh.forall_aemeasurable _
          aemeasurable_limit := hh.aemeasurable_limit
          tendsto := hh.tendsto.comp (batch_horizons_tendsto batchSize hpositive) }

end
end QubitOracle.Paper.MainPaperPureLimits
