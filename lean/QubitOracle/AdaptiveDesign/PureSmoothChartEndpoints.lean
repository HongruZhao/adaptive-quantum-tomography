import QubitOracle.AdaptiveDesign.PureAmplitudeEndpoints
import QubitOracle.AdaptiveDesign.ConsistentDeltaMethod

/-! Coordinate changes for the actual pure-state estimators. A chart
transition is represented by its measurable extension and Frechet derivative
at zero. Neither the observations nor the estimator are assumed independent.
The Gaussian limit is pushed forward by the chart Jacobian. -/
namespace QubitOracle.AdaptiveDesign
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive
open Filter MeasureTheory ProbabilityTheory TangentGLS
open scoped Topology InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace TangentGLS

theorem amplitudeCoordinates_self {d : ℕ} (truth : PureVector d) :
    amplitudeCoordinates truth (pureParameter d truth).val = 0 := by
  simp [amplitudeCoordinates]

theorem amplitudeCoordinates_continuousAt {d : ℕ} (truth : PureVector d) :
    ContinuousAt (amplitudeCoordinates truth) (pureParameter d truth).val :=
  (amplitude_factor_continuousAt truth).smul (by fun_prop)

theorem amplitudeCoordinates_comp_stronglyMeasurable {d : ℕ} (truth : PureVector d)
    {Ω : Type*} [MeasurableSpace Ω] (A : Ω → HermitianSpace (d+1))
    (hA : StronglyMeasurable A) : StronglyMeasurable (fun ω => amplitudeCoordinates truth (A ω)) := by
  unfold amplitudeCoordinates
  have hsub : StronglyMeasurable (fun ω => A ω - (pureParameter d truth).val) :=
    hA.sub (stronglyMeasurable_const :
      StronglyMeasurable (fun _ : Ω => (pureParameter d truth).val))
  exact ((stronglyMeasurable_const.inner hA).measurable.sqrt.inv.stronglyMeasurable).smul
    (((trueCoordinate truth).continuous.comp_stronglyMeasurable hsub).const_smul (2 : ℝ))

theorem smoothChart_clt_of_amplitude_clt {d : ℕ} (truth : PureVector d)
    {covMatrix : Matrix (TangentIndex d) (TangentIndex d) ℝ}
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (A : ℕ → Ω → HermitianSpace (d+1)) (hA : ∀ n, StronglyMeasurable (A n))
    (hc : ∀ᵐ ω ∂μ, Tendsto (fun n => A n ω) atTop (𝓝 (pureParameter d truth).val))
    (hclt : TendstoInDistribution (fun (n : ℕ) ω => Real.sqrt (n:ℝ) • amplitudeCoordinates truth (A n ω))
      atTop id (fun _ => μ)
      (multivariateGaussian 0 covMatrix))
    (φ : EuclideanSpace ℝ (TangentIndex d) → EuclideanSpace ℝ (TangentIndex d))
    (hφm : Measurable φ) (J : EuclideanSpace ℝ (TangentIndex d) →L[ℝ] EuclideanSpace ℝ (TangentIndex d))
    (hφ : HasFDerivAt φ J 0) :
    TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt (n:ℝ) • (φ (amplitudeCoordinates truth (A n ω))-φ 0))
      atTop (fun z => J z) (fun _ => μ)
      (multivariateGaussian 0 covMatrix) := by
  apply ConsistentDeltaMethod.delta_method
    (fun n ω => amplitudeCoordinates truth (A n ω)) id (fun n => Real.sqrt (n:ℝ)) 0
    (fun n => Real.sqrt_nonneg _) (fun n => (amplitudeCoordinates_comp_stronglyMeasurable truth (A n) (hA n)).measurable.aemeasurable)
  · filter_upwards [hc] with ω hω
    simpa only [Function.comp_def, amplitudeCoordinates_self] using
      (amplitudeCoordinates_continuousAt truth).tendsto.comp hω
  · simpa only [sub_zero] using hclt
  · exact hφm
  · exact hφ

variable {d : ℕ} {O : Type} [Fintype O]
  [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]

theorem smoothChart_optimalVariance
    (P : FinitePOVM (Fin (d+1)) O) (hI : GeneralPOVM.Identifying P)
    (hp : GeneralPOVM.Regular P) (hF : GeneralPOVM.FisherSymmetric P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j)
    (φ : EuclideanSpace ℝ (TangentIndex d) → EuclideanSpace ℝ (TangentIndex d))
    (hφm : Measurable φ) (J : EuclideanSpace ℝ (TangentIndex d) →L[ℝ] EuclideanSpace ℝ (TangentIndex d))
    (hφ : HasFDerivAt φ J 0) :
    TendstoInDistribution
      (fun (n : ℕ) path => Real.sqrt (n:ℝ) • (φ (amplitudeCoordinates truth
        (pureParameter d (actualEstimate P hI hp regularization ridge hr hη batchSize path n)).val)-φ 0))
      atTop (fun z => J z)
      (fun _ => adaptiveInfiniteTrajectoryMeasure (GeneralPOVM.adaptiveProtocol P hI regularization hr batchSize) truth)
      (multivariateGaussian 0 ((2:ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) := by
  apply smoothChart_clt_of_amplitude_clt truth
  · intro n
    exact FiniteHistoryStatistics.actualStatistic_stronglyMeasurable P hI regularization hr batchSize n
      (fun raw data => (pureParameter d
        (estimateFromRaw raw data (referenceFloor P) ridge (referenceFloor_pos P hp) hη)).val)
  · exact corrected_stronglyConsistent P hI hp truth regularization ridge hr hη batchSize
  · exact amplitude_optimalVariance P hI hp hF truth regularization ridge hr hη batchSize hpositive
  · exact hφm
  · exact hφ

theorem phasePair_smoothChart_optimalVariance
    (P : FinitePOVM (Fin (d+1)) O) (hI : GeneralPOVM.Identifying P)
    (hp : GeneralPOVM.Regular P) (hR : PhasePair.RankOne P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j)
    (φ : EuclideanSpace ℝ (TangentIndex d) → EuclideanSpace ℝ (TangentIndex d))
    (hφm : Measurable φ) (J : EuclideanSpace ℝ (TangentIndex d) →L[ℝ] EuclideanSpace ℝ (TangentIndex d))
    (hφ : HasFDerivAt φ J 0) :
    TendstoInDistribution
      (fun (n : ℕ) path => Real.sqrt (n:ℝ) • (φ (amplitudeCoordinates truth
        (pureParameter d (actualEstimate (PhasePair.paired P) (PhasePair.paired_identifying P hI)
          (PhasePair.paired_regular P hp) regularization ridge hr hη batchSize path n)).val)-φ 0))
      atTop (fun z => J z)
      (fun _ => adaptiveInfiniteTrajectoryMeasure
        (GeneralPOVM.adaptiveProtocol (PhasePair.paired P) (PhasePair.paired_identifying P hI)
          regularization hr batchSize) truth)
      (multivariateGaussian 0 ((2:ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) :=
  smoothChart_optimalVariance (PhasePair.paired P) (PhasePair.paired_identifying P hI)
    (PhasePair.paired_regular P hp) (PhasePair.paired_fisher_of_rankOne P hp hR)
    truth regularization ridge hr hη batchSize hpositive φ hφm J hφ
end TangentGLS

-- Section 5 proof route commented at the user request, 5 October 2026.
/-
namespace PVMPilotGLS
variable [PVMPilotSchedule.Schedule]
variable {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d]

theorem smoothChart_optimalVariance (truth : PureVector d) (ridge : ℝ) (hr : 0 < ridge)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) (hbudget : PVMPilotSchedule.OneStepBudget)
    (φ : EuclideanSpace ℝ (TangentIndex d) → EuclideanSpace ℝ (TangentIndex d))
    (hφm : Measurable φ) (J : EuclideanSpace ℝ (TangentIndex d) →L[ℝ] EuclideanSpace ℝ (TangentIndex d))
    (hφ : HasFDerivAt φ J 0) :
    TendstoInDistribution
      (fun (n : ℕ) path => Real.sqrt (n:ℝ) • (φ (amplitudeCoordinates truth
        (pureParameter d (actualEstimate ridge hr batchSize path n)).val)-φ 0))
      atTop (fun z => J z)
      (fun _ => adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth))
      (multivariateGaussian 0 ((2:ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))) := by
  apply smoothChart_clt_of_amplitude_clt truth
  · intro n
    exact actualStatistic_stronglyMeasurable batchSize n
      (fun raw data => (pureParameter d
        (estimateFromRaw raw data (floor d) ridge (floor_pos d) hr)).val)
  · exact corrected_consistent truth ridge hr batchSize hpositive
  · exact amplitude_optimalVariance truth ridge hr batchSize hpositive hbudget
  · exact hφm
  · exact hφ
end PVMPilotGLS
-/


end
end QubitOracle.AdaptiveDesign
