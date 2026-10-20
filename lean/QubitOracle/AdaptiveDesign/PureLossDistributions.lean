import QubitOracle.AdaptiveDesign.PureAmplitudeLoss
import QubitOracle.AdaptiveDesign.PureAmplitudeEndpoints
import QubitOracle.Paper.PureMultilevelLossConstants
import Mathlib.Analysis.Matrix.Order

/-! Physical loss distributions of the actual corrected pure-state
estimators. A chi-square random variable is represented by the squared
norm of a standard Gaussian on the `2*d` real tangent coordinates. -/
namespace QubitOracle.AdaptiveDesign
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive
open Filter MeasureTheory ProbabilityTheory TangentGLS
open PureMultilevelDeterministicGeometry
open scoped BigOperators Topology InnerProductSpace MatrixOrder
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace PureLossDistributions

theorem doubled_gaussian {ι : Type*} [Fintype ι] [DecidableEq ι] :
    multivariateGaussian 0 ((2:ℝ) • (1 : Matrix ι ι ℝ)) =
      (stdGaussian (EuclideanSpace ℝ ι)).map (fun z => Real.sqrt 2 • z) := by
  have hs : CFC.sqrt ((2:ℝ) • (1 : Matrix ι ι ℝ)) = Real.sqrt 2 • (1 : Matrix ι ι ℝ) := by
    apply CFC.sqrt_unique _ (Matrix.PosSemidef.one.smul (Real.sqrt_nonneg 2)).nonneg
    calc
      _ = (Real.sqrt 2 * Real.sqrt 2) • (1 : Matrix ι ι ℝ) := by
        simp only [smul_mul_assoc, mul_smul_comm, one_mul, smul_smul]
      _ = _ := by rw [← pow_two, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [multivariateGaussian, hs]
  congr 1
  ext z
  simp

theorem doubled_gaussian_norm_law {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℝ) :
    (multivariateGaussian 0 ((2:ℝ) • (1 : Matrix ι ι ℝ))).map
      (fun z : EuclideanSpace ℝ ι => ‖z‖^2/c) =
    (stdGaussian (EuclideanSpace ℝ ι)).map (fun z => 2*‖z‖^2/c) := by
  rw [doubled_gaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  ext z
  dsimp only [Function.comp_def]
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

theorem overlap_eq_fidelity {d : ℕ} (truth h : PureVector d) :
    ⟪(pureParameter d truth).val,(pureParameter d h).val⟫_ℝ =
      pureMultilevelFidelity truth.val h.val := by
  rw [inner_eq_trace]
  exact (congrArg Complex.re
    (PureMultilevelLossConstants.pureProjectorFidelity_eq_trace truth.val h.val)).symm

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Both physical loss laws. The limiting standard Gaussian has `2*d`
coordinates, so its squared norm has the chi-square law in Corollary 5.4. -/
def Statement {d : ℕ} (truth : PureVector d) (h : ℕ → Ω → PureVector d) (μ : Measure Ω)
    [IsProbabilityMeasure μ] : Prop :=
  TendstoInDistribution
    (fun (n : ℕ) ω => (n:ℝ)*(1-pureMultilevelFidelity truth.val (h n ω).val))
    atTop (fun z : EuclideanSpace ℝ (TangentIndex d) => ‖z‖^2/2) (fun _ => μ)
    (stdGaussian (EuclideanSpace ℝ (TangentIndex d))) ∧
  TendstoInDistribution
    (fun (n : ℕ) ω => (n:ℝ)*‖(pureParameter d (h n ω)).val-(pureParameter d truth).val‖^2)
    atTop (fun z : EuclideanSpace ℝ (TangentIndex d) => ‖z‖^2) (fun _ => μ)
    (stdGaussian (EuclideanSpace ℝ (TangentIndex d)))

theorem of_amplitude_clt {d : ℕ} (truth : PureVector d)
    (h : ℕ → Ω → PureVector d)
    (hm : ∀ n, StronglyMeasurable (fun ω => (pureParameter d (h n ω)).val))
    (hc : ∀ᵐ ω ∂μ, Tendsto (fun n => (pureParameter d (h n ω)).val) atTop
      (𝓝 (pureParameter d truth).val))
    (hclt : TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt (n:ℝ) • amplitudeCoordinates truth (pureParameter d (h n ω)).val)
      atTop id (fun _ => μ)
      (multivariateGaussian 0 ((2:ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)))) :
    Statement truth h μ := by
  have hi := infidelity_clt_of_amplitude_clt truth h hm hc hclt
  have hf := frobenius_clt_of_amplitude_clt truth h hm hc hclt
  have h4 : (multivariateGaussian 0 ((2:ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))).map
      (fun z => ‖z‖^2/4) = (stdGaussian (EuclideanSpace ℝ (TangentIndex d))).map
      (fun z => ‖z‖^2/2) := by
    rw [doubled_gaussian_norm_law]
    congr 1
    ext z
    ring
  have h2 : (multivariateGaussian 0 ((2:ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ))).map
      (fun z => ‖z‖^2/2) = (stdGaussian (EuclideanSpace ℝ (TangentIndex d))).map
      (fun z => ‖z‖^2) := by
    rw [doubled_gaussian_norm_law]
    congr 1
    ext z
    ring
  constructor
  · simpa only [← overlap_eq_fidelity] using
      (show TendstoInDistribution
        (fun (n : ℕ) ω => (n:ℝ)*(1-⟪(pureParameter d truth).val,(pureParameter d (h n ω)).val⟫_ℝ))
        atTop (fun z : EuclideanSpace ℝ (TangentIndex d) => ‖z‖^2/2) (fun _ => μ)
        (stdGaussian (EuclideanSpace ℝ (TangentIndex d))) from
        ⟨hi.forall_aemeasurable, by fun_prop, by convert hi.tendsto using 1; simp only [h4]⟩)
  · exact ⟨hf.forall_aemeasurable, by fun_prop,
      by convert hf.tendsto using 1; simp only [h2]⟩

theorem povm {d : ℕ} {O : Type} [Fintype O]
    [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]
    (P : FinitePOVM (Fin (d+1)) O) (hI : GeneralPOVM.Identifying P)
    (hp : GeneralPOVM.Regular P) (hF : GeneralPOVM.FisherSymmetric P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    Statement truth
      (fun n path => TangentGLS.actualEstimate P hI hp regularization ridge hr hη batchSize path n)
      (adaptiveInfiniteTrajectoryMeasure
        (GeneralPOVM.adaptiveProtocol P hI regularization hr batchSize) truth) := by
  apply of_amplitude_clt
  · intro n
    exact FiniteHistoryStatistics.actualStatistic_stronglyMeasurable P hI regularization hr batchSize n
      (fun raw data => (pureParameter d
        (estimateFromRaw raw data (referenceFloor P) ridge (referenceFloor_pos P hp) hη)).val)
  · exact corrected_stronglyConsistent P hI hp truth regularization ridge hr hη batchSize
  · exact TangentGLS.amplitude_optimalVariance P hI hp hF truth regularization ridge hr hη batchSize hpositive

theorem phasePair {d : ℕ} {O : Type} [Fintype O]
    [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]
    (P : FinitePOVM (Fin (d+1)) O) (hI : GeneralPOVM.Identifying P)
    (hp : GeneralPOVM.Regular P) (hR : PhasePair.RankOne P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    Statement truth
      (fun n path => TangentGLS.actualEstimate (PhasePair.paired P) (PhasePair.paired_identifying P hI)
        (PhasePair.paired_regular P hp) regularization ridge hr hη batchSize path n)
      (adaptiveInfiniteTrajectoryMeasure
        (GeneralPOVM.adaptiveProtocol (PhasePair.paired P) (PhasePair.paired_identifying P hI)
          regularization hr batchSize) truth) :=
  povm (PhasePair.paired P) (PhasePair.paired_identifying P hI) (PhasePair.paired_regular P hp)
    (PhasePair.paired_fisher_of_rankOne P hp hR) truth regularization ridge hr hη batchSize hpositive

-- Section 5 proof route commented at the user request, 5 October 2026.
/-
theorem pvm [PVMPilotSchedule.Schedule] {d : ℕ} [PVMGeneralGeometry.ExplorationLibrary d]
    (truth : PureVector d) (ridge : ℝ) (hr : 0 < ridge)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) (hbudget : PVMPilotSchedule.OneStepBudget) :
    Statement truth (fun n path => PVMPilotGLS.actualEstimate ridge hr batchSize path n)
      (adaptiveInfiniteTrajectoryMeasure (PVMPilotAdaptive.adaptiveProtocol d batchSize) (pureParameter d truth)) := by
  apply of_amplitude_clt
  · intro n
    exact PVMPilotGLS.actualStatistic_stronglyMeasurable batchSize n
      (fun raw data => (pureParameter d
        (estimateFromRaw raw data (PVMPilotGLS.floor d) ridge (PVMPilotGLS.floor_pos d) hr)).val)
  · exact PVMPilotGLS.corrected_consistent truth ridge hr batchSize hpositive
  · exact PVMPilotGLS.amplitude_optimalVariance truth ridge hr batchSize hpositive hbudget

-/

end PureLossDistributions
end
end QubitOracle.AdaptiveDesign
