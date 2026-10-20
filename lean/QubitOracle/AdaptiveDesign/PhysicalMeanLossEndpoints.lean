import QubitOracle.AdaptiveDesign.GeneralPOVMAdaptive
import QubitOracle.AdaptiveDesign.GeneralPOVMModel
import QubitOracle.AdaptiveDesign.GeneralPOVMTransport
import QubitOracle.AdaptiveDesign.GlobalPFSICBornModel
import QubitOracle.AdaptiveDesign.GlobalPFSICHermitianModel
import QubitOracle.AdaptiveDesign.P1BuresMeanLoss
import QubitOracle.AdaptiveDesign.P1ControllerBounds
import QubitOracle.AdaptiveDesign.P1WeightedBorn
import QubitOracle.AdaptiveDesign.P1WeightedController
import QubitOracle.AdaptiveDesign.P1WeightedPolicy
import QubitOracle.AdaptiveDesign.PhasePairPOVM
import QubitOracle.AdaptiveDesign.PureMatrixController
import QubitOracle.AdaptiveDesign.PurePOVMMeanLoss
import QubitOracle.AdaptiveDesign.QuantumFidelityBridges
import QubitOracle.AdaptiveDesign.TangentGLSEstimator
import QubitOracle.AdaptiveDesign.TangentGLSNormalizedError
import QubitOracle.FiniteGillMassar
import QubitOracle.Paper.AdaptiveTrajectoryExperiment
import QubitOracle.Paper.MixedProbabilityFloor
import QubitOracle.Paper.OneQubitBlochPhysicalState
import QubitOracle.Paper.OneQubitCyclicBornPath
import QubitOracle.Paper.OneQubitLabeledThreeAxisBornKernel
import QubitOracle.Paper.OneQubitMixedBuresFidelityLocalRemainder
import QubitOracle.Paper.PureMultilevelDeterministicGeometryClosed
import QubitOracle.Paper.PureMultilevelMatrixTraceDistance
import QubitOracle.Paper.QuantumDistances

/-! Expected-risk endpoints using the literal positive-matrix-square-root
Bures loss, rather than only its proved scalar representation. -/
namespace QubitOracle.AdaptiveDesign.PhysicalMeanLossEndpoints
open QubitOracle QubitOracle.Paper GlobalPFSICHermitian PureMatrixController P2Adaptive
open TangentGLS Filter MeasureTheory ProbabilityTheory P1Weighted
open PureMultilevelMatrixTraceDistance
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

theorem qubit_bures (theta eta : Fin 3 → ℝ)
    (ht : blochNormSq theta ≤ 1) (he : blochNormSq eta ≤ 1) :
    quantumBuresDistanceSq (blochFiniteDensityMatrix theta ht) (blochFiniteDensityMatrix eta he)=
      mixedQubitBlochBuresSqBetween theta eta := by
  simp only [quantumBuresDistanceSq,QuantumFidelityBridges.qubit_fidelity_bloch,
    mixedQubitBlochBuresSqBetween,mixedQubitBlochRootInfidelityBetween,
    mixedQubitBlochRootFidelityBetween,mixedQubitBlochFidelitySqBetween,
    Real.sqrt_mul (show 0 ≤ 1-blochNormSq theta by linarith)]

theorem controller_in_ball (loss : Loss) (n : ℕ) (x : Fin 3 → ℝ) :
    blochNormSq (controller loss n x) ≤ 1 := by
  rw [← bloch_norm_sq]
  have h := controller_norm_le_one loss n x
  nlinarith [norm_nonneg (WithLp.toLp 2 (controller loss n x))]

local instance physicalMean_measurable : MeasurableSpace LabeledBinaryOutcome := ⊤
local instance physicalMean_nonempty : Nonempty LabeledBinaryOutcome := ⟨(0,.plus)⟩

theorem mixed_bures_mean (ridge : ℝ) (hr : 0 < ridge)
    (refresh : ℕ → Bool) (hrefresh : ∀ K, ∃ n, K ≤ n ∧ refresh n=true)
    (truth : OneQubitPhysicalParameter) (htruth : blochNormSq truth.val < 1) :
    Tendsto (fun n : ℕ => (n:ℝ)*∫ path,
      quantumBuresDistanceSq (blochFiniteDensityMatrix truth.val htruth.le)
        (blochFiniteDensityMatrix (controller .bures n (estimate .bures ridge refresh n path))
          (controller_in_ball .bures n _))
      ∂adaptiveInfiniteTrajectoryMeasure (protocol (policy .bures ridge refresh)) truth)
      atTop (𝓝 (9/4:ℝ)) := by
  simpa only [qubit_bures] using bures_mean ridge hr refresh hrefresh truth htruth

def pureDensity {d : ℕ} (h : PureVector d) : FiniteDensityMatrix (Fin (d+1)) :=
  normalizedPureDensityMatrix h.val h.property

theorem pure_bures_loss {d : ℕ} (h g : PureVector d) :
    quantumBuresDistanceSq (pureDensity h) (pureDensity g)=
      PureMultilevelDeterministicGeometry.pureMultilevelBuresSq h.val g.val :=
  QuantumFidelityBridges.pure_bures h.val g.val h.property g.property

variable {d : ℕ} {O : Type} [Fintype O]
  [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]

theorem povm_bures_mean
    (P : FinitePOVM (Fin (d+1)) O) (hI : GeneralPOVM.Identifying P)
    (hp : GeneralPOVM.Regular P) (hF : GeneralPOVM.FisherSymmetric P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    Tendsto (fun n : ℕ => (n:ℝ)*∫ path,
      quantumBuresDistanceSq (pureDensity truth)
        (pureDensity (actualEstimate P hI hp regularization ridge hr hη batchSize path n))
      ∂adaptiveInfiniteTrajectoryMeasure (GeneralPOVM.adaptiveProtocol P hI regularization hr batchSize) truth)
      atTop (𝓝 (d:ℝ)) := by
  simpa only [pure_bures_loss] using
    (PurePOVMMeanLoss.povm P hI hp hF truth regularization ridge hr hη batchSize hpositive).2

theorem phasePair_bures_mean
    (P : FinitePOVM (Fin (d+1)) O) (hI : GeneralPOVM.Identifying P)
    (hp : GeneralPOVM.Regular P) (hR : PhasePair.RankOne P)
    (truth : PureVector d) (regularization ridge : ℝ) (hr : 0 < regularization) (hη : 0 < ridge)
    (batchSize : ℕ → ℕ) (hpositive : ∀ j, 0 < batchSize j) :
    let Q := PhasePair.paired P
    let hQI := PhasePair.paired_identifying P hI
    let hQp := PhasePair.paired_regular P hp
    Tendsto (fun n : ℕ => (n:ℝ)*∫ path,
      quantumBuresDistanceSq (pureDensity truth)
        (pureDensity (actualEstimate Q hQI hQp regularization ridge hr hη batchSize path n))
      ∂adaptiveInfiniteTrajectoryMeasure (GeneralPOVM.adaptiveProtocol Q hQI regularization hr batchSize) truth)
      atTop (𝓝 (d:ℝ)) :=
  povm_bures_mean (PhasePair.paired P) (PhasePair.paired_identifying P hI)
    (PhasePair.paired_regular P hp) (PhasePair.paired_fisher_of_rankOne P hp hR)
    truth regularization ridge hr hη batchSize hpositive


end
end QubitOracle.AdaptiveDesign.PhysicalMeanLossEndpoints
