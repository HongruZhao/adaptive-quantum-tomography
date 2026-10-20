import QubitOracle.Paper.MainPaperTheorem42
import QubitOracle.AdaptiveDesign.PhysicalMeanLossEndpoints

set_option autoImplicit false

/-! Combined completed-batch endpoints for Corollaries 5.2 and 5.3.
The Bures distance is the actual matrix-square-root loss. Its argument
order is the paper's estimate-first order, justified by symmetry below.
No moment or local-unbiasedness hypothesis is added. -/
namespace QubitOracle.Paper.MainPaperMeanLosses
open QubitOracle QubitOracle.Paper QubitOracle.AdaptiveDesign
open GlobalPFSICHermitian PureMatrixController P2Adaptive TangentGLS P1Weighted
open Filter MeasureTheory ProbabilityTheory
open scoped Topology InnerProductSpace BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

local instance : MeasurableSpace LabeledBinaryOutcome := ⊤
local instance : Nonempty LabeledBinaryOutcome := ⟨(0, .plus)⟩
local instance hermitianMeasurable (n : ℕ) : MeasurableSpace (HermitianSpace n) := borel _
local instance hermitianBorel (n : ℕ) : BorelSpace (HermitianSpace n) := ⟨rfl⟩

theorem qubit_bures_comm (rho sigma : FiniteDensityMatrix (Fin 2)) :
    quantumBuresDistanceSq rho sigma = quantumBuresDistanceSq sigma rho := by
  unfold quantumBuresDistanceSq
  rw [QuantumFidelityBridges.qubit_fidelity_trace_det,
    QuantumFidelityBridges.qubit_fidelity_trace_det, Matrix.trace_mul_comm,
    mul_comm rho.val.det.re sigma.val.det.re]

theorem pure_bures_comm {d : ℕ} (h g : PureVector d) :
    quantumBuresDistanceSq (PhysicalMeanLossEndpoints.pureDensity h)
      (PhysicalMeanLossEndpoints.pureDensity g) =
    quantumBuresDistanceSq (PhysicalMeanLossEndpoints.pureDensity g)
      (PhysicalMeanLossEndpoints.pureDensity h) := by
  rw [PhysicalMeanLossEndpoints.pure_bures_loss, PhysicalMeanLossEndpoints.pure_bures_loss]
  have he : PureMultilevelDeterministicGeometry.pureMultilevelFidelity h.val g.val =
      PureMultilevelDeterministicGeometry.pureMultilevelFidelity g.val h.val := by
    apply Complex.ofReal_injective
    rw [PureMultilevelDeterministicGeometry.pureMultilevelFidelity_eq_rankOneTrace,
      PureMultilevelDeterministicGeometry.pureMultilevelFidelity_eq_rankOneTrace,
      Matrix.trace_mul_comm]
  simp only [PureMultilevelDeterministicGeometry.pureMultilevelBuresSq,
    PureMultilevelDeterministicGeometry.pureMultilevelRootFidelity, he]

def mixedOutput (loss : Loss) (ridge : ℝ) (m : ℕ → ℕ) (n : ℕ) (path : Path) :
    FiniteDensityMatrix (Fin 2) :=
  blochFiniteDensityMatrix (controller loss n (estimate loss ridge (P1.batchRefresh m) n path))
    (PhysicalMeanLossEndpoints.controller_in_ball loss n _)

theorem corollary_5_2 (ridge : ℝ) (hr : 0 < ridge)
    (m : ℕ → ℕ) (hm : ∀ j, 0 < m j)
    (truth : OneQubitPhysicalParameter) (htruth : blochNormSq truth.val < 1) :
    Tendsto (fun j : ℕ => (P1.batchEndpoint m j : ℝ) * ∫ path,
      quantumBuresDistanceSq (mixedOutput .bures ridge m (P1.batchEndpoint m j) path)
        (blochFiniteDensityMatrix truth.val htruth.le)
      ∂adaptiveInfiniteTrajectoryMeasure (protocol (policy .bures ridge (P1.batchRefresh m))) truth)
      atTop (𝓝 (9/4 : ℝ)) ∧
    Tendsto (fun j : ℕ => (P1.batchEndpoint m j : ℝ) * ∫ path,
      qubitFrobeniusLoss truth.val
        (controller .frobenius (P1.batchEndpoint m j)
          (estimate .frobenius ridge (P1.batchRefresh m) (P1.batchEndpoint m j) path))
      ∂adaptiveInfiniteTrajectoryMeasure (protocol (policy .frobenius ridge (P1.batchRefresh m))) truth)
      atTop (𝓝 ((2+mixedRadialGap truth.val)^2/2)) := by
  have hN := (P1.batchEndpoint_strictMono m hm).tendsto_atTop
  constructor
  · have hb := (PhysicalMeanLossEndpoints.mixed_bures_mean ridge hr (P1.batchRefresh m)
      (P1.batchRefresh_unbounded m hm) truth htruth).comp hN
    have he (n : ℕ) (path : Path) :
        quantumBuresDistanceSq (blochFiniteDensityMatrix truth.val htruth.le)
          (mixedOutput .bures ridge m n path) =
        quantumBuresDistanceSq (mixedOutput .bures ridge m n path)
          (blochFiniteDensityMatrix truth.val htruth.le) := qubit_bures_comm _ _
    change Tendsto (fun j : ℕ => (P1.batchEndpoint m j : ℝ) * ∫ path,
      quantumBuresDistanceSq (blochFiniteDensityMatrix truth.val htruth.le)
        (mixedOutput .bures ridge m (P1.batchEndpoint m j) path)
      ∂adaptiveInfiniteTrajectoryMeasure (protocol (policy .bures ridge (P1.batchRefresh m))) truth)
      atTop (𝓝 (9/4 : ℝ)) at hb
    simpa only [he] using hb
  · exact (frobenius_mean ridge hr (P1.batchRefresh m) (P1.batchRefresh_unbounded m hm)
      truth htruth).comp hN

variable {d : ℕ} {O : Type} [Fintype O]
  [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]

def pureOutput (A : MainPaperTheorem42.Inputs d O)
    (path : AdaptiveInfinitePath (Bool × O)) (n : ℕ) : FiniteDensityMatrix (Fin (d+1)) :=
  PhysicalMeanLossEndpoints.pureDensity
    (actualEstimate A.paired A.pairedIdentifying A.pairedRegular A.lambda A.eta
      A.lambda_positive A.eta_positive A.batches path n)

theorem corollary_5_3 (A : MainPaperTheorem42.Inputs d O) (truth : PureVector d) :
    Tendsto (fun j : ℕ => (A.horizon j : ℝ) * ∫ path,
      quantumBuresDistanceSq (pureOutput A path (A.horizon j))
        (PhysicalMeanLossEndpoints.pureDensity truth) ∂A.measure truth)
      atTop (𝓝 (d : ℝ)) ∧
    Tendsto (fun j : ℕ => (A.horizon j : ℝ) * ∫ path,
      ‖A.corrected path (A.horizon j)-(pureParameter d truth).val‖^2 ∂A.measure truth)
      atTop (𝓝 (2*(d : ℝ))) := by
  have hN := MainPaperPureLimits.batch_horizons_tendsto A.batches A.batches_positive
  constructor
  · have hb := (PhysicalMeanLossEndpoints.phasePair_bures_mean A.reference A.identifying A.regular
      A.rankOne truth A.lambda A.eta A.lambda_positive A.eta_positive A.batches A.batches_positive).comp hN
    have he (n : ℕ) (path : AdaptiveInfinitePath (Bool × O)) :
        quantumBuresDistanceSq (PhysicalMeanLossEndpoints.pureDensity truth) (pureOutput A path n) =
        quantumBuresDistanceSq (pureOutput A path n) (PhysicalMeanLossEndpoints.pureDensity truth) :=
      pure_bures_comm truth _
    change Tendsto (fun j : ℕ => (A.horizon j : ℝ) * ∫ path,
      quantumBuresDistanceSq (PhysicalMeanLossEndpoints.pureDensity truth)
        (pureOutput A path (A.horizon j)) ∂A.measure truth) atTop (𝓝 (d : ℝ)) at hb
    simpa only [he] using hb
  · exact (PurePOVMMeanLoss.phasePair A.reference A.identifying A.regular A.rankOne truth A.lambda A.eta
      A.lambda_positive A.eta_positive A.batches A.batches_positive).1.comp hN

end
end QubitOracle.Paper.MainPaperMeanLosses
