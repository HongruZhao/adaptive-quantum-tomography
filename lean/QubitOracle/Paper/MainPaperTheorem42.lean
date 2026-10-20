import QubitOracle.Paper.MainPaperPureLimits
import QubitOracle.AdaptiveDesign.TangentGLSSecondOrderCancellation

set_option autoImplicit false

/-! One complete exported endpoint for Theorem 4.2. `Inputs` contains
only the paper's deterministic apparatus, ridge and batch assumptions.
`Conclusions` contains the actual adaptive-process limits; none of its
fields is an input hypothesis. Copy indices in the implementation start
at zero; reported sample sizes are the completed batch boundaries. -/
namespace QubitOracle.Paper.MainPaperTheorem42
open QubitOracle QubitOracle.Paper QubitOracle.AdaptiveDesign
open GlobalPFSICHermitian PureMatrixController P2Adaptive TangentGLS GeneralPOVM
open Filter MeasureTheory ProbabilityTheory ProbabilityCalculus
open scoped Topology InnerProductSpace BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

local instance hermitianMeasurable (n : ℕ) : MeasurableSpace (HermitianSpace n) := borel _
local instance hermitianBorel (n : ℕ) : BorelSpace (HermitianSpace n) := ⟨rfl⟩

structure Inputs (d : ℕ) (O : Type) [Fintype O] where
  dimension_positive : 0 < d
  reference : FinitePOVM (Fin (d+1)) O
  identifying : Identifying reference
  regular : Regular reference
  rankOne : PhasePair.RankOne reference
  lambda : ℝ
  eta : ℝ
  lambda_positive : 0 < lambda
  eta_positive : 0 < eta
  batches : ℕ → ℕ
  batches_positive : ∀ j, 0 < batches j

variable {d : ℕ} {O : Type} [Fintype O]
  [MeasurableSpace O] [MeasurableSingletonClass O] [Nonempty O]

namespace Inputs
variable (A : Inputs d O)

abbrev paired := PhasePair.paired A.reference
abbrev pairedIdentifying := PhasePair.paired_identifying A.reference A.identifying
abbrev pairedRegular := PhasePair.paired_regular A.reference A.regular

def protocol := adaptiveProtocol A.paired A.pairedIdentifying A.lambda A.lambda_positive A.batches

def measure (truth : PureVector d) := adaptiveInfiniteTrajectoryMeasure A.protocol truth

instance measure_probability (truth : PureVector d) : IsProbabilityMeasure (A.measure truth) := by
  unfold measure
  infer_instance

def horizon := SequentialRidgeController.batchBoundary A.batches

def raw (path : AdaptiveInfinitePath (Bool × O)) (n : ℕ) : HermitianSpace (d+1) :=
  rawEstimator A.paired A.pairedIdentifying A.lambda A.lambda_positive A.batches path n

def preliminary (path : AdaptiveInfinitePath (Bool × O)) (n : ℕ) : HermitianSpace (d+1) :=
  (pureParameter d (actualPreliminary A.paired A.pairedIdentifying
    A.lambda A.lambda_positive A.batches path n)).val

def corrected (path : AdaptiveInfinitePath (Bool × O)) (n : ℕ) : HermitianSpace (d+1) :=
  (pureParameter d (actualEstimate A.paired A.pairedIdentifying A.pairedRegular
    A.lambda A.eta A.lambda_positive A.eta_positive A.batches path n)).val

def alignedRay (path : AdaptiveInfinitePath (Bool × O)) (n : ℕ) :=
  GlobalPFSIC.frameProjector
    (measurementFrame A.paired A.pairedIdentifying A.lambda A.lambda_positive A.batches path n)

def information (truth : PureVector d) (path : AdaptiveInfinitePath (Bool × O)) (n : ℕ) :=
  actualBornFisher A.paired truth
    (actualState A.paired A.pairedIdentifying A.lambda A.lambda_positive A.batches path n).action

end Inputs

/-- Every clause of the main theorem, with actual estimator definitions
and genuine smooth local coordinate changes at the fixed truth. -/
structure Conclusions (A : Inputs d O) (truth : PureVector d) : Prop where
  raw_consistent : ∀ᵐ path ∂A.measure truth,
    Tendsto (fun j => A.raw path (A.horizon j)) atTop (𝓝 (pureParameter d truth).val)
  preliminary_consistent : ∀ᵐ path ∂A.measure truth,
    Tendsto (fun j => A.preliminary path (A.horizon j)) atTop (𝓝 (pureParameter d truth).val)
  corrected_consistent : ∀ᵐ path ∂A.measure truth,
    Tendsto (fun j => A.corrected path (A.horizon j)) atTop (𝓝 (pureParameter d truth).val)
  alignment_consistent : ∀ᵐ path ∂A.measure truth,
    Tendsto (A.alignedRay path) atTop (𝓝 (rankOneDensity truth.val))
  conditional_information : ∀ᵐ path ∂A.measure truth,
    Tendsto (A.information truth path) atTop
      (𝓝 ((1/2 : ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)))
  average_information : ∀ᵐ path ∂A.measure truth, ∀ x y : TangentIndex d,
    Tendsto (fun j => (A.horizon j : ℝ)⁻¹ *
      ∑ t ∈ Finset.range (A.horizon j), A.information truth path t x y) atTop
      (𝓝 (((1/2 : ℝ) • (1 : Matrix (TangentIndex d) (TangentIndex d) ℝ)) x y))
  raw_root_rate : TightNorm (A.measure truth)
    (fun n path => Real.sqrt ((n+1 : ℕ) : ℝ) •
      (A.raw path (n+1)-(pureParameter d truth).val)) atTop
  preliminary_root_rate : TightNorm (A.measure truth)
    (fun n path => Real.sqrt ((n+1 : ℕ) : ℝ) •
      (A.preliminary path (n+1)-(pureParameter d truth).val)) atTop
  chart_normality : ∀ C : MainPaperPureCharts.SmoothCoordinates d,
    TendstoInDistribution
      (fun j path => Real.sqrt (A.horizon j : ℝ) •
        (C.extension (amplitudeCoordinates truth (A.corrected path (A.horizon j)))-C.change 0))
      atTop C.derivativeEquiv (fun _ => A.measure truth) (MainPaperPureLimits.gaussian d)
  chart_covariance : ∀ (C : MainPaperPureCharts.SmoothCoordinates d)
      (u v : MainPaperPureCharts.Coordinates d),
    covarianceBilin ((MainPaperPureLimits.gaussian d).map C.derivativeEquiv) u v =
      2 * ⟪u, PureChartCovariance.inverseQfiOperator C.derivativeEquiv v⟫_ℝ
  chart_sld_information : ∀ (C : MainPaperPureCharts.SmoothCoordinates d)
      (u v : MainPaperPureCharts.Coordinates d),
    PureSLDMetric.metricFromSLD truth
      (PureSLDMetric.normalizedLift truth (C.derivativeEquiv.symm u))
      (PureSLDMetric.normalizedLift truth (C.derivativeEquiv.symm v)) =
      ⟪u, PureChartCovariance.qfiOperator C.derivativeEquiv v⟫_ℝ
  ambient_normality : TendstoInDistribution
    (fun j path => Real.sqrt (A.horizon j : ℝ) •
      (A.corrected path (A.horizon j)-(pureParameter d truth).val))
    atTop (MainPaperPureLimits.tangentLift truth) (fun _ => A.measure truth)
    (MainPaperPureLimits.gaussian d)
  ambient_gaussian : IsGaussian (MainPaperPureLimits.limitLaw truth)
  ambient_centered : ∫ B, B ∂MainPaperPureLimits.limitLaw truth = 0
  ambient_tangent_support : ∀ᵐ B ∂MainPaperPureLimits.limitLaw truth, B ∈ tangentSpace truth
  ambient_covariance : ∀ B C : tangentSpace truth,
    covarianceBilin (MainPaperPureLimits.limitLaw truth) B.val C.val = ⟪B, C⟫_ℝ

theorem theorem_4_2 (A : Inputs d O) (truth : PureVector d) : Conclusions A truth := by
  have hN := MainPaperPureLimits.batch_horizons_tendsto A.batches A.batches_positive
  have hcons := GeneralPOVM.adaptive_consistency A.paired A.pairedIdentifying A.lambda
    A.lambda_positive truth A.batches A.batches_positive
  have hinfo := PhasePair.adaptive_actualBorn_information A.reference A.identifying A.regular
    A.rankOne A.lambda A.lambda_positive truth A.batches A.batches_positive
  refine {
    raw_consistent := ?_
    preliminary_consistent := ?_
    corrected_consistent := ?_
    alignment_consistent := ?_
    conditional_information := ?_
    average_information := ?_
    raw_root_rate := ?_
    preliminary_root_rate := ?_
    chart_normality := ?_
    chart_covariance := ?_
    chart_sld_information := ?_
    ambient_normality := ?_
    ambient_gaussian := MainPaperPureLimits.limitLaw_gaussian truth
    ambient_centered := MainPaperPureLimits.limitLaw_mean truth
    ambient_tangent_support := MainPaperPureLimits.limitLaw_tangent_support truth
    ambient_covariance := MainPaperPureLimits.limitLaw_tangent_covariance truth }
  · filter_upwards [hcons] with path hp
    exact hp.1.comp hN
  · filter_upwards [actualPreliminaryError_consistent A.paired A.pairedIdentifying A.lambda
      A.lambda_positive A.batches truth] with path hp
    exact (tendsto_sub_nhds_zero_iff.mp hp).comp hN
  · filter_upwards [corrected_stronglyConsistent A.paired A.pairedIdentifying A.pairedRegular
      truth A.lambda A.eta A.lambda_positive A.eta_positive A.batches] with path hp
    exact hp.comp hN
  · filter_upwards [hcons] with path hp
    exact hp.2.2
  · filter_upwards [hinfo] with path hp
    exact hp.2.2.1
  · filter_upwards [hinfo] with path hp
    intro x y
    exact (hp.2.2.2 x y).comp hN
  · exact GeneralPOVMRootRate.rawEstimator_rootTight A.paired A.pairedIdentifying
      A.lambda A.lambda_positive A.batches truth
  · exact actualPreliminaryError_rootTight A.paired A.pairedIdentifying truth
      A.lambda A.lambda_positive A.batches
  · intro C
    exact MainPaperPureLimits.phasePair_completed_chart_clt A.reference A.identifying A.regular
      A.rankOne truth A.lambda A.eta A.lambda_positive A.eta_positive A.batches A.batches_positive C
  · intro C u v
    exact PureChartCovariance.covariance_eq_twice_inverse_qfi C.derivativeEquiv u v
  · intro C u v
    exact C.parametrization_sld truth u v
  · exact MainPaperPureLimits.phasePair_completed_ambient_clt A.reference A.identifying A.regular
      A.rankOne truth A.lambda A.eta A.lambda_positive A.eta_positive A.batches A.batches_positive

end
end QubitOracle.Paper.MainPaperTheorem42
