import QubitOracle.Paper.OneQubitHajekMinimaxReduction
import QubitOracle.Paper.OneQubitMixedPolynomialOrdinaryInfidelityEndpoint
import QubitOracle.Paper.OneQubitMixedFrozenPolynomialEndpointCore
import QubitOracle.Paper.OneQubitPureFidelityRiskEndpoints
import QubitOracle.Paper.OneQubitDesignOptimality

/-!
# Concrete one-qubit local-minimax reduction

This file isolates the remaining literature boundary from the estimator
attainment calculations.

The lower bound uses only

* an explicit LAN conclusion for the frozen experiment, including its inverse
  information matrix; and
* `ExactLANLocalMinimaxQuadraticTransfer`, a `Prop`-valued contract for the
  external LAN-to-local-asymptotic-minimax theorem for nonnegative subconvex
  quadratic-limit losses.

The contract is not an axiom and is not inhabited here.  It is the exact
citation boundary that must be approved and supplied from a local asymptotic
minimax theorem.  In particular, no MLE efficiency statement occurs in the
lower-bound route.

The concrete mixed and pure risk theorems currently available are fixed-truth
attainment statements.  Accordingly, the final structures below deliberately
record a universal local lower bound and fixed-truth attainment as separate
fields.  They do not silently claim the still stronger uniform shrinking-
neighborhood upper bound.

All concrete endpoints are for the frozen complete-block two-stage qubit
protocol: `Fin 3` for an interior mixed qubit and `Fin 2` for the north-pole
pure-qubit tangent chart.  Nothing here states a continuing-adaptive or an
arbitrary-dimensional quantum theorem.
-/

open scoped BigOperators ENNReal Topology
open Filter MeasureTheory

namespace QubitOracle.Paper

noncomputable section

/-! ## Nonnegative subconvex coordinate-quadratic limit losses -/

/-- A finite-dimensional diagonal quadratic-limit loss.  Nonnegative weights
are enough to prove nonnegativity and the Jensen (hence subconvex-sublevel)
property used by the local asymptotic minimax transfer. -/
structure NonnegativeCoordinateQuadraticLimitLoss
    (D : Type*) [Fintype D] where
  weight : D → ℝ
  weight_nonnegative : ∀ i, 0 ≤ weight i

/-- The real quadratic-limit loss represented by diagonal coordinate weights. -/
def coordinateQuadraticLimitLoss
    {D : Type*} [Fintype D]
    (L : NonnegativeCoordinateQuadraticLimitLoss D)
    (x : D → ℝ) : ℝ :=
  ∑ i, L.weight i * x i ^ 2

/-- Every represented coordinate-quadratic loss is nonnegative. -/
theorem coordinateQuadraticLimitLoss_nonnegative
    {D : Type*} [Fintype D]
    (L : NonnegativeCoordinateQuadraticLimitLoss D)
    (x : D → ℝ) :
    0 ≤ coordinateQuadraticLimitLoss L x := by
  unfold coordinateQuadraticLimitLoss
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (L.weight_nonnegative i) (sq_nonneg (x i))

/-- A concrete algebraic formulation of the subconvex condition: the loss is
convex on every line segment.  This is stronger than convexity of all sublevel
sets. -/
def IsNonnegativeSubconvexQuadraticLimitLoss
    {D : Type*} [Fintype D]
    (L : NonnegativeCoordinateQuadraticLimitLoss D) : Prop :=
  (∀ x : D → ℝ, 0 ≤ coordinateQuadraticLimitLoss L x) ∧
    ∀ (x y : D → ℝ) (t : ℝ), 0 ≤ t → t ≤ 1 →
      coordinateQuadraticLimitLoss L
          (fun i => t * x i + (1 - t) * y i) ≤
        t * coordinateQuadraticLimitLoss L x +
          (1 - t) * coordinateQuadraticLimitLoss L y

/-- The finite-coordinate square identity proves the required subconvex
certificate without a literature premise. -/
theorem coordinateQuadraticLimitLoss_isNonnegativeSubconvex
    {D : Type*} [Fintype D]
    (L : NonnegativeCoordinateQuadraticLimitLoss D) :
    IsNonnegativeSubconvexQuadraticLimitLoss L := by
  refine ⟨coordinateQuadraticLimitLoss_nonnegative L, ?_⟩
  intro x y t ht0 ht1
  unfold coordinateQuadraticLimitLoss
  calc
    (∑ i, L.weight i * (t * x i + (1 - t) * y i) ^ 2) ≤
        ∑ i, (t * (L.weight i * x i ^ 2) +
          (1 - t) * (L.weight i * y i ^ 2)) := by
      apply Finset.sum_le_sum
      intro i hi
      have htOne : 0 ≤ 1 - t := sub_nonneg.mpr ht1
      have hSquare : 0 ≤ (x i - y i) ^ 2 := sq_nonneg (x i - y i)
      have hGap :
          0 ≤ L.weight i * (t * (1 - t) * (x i - y i) ^ 2) :=
        mul_nonneg (L.weight_nonnegative i)
          (mul_nonneg (mul_nonneg ht0 htOne) hSquare)
      nlinarith
    _ = t * (∑ i, L.weight i * x i ^ 2) +
        (1 - t) * (∑ i, L.weight i * y i ^ 2) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]

/-- For a centered Gaussian limit with covariance `covariance`, the expected
value of a diagonal quadratic loss is the weighted diagonal trace. -/
def coordinateGaussianQuadraticBenchmark
    {D : Type*} [Fintype D]
    (L : NonnegativeCoordinateQuadraticLimitLoss D)
    (covariance : Matrix D D ℝ) : ℝ :=
  ∑ i, L.weight i * covariance i i

/-! ## Exact vector local-risk functional -/

/-- An arbitrary sequence of vector estimators for a Hájek experiment.  The
external transfer contract below quantifies over every such map; no MLE or
regular-estimator restriction is inserted here. -/
structure HajekVectorEstimator
    {D : Type*} [Fintype D]
    (E : HajekExperimentSequence D) where
  estimate : ∀ n, E.Sample n → HajekParameter D

/-- Root-sample-size quadratic risk at the local parameter
`truth + h / sqrt(n+1)`.  The `n+1` indexing makes the zero-row convention
explicit and avoids division by zero. -/
noncomputable def hajekLocalQuadraticRisk
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : HajekExperimentSequence D)
    (truth : HajekParameter D)
    (L : NonnegativeCoordinateQuadraticLimitLoss D)
    (T : HajekVectorEstimator E)
    (n : ℕ) (h : HajekParameter D) : ℝ≥0∞ := by
  let m : ℕ := n + 1
  letI : MeasurableSpace (E.Sample m) := E.measurableSpace m
  exact ∫⁻ x,
    ENNReal.ofReal
      (coordinateQuadraticLimitLoss L
        (fun i => Real.sqrt (m : ℝ) *
          (T.estimate m x i - hajekLocalParameter truth h m i)))
      ∂E.law m (hajekLocalParameter truth h m)

/-- Worst local risk over a finite coordinate cube, restricted to local
parameters belonging to the experiment parameter set. -/
noncomputable def hajekLocalWorstQuadraticRisk
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : HajekExperimentSequence D)
    (truth : HajekParameter D)
    (L : NonnegativeCoordinateQuadraticLimitLoss D)
    (T : HajekVectorEstimator E)
    (radius : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ⨆ h : HajekParameter D,
    ⨆ (_hBound : ∀ i, |h i| ≤ radius),
      ⨆ (_hParameter : hajekLocalParameter truth h (n + 1) ∈ E.parameterSet),
        hajekLocalQuadraticRisk E truth L T n h

/-- `sup_radius liminf_n` of the local worst risks.  The original parameter
neighborhoods shrink at the `1/sqrt(n+1)` scale through
`hajekLocalParameter`. -/
noncomputable def hajekShrinkingNeighborhoodQuadraticRisk
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : HajekExperimentSequence D)
    (truth : HajekParameter D)
    (L : NonnegativeCoordinateQuadraticLimitLoss D)
    (T : HajekVectorEstimator E) : ℝ≥0∞ :=
  ⨆ radius : ℕ,
    ⨆ N : ℕ,
      ⨅ n : {n : ℕ // N ≤ n},
        hajekLocalWorstQuadraticRisk E truth L T
          ((radius : ℝ) + 1) n.1

/-! ## The sole external local-minimax transfer boundary -/

/-- Exact external theorem contract needed by this file.

Given the already formalized LAN conclusion, it transfers every nonnegative
subconvex finite-coordinate quadratic-limit loss to the all-estimator local
asymptotic lower bound with covariance `information⁻¹`.

This is a parameter, not an axiom.  It is intentionally stronger than the
scalar-coordinate-only Hájek contract already encoded in
`OneQubitHajekMinimaxReduction`; that scalar contract alone cannot justify
summing suprema into a common vector-loss minimax bound.  An approved source
must match this vector/subconvex scope exactly (Hájek 1972, Section 3,
Assumption 3.1 and Theorem 4.2, or an explicitly approved later formulation). -/
structure ExactLANLocalMinimaxQuadraticTransfer
    {D : Type*} [Fintype D] [DecidableEq D] [Nonempty D]
    (E : HajekExperimentSequence D)
    (truth : HajekParameter D)
    (lan : Hajek1972Assumption31LAN E truth) : Prop where
  lower_bound :
    ∀ (L : NonnegativeCoordinateQuadraticLimitLoss D)
      (T : HajekVectorEstimator E),
      ENNReal.ofReal
          (coordinateGaussianQuadraticBenchmark L lan.information⁻¹) ≤
        hajekShrinkingNeighborhoodQuadraticRisk E truth L T

/-- The concrete LAN conclusion required by a frozen qubit specialization.
Besides Assumption 3.1, it identifies the LAN information and its inverse in
the chosen local coordinates. -/
structure FrozenQubitLANConclusion
    {D : Type*} [Fintype D] [DecidableEq D] [Nonempty D]
    (E : HajekExperimentSequence D)
    (truth : HajekParameter D)
    (information covariance : Matrix D D ℝ) where
  lan : Hajek1972Assumption31LAN E truth
  information_eq : lan.information = information
  inverse_information_eq : lan.information⁻¹ = covariance

/-! ## Concrete mixed and pure Gaussian pairs -/

/-- Equal three-axis allocation in Bures-whitened mixed-qubit coordinates has
per-observation information `(1/3) I₃`. -/
def mixedFrozenOracleInformation : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => if i = j then (1 / 3 : ℝ) else 0

/-- Its root-total-shot Gaussian covariance is `3 I₃`. -/
def mixedFrozenOracleCovariance : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => if i = j then (3 : ℝ) else 0

/-- In the paper's pure `k` tangent chart, the equal two-axis design has
per-observation information `(1/2) I₂`. -/
def pureFrozenOracleInformation : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = j then (1 / 2 : ℝ) else 0

/-- Its root-total-shot Gaussian covariance is `2 I₂`.  This is the `k`-chart
normalization, not the stereographic `u`-chart normalization. -/
def pureFrozenOracleCovariance : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = j then (2 : ℝ) else 0

/-- Squared Bures and ordinary infidelity have the same local quadratic term,
`(1/4) ||h||²`, in the frozen whitened coordinates. -/
def buresQuadraticLimitLossData
    (D : Type*) [Fintype D] :
    NonnegativeCoordinateQuadraticLimitLoss D where
  weight := fun _ => (1 / 4 : ℝ)
  weight_nonnegative := by
    intro i
    norm_num

/-- Ordinary infidelity has the same second-order limit loss as squared Bures. -/
abbrev ordinaryInfidelityQuadraticLimitLossData
    (D : Type*) [Fintype D] :
    NonnegativeCoordinateQuadraticLimitLoss D :=
  buresQuadraticLimitLossData D

/-- Root infidelity `1 - sqrt(F)` is exactly one half of squared Bures, so its
local quadratic weight is `1/8`. -/
def rootInfidelityQuadraticLimitLossData
    (D : Type*) [Fintype D] :
    NonnegativeCoordinateQuadraticLimitLoss D where
  weight := fun _ => (1 / 8 : ℝ)
  weight_nonnegative := by
    intro i
    norm_num

/-- The mixed Bures Gaussian benchmark is exactly `9/4`. -/
theorem mixedFrozenBuresGaussianBenchmark_eq_nine_fourths :
    coordinateGaussianQuadraticBenchmark
        (buresQuadraticLimitLossData (Fin 3))
        mixedFrozenOracleCovariance = 9 / 4 := by
  norm_num [coordinateGaussianQuadraticBenchmark,
    buresQuadraticLimitLossData, mixedFrozenOracleCovariance,
    Fin.sum_univ_succ]

/-- The pure tangent Bures Gaussian benchmark is exactly `1`. -/
theorem pureFrozenBuresGaussianBenchmark_eq_one :
    coordinateGaussianQuadraticBenchmark
        (buresQuadraticLimitLossData (Fin 2))
        pureFrozenOracleCovariance = 1 := by
  norm_num [coordinateGaussianQuadraticBenchmark,
    buresQuadraticLimitLossData, pureFrozenOracleCovariance,
    Fin.sum_univ_succ]

/-- Exact mixed root-infidelity benchmark, separated by loss scaling. -/
theorem mixedFrozenRootInfidelityGaussianBenchmark_eq_nine_eighths :
    coordinateGaussianQuadraticBenchmark
        (rootInfidelityQuadraticLimitLossData (Fin 3))
        mixedFrozenOracleCovariance = 9 / 8 := by
  norm_num [coordinateGaussianQuadraticBenchmark,
    rootInfidelityQuadraticLimitLossData, mixedFrozenOracleCovariance,
    Fin.sum_univ_succ]

/-- Exact pure root-infidelity benchmark, separated by loss scaling. -/
theorem pureFrozenRootInfidelityGaussianBenchmark_eq_one_half :
    coordinateGaussianQuadraticBenchmark
        (rootInfidelityQuadraticLimitLossData (Fin 2))
        pureFrozenOracleCovariance = 1 / 2 := by
  norm_num [coordinateGaussianQuadraticBenchmark,
    rootInfidelityQuadraticLimitLossData, pureFrozenOracleCovariance,
    Fin.sum_univ_succ]

/-- The mixed LAN package in Bures-whitened `Fin 3` coordinates. -/
abbrev FrozenMixedQubitLANConclusion
    (E : HajekExperimentSequence (Fin 3))
    (truth : HajekParameter (Fin 3)) :=
  FrozenQubitLANConclusion E truth
    mixedFrozenOracleInformation mixedFrozenOracleCovariance

/-- The pure LAN package in the paper's `Fin 2` tangent `k` coordinates. -/
abbrev FrozenPureQubitLANConclusion
    (E : HajekExperimentSequence (Fin 2))
    (truth : HajekParameter (Fin 2)) :=
  FrozenQubitLANConclusion E truth
    pureFrozenOracleInformation pureFrozenOracleCovariance

/-! ## Lower bound plus concrete attainment, without an MLE premise -/

/-- Honest reduction object used by the paper-facing statements.

`universal_local_lower_bound` is the minimax lower-bound conclusion for every
estimator.  `concrete_fixed_truth_attainment` is exactly the scope proved by the
current finite estimator endpoint.  A future uniform-local attainment theorem
may strengthen the second field, but is not assumed here. -/
structure FrozenTwoStageConditionalLocalMinimaxBenchmarkReduction
    {D : Type*} [Fintype D] [DecidableEq D] [Nonempty D]
    (E : HajekExperimentSequence D)
    (truth : HajekParameter D)
    (lan : Hajek1972Assumption31LAN E truth)
    (L : NonnegativeCoordinateQuadraticLimitLoss D)
    (concreteRisk : ℕ → ℝ≥0∞)
    (constant : ℝ) : Prop where
  constant_nonnegative : 0 ≤ constant
  gaussian_benchmark_eq :
    coordinateGaussianQuadraticBenchmark L lan.information⁻¹ = constant
  universal_local_lower_bound :
    ∀ T : HajekVectorEstimator E,
      ENNReal.ofReal constant ≤
        hajekShrinkingNeighborhoodQuadraticRisk E truth L T
  concrete_fixed_truth_attainment :
    Tendsto concreteRisk atTop (nhds (ENNReal.ofReal constant))

/-- Generic constructor: the lower-bound field is obtained only from the LAN
transfer contract, while attainment is supplied independently by the concrete
estimator theorem. -/
theorem frozenTwoStageConditionalLocalMinimaxBenchmarkReduction_of_transfer
    {D : Type*} [Fintype D] [DecidableEq D] [Nonempty D]
    {E : HajekExperimentSequence D}
    {truth : HajekParameter D}
    {information covariance : Matrix D D ℝ}
    (C : FrozenQubitLANConclusion E truth information covariance)
    (transfer : ExactLANLocalMinimaxQuadraticTransfer E truth C.lan)
    (L : NonnegativeCoordinateQuadraticLimitLoss D)
    (concreteRisk : ℕ → ℝ≥0∞)
    (constant : ℝ)
    (hBenchmark :
      coordinateGaussianQuadraticBenchmark L C.lan.information⁻¹ = constant)
    (hConstant : 0 ≤ constant)
    (hAttainment :
      Tendsto concreteRisk atTop (nhds (ENNReal.ofReal constant))) :
    FrozenTwoStageConditionalLocalMinimaxBenchmarkReduction
      E truth C.lan L concreteRisk constant := by
  refine
    { constant_nonnegative := hConstant
      gaussian_benchmark_eq := hBenchmark
      universal_local_lower_bound := ?_
      concrete_fixed_truth_attainment := hAttainment }
  intro T
  rw [← hBenchmark]
  exact transfer.lower_bound L T

/-- Concrete mixed total-observation squared-Bures risk sequence. -/
noncomputable abbrev mixedFrozenSquaredBuresRisk
    (theta b : RLSVector 3) : ℕ → ℝ≥0∞ :=
  mixedPolynomialTotalObservationScaledExpectedExactBuresRisk theta b

/-- Concrete mixed total-observation ordinary-infidelity risk sequence. -/
noncomputable abbrev mixedFrozenOrdinaryInfidelityRisk
    (theta b : RLSVector 3) : ℕ → ℝ≥0∞ :=
  mixedPolynomialTotalObservationScaledExpectedOrdinaryInfidelityRisk theta b

/-- Concrete mixed total-observation root-infidelity risk sequence. -/
noncomputable abbrev mixedFrozenRootInfidelityRisk
    (theta b : RLSVector 3) : ℕ → ℝ≥0∞ :=
  mixedPolynomialTotalObservationScaledExpectedRootInfidelityRisk theta b

/-- Concrete pure total-shot squared-Bures risk, embedded in `ENNReal`. -/
noncomputable abbrev pureFrozenSquaredBuresRisk : ℕ → ℝ≥0∞ :=
  fun q => ENNReal.ofReal (pureLinearScaledExpectedSquaredBuresRisk q)

/-- Concrete pure total-shot ordinary-infidelity risk, embedded in `ENNReal`. -/
noncomputable abbrev pureFrozenOrdinaryInfidelityRisk : ℕ → ℝ≥0∞ :=
  fun q => ENNReal.ofReal (pureLinearScaledExpectedOrdinaryInfidelityRisk q)

/-- Concrete pure total-shot root-infidelity risk, embedded in `ENNReal`. -/
noncomputable abbrev pureFrozenRootInfidelityRisk : ℕ → ℝ≥0∞ :=
  fun q => ENNReal.ofReal (pureLinearScaledExpectedRootInfidelityRisk q)

/-- Conditional mixed squared-Bures local-minimax benchmark reduction with
constant `9/4`. -/
theorem mixedConcreteSquaredBuresConditionalLocalMinimaxReduction
    {E : HajekExperimentSequence (Fin 3)}
    {truth : HajekParameter (Fin 3)}
    (C : FrozenMixedQubitLANConclusion E truth)
    (transfer : ExactLANLocalMinimaxQuadraticTransfer E truth C.lan)
    (theta b : RLSVector 3)
    (h : MixedFrozenPolynomialEndpointConditions theta b) :
    FrozenTwoStageConditionalLocalMinimaxBenchmarkReduction
      E truth C.lan (buresQuadraticLimitLossData (Fin 3))
      (mixedFrozenSquaredBuresRisk theta b) (9 / 4) := by
  apply frozenTwoStageConditionalLocalMinimaxBenchmarkReduction_of_transfer
    C transfer
  · calc
      coordinateGaussianQuadraticBenchmark
          (buresQuadraticLimitLossData (Fin 3)) C.lan.information⁻¹ =
          coordinateGaussianQuadraticBenchmark
            (buresQuadraticLimitLossData (Fin 3))
            mixedFrozenOracleCovariance := by
              rw [C.inverse_information_eq]
      _ = 9 / 4 := mixedFrozenBuresGaussianBenchmark_eq_nine_fourths
  · norm_num
  · exact
      mixedPolynomialTotalObservationScaledExpectedExactBuresRisk_tendsto_nine_fourths
        theta b h.positive h.interior h.seed h.physical h.hoeffding

/-- Conditional mixed ordinary-infidelity reduction.  Its local quadratic loss
is the same as squared Bures, and the separate concrete endpoint attains
`9/4`. -/
theorem mixedConcreteOrdinaryInfidelityConditionalLocalMinimaxReduction
    {E : HajekExperimentSequence (Fin 3)}
    {truth : HajekParameter (Fin 3)}
    (C : FrozenMixedQubitLANConclusion E truth)
    (transfer : ExactLANLocalMinimaxQuadraticTransfer E truth C.lan)
    (theta b : RLSVector 3)
    (h : MixedFrozenPolynomialEndpointConditions theta b) :
    FrozenTwoStageConditionalLocalMinimaxBenchmarkReduction
      E truth C.lan (ordinaryInfidelityQuadraticLimitLossData (Fin 3))
      (mixedFrozenOrdinaryInfidelityRisk theta b) (9 / 4) := by
  apply frozenTwoStageConditionalLocalMinimaxBenchmarkReduction_of_transfer
    C transfer
  · calc
      coordinateGaussianQuadraticBenchmark
          (ordinaryInfidelityQuadraticLimitLossData (Fin 3))
          C.lan.information⁻¹ =
          coordinateGaussianQuadraticBenchmark
            (buresQuadraticLimitLossData (Fin 3))
            mixedFrozenOracleCovariance := by
              rw [C.inverse_information_eq]
      _ = 9 / 4 := mixedFrozenBuresGaussianBenchmark_eq_nine_fourths
  · norm_num
  · exact
      mixedPolynomialTotalObservationScaledExpectedOrdinaryInfidelityRisk_tendsto_nine_fourths
        theta b h.positive h.interior h.seed h.physical h.hoeffding

/-- The mixed root-infidelity constant is separately `9/8`, obtained from its
exact half-Bures local loss and its exact concrete endpoint. -/
theorem mixedConcreteRootInfidelityConditionalLocalMinimaxReduction
    {E : HajekExperimentSequence (Fin 3)}
    {truth : HajekParameter (Fin 3)}
    (C : FrozenMixedQubitLANConclusion E truth)
    (transfer : ExactLANLocalMinimaxQuadraticTransfer E truth C.lan)
    (theta b : RLSVector 3)
    (h : MixedFrozenPolynomialEndpointConditions theta b) :
    FrozenTwoStageConditionalLocalMinimaxBenchmarkReduction
      E truth C.lan (rootInfidelityQuadraticLimitLossData (Fin 3))
      (mixedFrozenRootInfidelityRisk theta b) (9 / 8) := by
  apply frozenTwoStageConditionalLocalMinimaxBenchmarkReduction_of_transfer
    C transfer
  · calc
      coordinateGaussianQuadraticBenchmark
          (rootInfidelityQuadraticLimitLossData (Fin 3))
          C.lan.information⁻¹ =
          coordinateGaussianQuadraticBenchmark
            (rootInfidelityQuadraticLimitLossData (Fin 3))
            mixedFrozenOracleCovariance := by
              rw [C.inverse_information_eq]
      _ = 9 / 8 :=
        mixedFrozenRootInfidelityGaussianBenchmark_eq_nine_eighths
  · norm_num
  · exact
      mixedPolynomialTotalObservationScaledExpectedRootInfidelityRisk_tendsto_nine_eighths
        theta b h.positive h.interior h.seed h.physical h.hoeffding

/-- Conditional pure tangent squared-Bures local-minimax benchmark reduction
with constant `1`. -/
theorem pureConcreteSquaredBuresConditionalLocalMinimaxReduction
    {E : HajekExperimentSequence (Fin 2)}
    {truth : HajekParameter (Fin 2)}
    (C : FrozenPureQubitLANConclusion E truth)
    (transfer : ExactLANLocalMinimaxQuadraticTransfer E truth C.lan) :
    FrozenTwoStageConditionalLocalMinimaxBenchmarkReduction
      E truth C.lan (buresQuadraticLimitLossData (Fin 2))
      pureFrozenSquaredBuresRisk 1 := by
  apply frozenTwoStageConditionalLocalMinimaxBenchmarkReduction_of_transfer
    C transfer
  · calc
      coordinateGaussianQuadraticBenchmark
          (buresQuadraticLimitLossData (Fin 2)) C.lan.information⁻¹ =
          coordinateGaussianQuadraticBenchmark
            (buresQuadraticLimitLossData (Fin 2))
            pureFrozenOracleCovariance := by
              rw [C.inverse_information_eq]
      _ = 1 := pureFrozenBuresGaussianBenchmark_eq_one
  · norm_num
  · simpa [pureFrozenSquaredBuresRisk, Function.comp_def] using
      (ENNReal.continuous_ofReal.tendsto (1 : ℝ)).comp
        pureLinearScaledExpectedSquaredBuresRisk_tendsto_one

/-- Conditional pure tangent ordinary-infidelity reduction with constant `1`. -/
theorem pureConcreteOrdinaryInfidelityConditionalLocalMinimaxReduction
    {E : HajekExperimentSequence (Fin 2)}
    {truth : HajekParameter (Fin 2)}
    (C : FrozenPureQubitLANConclusion E truth)
    (transfer : ExactLANLocalMinimaxQuadraticTransfer E truth C.lan) :
    FrozenTwoStageConditionalLocalMinimaxBenchmarkReduction
      E truth C.lan (ordinaryInfidelityQuadraticLimitLossData (Fin 2))
      pureFrozenOrdinaryInfidelityRisk 1 := by
  apply frozenTwoStageConditionalLocalMinimaxBenchmarkReduction_of_transfer
    C transfer
  · calc
      coordinateGaussianQuadraticBenchmark
          (ordinaryInfidelityQuadraticLimitLossData (Fin 2))
          C.lan.information⁻¹ =
          coordinateGaussianQuadraticBenchmark
            (buresQuadraticLimitLossData (Fin 2))
            pureFrozenOracleCovariance := by
              rw [C.inverse_information_eq]
      _ = 1 := pureFrozenBuresGaussianBenchmark_eq_one
  · norm_num
  · simpa [pureFrozenOrdinaryInfidelityRisk, Function.comp_def] using
      (ENNReal.continuous_ofReal.tendsto (1 : ℝ)).comp
        pureLinearScaledExpectedOrdinaryInfidelityRisk_tendsto_one

/-- The pure root-infidelity constant is separately `1/2`. -/
theorem pureConcreteRootInfidelityConditionalLocalMinimaxReduction
    {E : HajekExperimentSequence (Fin 2)}
    {truth : HajekParameter (Fin 2)}
    (C : FrozenPureQubitLANConclusion E truth)
    (transfer : ExactLANLocalMinimaxQuadraticTransfer E truth C.lan) :
    FrozenTwoStageConditionalLocalMinimaxBenchmarkReduction
      E truth C.lan (rootInfidelityQuadraticLimitLossData (Fin 2))
      pureFrozenRootInfidelityRisk (1 / 2) := by
  apply frozenTwoStageConditionalLocalMinimaxBenchmarkReduction_of_transfer
    C transfer
  · calc
      coordinateGaussianQuadraticBenchmark
          (rootInfidelityQuadraticLimitLossData (Fin 2))
          C.lan.information⁻¹ =
          coordinateGaussianQuadraticBenchmark
            (rootInfidelityQuadraticLimitLossData (Fin 2))
            pureFrozenOracleCovariance := by
              rw [C.inverse_information_eq]
      _ = 1 / 2 := pureFrozenRootInfidelityGaussianBenchmark_eq_one_half
  · norm_num
  · simpa [pureFrozenRootInfidelityRisk, Function.comp_def] using
      (ENNReal.continuous_ofReal.tendsto (1 / 2 : ℝ)).comp
        pureLinearScaledExpectedRootInfidelityRisk_tendsto_one_half

/-! ## Paper-facing frozen-qubit labels -/

namespace Label

/-- Mixed frozen two-stage qubit reduction: Bures and ordinary infidelity have
benchmark `9/4`; root infidelity has benchmark `9/8`. -/
theorem thm_concrete_mixed_local_minimax_reduction_qubit
    {E : HajekExperimentSequence (Fin 3)}
    {truth : HajekParameter (Fin 3)}
    (C : FrozenMixedQubitLANConclusion E truth)
    (transfer : ExactLANLocalMinimaxQuadraticTransfer E truth C.lan)
    (theta b : RLSVector 3)
    (h : MixedFrozenPolynomialEndpointConditions theta b) :
    FrozenTwoStageConditionalLocalMinimaxBenchmarkReduction
        E truth C.lan (buresQuadraticLimitLossData (Fin 3))
        (mixedFrozenSquaredBuresRisk theta b) (9 / 4) ∧
      FrozenTwoStageConditionalLocalMinimaxBenchmarkReduction
        E truth C.lan (ordinaryInfidelityQuadraticLimitLossData (Fin 3))
        (mixedFrozenOrdinaryInfidelityRisk theta b) (9 / 4) ∧
      FrozenTwoStageConditionalLocalMinimaxBenchmarkReduction
        E truth C.lan (rootInfidelityQuadraticLimitLossData (Fin 3))
        (mixedFrozenRootInfidelityRisk theta b) (9 / 8) :=
  ⟨mixedConcreteSquaredBuresConditionalLocalMinimaxReduction
      C transfer theta b h,
    mixedConcreteOrdinaryInfidelityConditionalLocalMinimaxReduction
      C transfer theta b h,
    mixedConcreteRootInfidelityConditionalLocalMinimaxReduction
      C transfer theta b h⟩

/-- Pure frozen two-tangent-axis qubit reduction: Bures and ordinary
infidelity have benchmark `1`; root infidelity has benchmark `1/2`. -/
theorem thm_concrete_pure_local_minimax_reduction_qubit
    {E : HajekExperimentSequence (Fin 2)}
    {truth : HajekParameter (Fin 2)}
    (C : FrozenPureQubitLANConclusion E truth)
    (transfer : ExactLANLocalMinimaxQuadraticTransfer E truth C.lan) :
    FrozenTwoStageConditionalLocalMinimaxBenchmarkReduction
        E truth C.lan (buresQuadraticLimitLossData (Fin 2))
        pureFrozenSquaredBuresRisk 1 ∧
      FrozenTwoStageConditionalLocalMinimaxBenchmarkReduction
        E truth C.lan (ordinaryInfidelityQuadraticLimitLossData (Fin 2))
        pureFrozenOrdinaryInfidelityRisk 1 ∧
      FrozenTwoStageConditionalLocalMinimaxBenchmarkReduction
        E truth C.lan (rootInfidelityQuadraticLimitLossData (Fin 2))
        pureFrozenRootInfidelityRisk (1 / 2) :=
  ⟨pureConcreteSquaredBuresConditionalLocalMinimaxReduction C transfer,
    pureConcreteOrdinaryInfidelityConditionalLocalMinimaxReduction C transfer,
    pureConcreteRootInfidelityConditionalLocalMinimaxReduction C transfer⟩

end Label

end

end QubitOracle.Paper
