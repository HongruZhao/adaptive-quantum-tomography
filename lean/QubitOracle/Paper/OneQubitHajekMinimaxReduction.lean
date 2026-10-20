import Mathlib

/-!
# Hájek scalar local-minimax contract and finite qubit reductions

## Citation boundary, awaiting user approval

Jaroslav Hájek, "Local Asymptotic Minimax and Admissibility in Estimation,"
*Proceedings of the Sixth Berkeley Symposium on Mathematical Statistics and
Probability*, Volume I (1972), pp. 175--194.

Source: Section 3, Assumption 3.1 (LAN), and Section 4, Theorem 4.2,
https://digicoll.lib.berkeley.edu/record/113183/files/math_s6_v1_article-11.pdf

Assumption 3.1 writes the local likelihood ratio at `t + h / sqrt n` as

`exp (h' Delta_n - (1/2) h' Gamma h + Z_n(h))`,

with `Delta_n` converging to `N(0, Gamma)`, `Z_n(h)` converging to zero in
`P_{n,t}`-probability for each fixed `h`, and `Gamma` positive definite.

Theorem 4.2 is stated, without proof, for an arbitrary sequence of estimators
of the first coordinate.  The other coordinates are nuisance parameters.  It
gives a scalar-loss lower bound over neighborhoods shrinking to the LAN truth.
It is not, as stated there, a vector quadratic-loss theorem.

Accordingly, `Hajek1972Theorem42AwaitingUserApproval` below is only a `Prop`
contract.  It has no inhabitant in this file, is not an axiom, and must not be
used as a cited theorem until the user approves the transcription against the
source.  The proved results in the second half of the file are only finite
algebraic summations of simultaneously supplied scalar inequalities.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

noncomputable section

universe u

/-! ## A general sequence of finite-dimensional experiments -/

/-- A finite-dimensional real parameter written in coordinates. -/
abbrev HajekParameter (D : Type*) := D -> Real

/-- A general sequence of experiments.  The sample space may depend on `n`;
the parameter set and its dimension remain fixed. -/
structure HajekExperimentSequence (D : Type*) [Fintype D] where
  Sample : Nat -> Type u
  measurableSpace : (n : Nat) -> MeasurableSpace (Sample n)
  parameterSet : Set (HajekParameter D)
  law : (n : Nat) -> HajekParameter D ->
    @Measure (Sample n) (measurableSpace n)
  probabilityMeasure : forall n theta,
    @IsProbabilityMeasure (Sample n) (measurableSpace n) (law n theta)

/-- Radon--Nikodym likelihood ratio of the absolutely continuous part, in
the convention used by Hájek immediately before equation (3.1). -/
def hajekLikelihoodRatio
    {D : Type*} [Fintype D]
    (E : HajekExperimentSequence D) (n : Nat)
    (theta truth : HajekParameter D) : E.Sample n -> Real := by
  letI : MeasurableSpace (E.Sample n) := E.measurableSpace n
  exact fun x => ((E.law n theta).rnDeriv (E.law n truth) x).toReal

/-- The root-`n` local parameter used in Assumption 3.1. -/
def hajekLocalParameter {D : Type*}
    (truth h : HajekParameter D) (n : Nat) : HajekParameter D :=
  fun i => truth i + (Real.sqrt (n : Real))⁻¹ * h i

/-- The quadratic form `h' Gamma h`. -/
def hajekQuadraticForm
    {D : Type*} [Fintype D]
    (Gamma : Matrix D D Real) (h : HajekParameter D) : Real :=
  dotProduct h (Gamma.mulVec h)

/-- Characteristic-function formulation of
`Delta_n -> N(0, Gamma)` under the truth law.  This avoids introducing an
additional external Gaussian-convergence declaration. -/
def HajekScoreConvergesToGaussian
    {D : Type*} [Fintype D]
    (E : HajekExperimentSequence D) (truth : HajekParameter D)
    (Gamma : Matrix D D Real)
    (score : (n : Nat) -> E.Sample n -> HajekParameter D) : Prop :=
  forall z : HajekParameter D,
    Tendsto
      (fun n =>
        letI : MeasurableSpace (E.Sample n) := E.measurableSpace n
        integral (E.law n truth)
          (fun x => Complex.exp
            (Complex.I *
              Complex.ofReal (dotProduct z (score n x)))))
      atTop
      (nhds (Complex.exp
        (-((hajekQuadraticForm Gamma z : Real) : Complex) / 2)))

/-- Pointwise-in-`h` convergence of the LAN remainder to zero in probability
under the truth law. -/
def HajekRemainderConvergesInProbability
    {D : Type*} [Fintype D]
    (E : HajekExperimentSequence D) (truth : HajekParameter D)
    (remainder : (n : Nat) -> HajekParameter D -> E.Sample n -> Real) :
    Prop :=
  forall h epsilon, 0 < epsilon ->
    Tendsto
      (fun n =>
        letI : MeasurableSpace (E.Sample n) := E.measurableSpace n
        E.law n truth {x | epsilon <= |remainder n h x|})
      atTop (nhds 0)

/-- Machine-readable data and obligations corresponding to Hájek's
Assumption 3.1.  This is ordinary structure data, not an axiom. -/
structure Hajek1972Assumption31LAN
    {D : Type*} [Fintype D] [DecidableEq D]
    (E : HajekExperimentSequence D) (truth : HajekParameter D) where
  truth_mem : truth ∈ E.parameterSet
  information : Matrix D D Real
  information_posDef : information.PosDef
  score : (n : Nat) -> E.Sample n -> HajekParameter D
  score_measurable : forall n i,
    letI : MeasurableSpace (E.Sample n) := E.measurableSpace n
    Measurable (fun x => score n x i)
  remainder : (n : Nat) -> HajekParameter D -> E.Sample n -> Real
  remainder_measurable : forall n h,
    letI : MeasurableSpace (E.Sample n) := E.measurableSpace n
    Measurable (remainder n h)
  local_parameter_eventually_mem : forall h,
    exists N, forall n, N <= n ->
      hajekLocalParameter truth h n ∈ E.parameterSet
  likelihood_ratio_expansion : forall h,
    exists N, forall n, N <= n -> forall x,
      hajekLikelihoodRatio E n (hajekLocalParameter truth h n) truth x =
        Real.exp
          (dotProduct h (score n x) -
            (1 / 2 : Real) * hajekQuadraticForm information h +
            remainder n h x)
  score_converges :
    HajekScoreConvergesToGaussian E truth information score
  remainder_converges :
    HajekRemainderConvergesInProbability E truth remainder

/-! ## Exact scalar-risk scope of Theorem 4.2 -/

/-- A measurable scalar estimator sequence for the first coordinate. -/
structure HajekScalarEstimator
    {D : Type*} [Fintype D] (E : HajekExperimentSequence D) where
  value : (n : Nat) -> E.Sample n -> Real
  measurable : forall n,
    letI : MeasurableSpace (E.Sample n) := E.measurableSpace n
    Measurable (value n)

/-- Conservative machine-readable form of the scalar symmetric bowl-loss
conditions referenced by Hájek as (2.1)--(2.4): pointwise finiteness,
measurability, symmetry, and monotonicity in absolute distance.  This package,
like the theorem contract below, remains subject to user comparison with the
original typography. -/
structure Hajek1972ScalarLossConditions (loss : Real -> ENNReal) : Prop where
  finite : forall x, loss x ≠ top
  measurable : Measurable loss
  symmetric : forall x, loss (-x) = loss x
  monotone_radius : forall x y, |x| <= |y| -> loss x <= loss y

/-- Risk of one scalar first-coordinate estimator at one parameter. -/
def hajekScalarRisk
    {D : Type*} [Fintype D]
    (E : HajekExperimentSequence D)
    (first : D) (loss : Real -> ENNReal)
    (T : HajekScalarEstimator E) (n : Nat)
    (theta : HajekParameter D) : ENNReal := by
  letI : MeasurableSpace (E.Sample n) := E.measurableSpace n
  exact lintegral (E.law n theta)
    (fun x => loss
      (Real.sqrt (n : Real) * (T.value n x - theta first)))

/-- Worst scalar risk over the source's fixed-radius neighborhood of the LAN
truth.  The function-space norm is the finite-coordinate supremum norm. -/
def hajekLocalWorstScalarRisk
    {D : Type*} [Fintype D] [Nonempty D]
    (E : HajekExperimentSequence D)
    (truth : HajekParameter D) (first : D)
    (loss : Real -> ENNReal) (T : HajekScalarEstimator E)
    (delta : Real) (n : Nat) : ENNReal :=
  iSup fun theta : {theta : HajekParameter D //
      theta ∈ E.parameterSet ∧
        ‖theta - truth‖ < delta} =>
    hajekScalarRisk E first loss T n theta.1

/-- The order `delta down to zero` after `liminf n`, matching (4.14).
Writing the monotone outer limit as an infimum over all positive radii avoids
adding a separate existence-of-limit premise. -/
def hajekShrinkingNeighborhoodScalarRisk
    {D : Type*} [Fintype D] [Nonempty D]
    (E : HajekExperimentSequence D)
    (truth : HajekParameter D) (first : D)
    (loss : Real -> ENNReal) (T : HajekScalarEstimator E) : ENNReal :=
  iInf fun delta : {delta : Real // 0 < delta} =>
    Filter.liminf
      (fun n => hajekLocalWorstScalarRisk
        E truth first loss T delta.1 n)
      atTop

/-- The right side of (4.14), written as an integral against the standard
normal density with scalar standard deviation `sigma`. -/
def hajekGaussianScalarRisk
    (loss : Real -> ENNReal) (sigma : Real) : ENNReal :=
  lintegral volume
    (fun y : Real =>
      loss (sigma * y) *
        ENNReal.ofReal
          ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2)))

/-- The first-coordinate Gaussian standard deviation from `Gamma⁻¹`. -/
def hajekFirstCoordinateSigma
    {D : Type*} [Fintype D] [DecidableEq D]
    {E : HajekExperimentSequence D} {truth : HajekParameter D}
    (lan : Hajek1972Assumption31LAN E truth) (first : D) : Real :=
  Real.sqrt (lan.information⁻¹ first first)

/-- **Awaiting user approval of the historical transcription.**

This proposition is the exact trust boundary used by this file for Hájek
(1972), Theorem 4.2.  It quantifies over every measurable estimator sequence,
but only for the chosen first coordinate and scalar loss.  An arbitrary
direction requires a separately justified coordinate change and LAN
certificate.  No declaration in this file proves or inhabits this `Prop`. -/
def Hajek1972Theorem42AwaitingUserApproval
    {D : Type*} [Fintype D] [DecidableEq D] [Nonempty D]
    (E : HajekExperimentSequence D) (truth : HajekParameter D)
    (lan : Hajek1972Assumption31LAN E truth)
    (first : D) (loss : Real -> ENNReal) : Prop :=
  Hajek1972ScalarLossConditions loss ∧
    forall T : HajekScalarEstimator E,
      hajekGaussianScalarRisk loss
          (hajekFirstCoordinateSigma lan first) <=
        hajekShrinkingNeighborhoodScalarRisk
          E truth first loss T

/-! ## Deterministic finite-coordinate qubit reductions -/

/-- A standard coordinate direction. -/
def hajekStandardCoordinateDirection
    {D : Type*} [DecidableEq D] (i : D) : D -> Real :=
  fun j => if j = i then 1 else 0

/-- The standard coordinate family is orthonormal. -/
theorem hajekStandardCoordinateDirection_dot
    {D : Type*} [Fintype D] [DecidableEq D]
    (i j : D) :
    dotProduct (hajekStandardCoordinateDirection i)
        (hajekStandardCoordinateDirection j) =
      if i = j then 1 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simp [dotProduct, hajekStandardCoordinateDirection]
  · rw [if_neg hij]
    unfold dotProduct
    apply Finset.sum_eq_zero
    intro x _
    by_cases hxi : x = i
    · subst x
      simp [hajekStandardCoordinateDirection, hij]
    · simp [hajekStandardCoordinateDirection, hxi]

/-- Scalar Gaussian quadratic benchmark in direction `v`. -/
def hajekDirectionalQuadraticBenchmark
    {D : Type*} [Fintype D]
    (Sigma : Matrix D D Real) (v : D -> Real) : Real :=
  dotProduct v (Sigma.mulVec v)

/-- A standard-coordinate directional benchmark is the corresponding
diagonal covariance entry. -/
theorem hajekDirectionalQuadraticBenchmark_standardCoordinate
    {D : Type*} [Fintype D] [DecidableEq D]
    (Sigma : Matrix D D Real) (i : D) :
    hajekDirectionalQuadraticBenchmark Sigma
        (hajekStandardCoordinateDirection i) = Sigma i i := by
  classical
  simp [hajekDirectionalQuadraticBenchmark,
    hajekStandardCoordinateDirection, dotProduct, Matrix.mulVec]

/-- The trace is the finite sum of the scalar benchmarks along the standard
orthonormal coordinate family. -/
theorem hajekTrace_eq_sum_standardCoordinateQuadratics
    {D : Type*} [Fintype D] [DecidableEq D]
    (Sigma : Matrix D D Real) :
    Matrix.trace Sigma =
      ∑ i, 
        hajekDirectionalQuadraticBenchmark Sigma
          (hajekStandardCoordinateDirection i) := by
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  exact (hajekDirectionalQuadraticBenchmark_standardCoordinate Sigma i).symm

/-- Pointwise quadratic mixed-qubit Bloch loss in the three standard Bloch
coordinates. -/
def mixedFinThreeBlochQuadraticLoss (error : Fin 3 -> Real) : Real :=
  ∑ i, error i ^ 2

/-- Its coordinate contributions. -/
def mixedFinThreeBlochCoordinateLoss
    (i : Fin 3) (error : Fin 3 -> Real) : Real :=
  error i ^ 2

theorem mixedFinThreeBlochQuadraticLoss_eq_sum_coordinates
    (error : Fin 3 -> Real) :
    mixedFinThreeBlochQuadraticLoss error =
      ∑ i, mixedFinThreeBlochCoordinateLoss i error := by
  rfl

/-- A common-law mixed quadratic risk assembled from its three expected
coordinate contributions.  This is deliberately not a supremum or liminf. -/
def mixedFinThreeBlochSummedCoordinateRisk
    (coordinateRisk : Fin 3 -> Real) : Real :=
  ∑ i, coordinateRisk i

/-- Concrete mixed-qubit reduction.  Three simultaneous scalar directional
bounds sum to the covariance-trace lower bound.  No vector lower bound is a
premise. -/
theorem mixedFinThreeBloch_trace_lower_bound_reduction
    (Sigma : Matrix (Fin 3) (Fin 3) Real)
    (coordinateRisk : Fin 3 -> Real)
    (hscalar : forall i,
      hajekDirectionalQuadraticBenchmark Sigma
          (hajekStandardCoordinateDirection i) <= coordinateRisk i) :
    Matrix.trace Sigma <=
      mixedFinThreeBlochSummedCoordinateRisk coordinateRisk := by
  unfold mixedFinThreeBlochSummedCoordinateRisk
  rw [hajekTrace_eq_sum_standardCoordinateQuadratics]
  exact Finset.sum_le_sum (fun i _ => hscalar i)

/-- Pointwise local pure-state Bures quadratic loss in the rank-one tangent
`k` convention: `(1/4) * (k_0^2 + k_1^2)`. -/
def pureFinTwoBuresQuadraticLoss (error : Fin 2 -> Real) : Real :=
  (1 / 4 : Real) * ∑ i, error i ^ 2

/-- The corresponding common-law sum of two expected coordinate losses. -/
def pureFinTwoBuresSummedCoordinateRisk
    (coordinateRisk : Fin 2 -> Real) : Real :=
  (1 / 4 : Real) * ∑ i, coordinateRisk i

/-- Concrete pure-qubit reduction.  The scalar coordinate bounds give the
rank-one/Bures quadratic trace benchmark `(1/4) trace Sigma`. -/
theorem pureFinTwoBures_trace_lower_bound_reduction
    (Sigma : Matrix (Fin 2) (Fin 2) Real)
    (coordinateRisk : Fin 2 -> Real)
    (hscalar : forall i,
      hajekDirectionalQuadraticBenchmark Sigma
          (hajekStandardCoordinateDirection i) <= coordinateRisk i) :
    (1 / 4 : Real) * Matrix.trace Sigma <=
      pureFinTwoBuresSummedCoordinateRisk coordinateRisk := by
  have hsum : Matrix.trace Sigma <= ∑ i, coordinateRisk i := by
    rw [hajekTrace_eq_sum_standardCoordinateQuadratics]
    exact Finset.sum_le_sum (fun i _ => hscalar i)
  unfold pureFinTwoBuresSummedCoordinateRisk
  exact mul_le_mul_of_nonneg_left hsum (by norm_num)

/-!
Scope warning: The two reduction theorems above concern simultaneous scalar
inequalities for coordinate contributions to one additive, common-law risk.
Hájek's Theorem 4.2 by itself supplies separate scalar neighborhood-worst-risk
bounds.  In general, a supremum of a sum is not the sum of the separate
suprema, and a liminf does not commute with that operation for free.
Consequently this file proves no theorem that applies
`Hajek1972Theorem42AwaitingUserApproval` directly to either summed qubit risk.
A later statistical argument must provide a common Bayes/localization device,
or another source theorem with vector bowl-shaped loss, before that final
minimax trace conclusion is justified.
-/

end

end QubitOracle.Paper
