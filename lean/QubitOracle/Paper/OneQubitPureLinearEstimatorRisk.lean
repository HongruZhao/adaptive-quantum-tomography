import QubitOracle.Paper.OneQubitPureBuresFidelityRiskTransfer
import QubitOracle.Paper.OneQubitDesignOptimality
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration

/-!
# Exact risk of the two-axis pure-qubit linear estimator

For each of the two canonical tangent Pauli axes, take `q > 0` independent
measurements at the north-pole pure truth.  Every outcome is fair and is
represented by a sign in `{-1, +1}`.  The coordinate estimator is the sample
mean of the `q` signs on that axis.

This file uses a finite product space indexed by `Fin 2 × Fin q`; it is
independent of the quarantined infinite-product source candidate.  It proves
exactly:

* zero coordinate means;
* coordinate variance `1 / q`;
* zero cross-covariance from product-coordinate independence;
* with total shots `N = 2 q`, scaled expected quadratic loss
  `(1 / 4) * ||error||^2` equal to one;
* exact equality of chart infidelity and the quadratic loss;
* the existing nonnegative fourth-order remainder for squared Bures loss.

No finite-sample equality between squared Bures loss and its quadratic term is
claimed: the former has the rigorously retained positive remainder.
-/

open scoped BigOperators ENNReal MeasureTheory

noncomputable section

namespace QubitOracle.Paper.OneQubitPureLinearEstimatorRisk

/-- Boolean outcome represented as the real sign used by this finite model. -/
def pureLinearBoolSign : Bool → ℝ
  | false => -1
  | true => 1

/-- One shot is identified by its tangent Pauli axis and its replicate. -/
abbrev PureLinearShotIndex (q : ℕ) := Fin 2 × Fin q

/-- Complete finite outcome table for `q` shots on each of two axes. -/
abbrev PureLinearSampleSpace (q : ℕ) := PureLinearShotIndex q → Bool

/-- The fair one-shot Born measure at the north-pole pure truth. -/
def pureLinearFairBoolMeasure : MeasureTheory.Measure Bool :=
  (2 : ℝ≥0∞)⁻¹ • MeasureTheory.Measure.dirac false +
    (2 : ℝ≥0∞)⁻¹ • MeasureTheory.Measure.dirac true

noncomputable instance pureLinearHalfDiracFalse_isFiniteMeasure :
    MeasureTheory.IsFiniteMeasure
      ((2 : ℝ≥0∞)⁻¹ • MeasureTheory.Measure.dirac false) :=
  ⟨by simp⟩

noncomputable instance pureLinearHalfDiracTrue_isFiniteMeasure :
    MeasureTheory.IsFiniteMeasure
      ((2 : ℝ≥0∞)⁻¹ • MeasureTheory.Measure.dirac true) :=
  ⟨by simp⟩

noncomputable instance pureLinearFairBoolMeasure_isProbabilityMeasure :
    MeasureTheory.IsProbabilityMeasure pureLinearFairBoolMeasure where
  measure_univ := by
    norm_num [pureLinearFairBoolMeasure]
    rw [← two_mul]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

/-- The finite independent product law for all `2q` outcomes. -/
def pureLinearSampleMeasure (q : ℕ) :
    MeasureTheory.Measure (PureLinearSampleSpace q) :=
  MeasureTheory.Measure.infinitePi
    (fun _ : PureLinearShotIndex q => pureLinearFairBoolMeasure)

noncomputable instance pureLinearSampleMeasure_isProbabilityMeasure (q : ℕ) :
    MeasureTheory.IsProbabilityMeasure (pureLinearSampleMeasure q) := by
  unfold pureLinearSampleMeasure
  infer_instance

/-- A Boolean measurement outcome represented as the real Pauli sign. -/
def pureLinearShot
    (q : ℕ) (index : PureLinearShotIndex q)
    (omega : PureLinearSampleSpace q) : ℝ :=
  pureLinearBoolSign (omega index)

theorem pureLinearShot_measurable
    (q : ℕ) (index : PureLinearShotIndex q) :
    Measurable (pureLinearShot q index) := by
  exact (measurable_of_finite pureLinearBoolSign).comp
    (measurable_pi_apply index)

/-- Every product coordinate has the fair one-shot law. -/
theorem pureLinearCoordinate_map
    (q : ℕ) (index : PureLinearShotIndex q) :
    MeasureTheory.Measure.map
        (fun omega : PureLinearSampleSpace q => omega index)
        (pureLinearSampleMeasure q) =
      pureLinearFairBoolMeasure := by
  simpa [pureLinearSampleMeasure] using
    (MeasureTheory.Measure.infinitePi_map_eval
      (fun _ : PureLinearShotIndex q => pureLinearFairBoolMeasure) index)

/-- The real Pauli sign has mean zero under the fair one-shot law. -/
theorem pureLinearFairBool_sign_mean_zero :
    (∫ b, pureLinearBoolSign b
      ∂pureLinearFairBoolMeasure) = 0 := by
  change
    (∫ b, pureLinearBoolSign b
      ∂((2 : ℝ≥0∞)⁻¹ • MeasureTheory.Measure.dirac false +
        (2 : ℝ≥0∞)⁻¹ • MeasureTheory.Measure.dirac true)) = 0
  rw [MeasureTheory.integral_add_measure
    (MeasureTheory.Integrable.of_finite)
    (MeasureTheory.Integrable.of_finite)]
  norm_num [pureLinearBoolSign]

/-- The real Pauli sign has exact second moment one. -/
theorem pureLinearFairBool_sign_secondMoment_one :
    (∫ b, (pureLinearBoolSign b) ^ 2
      ∂pureLinearFairBoolMeasure) = 1 := by
  change
    (∫ b, (pureLinearBoolSign b) ^ 2
      ∂((2 : ℝ≥0∞)⁻¹ • MeasureTheory.Measure.dirac false +
        (2 : ℝ≥0∞)⁻¹ • MeasureTheory.Measure.dirac true)) = 1
  rw [MeasureTheory.integral_add_measure
    (MeasureTheory.Integrable.of_finite)
    (MeasureTheory.Integrable.of_finite)]
  norm_num [pureLinearBoolSign]

/-- Every individual shot has mean zero under the finite product law. -/
theorem pureLinearShot_mean_zero
    (q : ℕ) (index : PureLinearShotIndex q) :
    (∫ omega, pureLinearShot q index omega
      ∂pureLinearSampleMeasure q) = 0 := by
  calc
    (∫ omega, pureLinearShot q index omega
        ∂pureLinearSampleMeasure q) =
        ∫ b, pureLinearBoolSign b
          ∂MeasureTheory.Measure.map
            (fun omega : PureLinearSampleSpace q => omega index)
            (pureLinearSampleMeasure q) := by
      symm
      exact MeasureTheory.integral_map
        (measurable_pi_apply index).aemeasurable
        (measurable_of_finite
          pureLinearBoolSign).aestronglyMeasurable
    _ = ∫ b, pureLinearBoolSign b
          ∂pureLinearFairBoolMeasure := by
      rw [pureLinearCoordinate_map]
    _ = 0 := pureLinearFairBool_sign_mean_zero

/-- Every individual shot has second moment one. -/
theorem pureLinearShot_secondMoment_one
    (q : ℕ) (index : PureLinearShotIndex q) :
    (∫ omega, (pureLinearShot q index omega) ^ 2
      ∂pureLinearSampleMeasure q) = 1 := by
  calc
    (∫ omega, (pureLinearShot q index omega) ^ 2
        ∂pureLinearSampleMeasure q) =
        ∫ b, (pureLinearBoolSign b) ^ 2
          ∂MeasureTheory.Measure.map
            (fun omega : PureLinearSampleSpace q => omega index)
            (pureLinearSampleMeasure q) := by
      symm
      exact MeasureTheory.integral_map
        (measurable_pi_apply index).aemeasurable
        (measurable_of_finite
          (fun b => (pureLinearBoolSign b) ^ 2)).aestronglyMeasurable
    _ = ∫ b, (pureLinearBoolSign b) ^ 2
          ∂pureLinearFairBoolMeasure := by
      rw [pureLinearCoordinate_map]
    _ = 1 := pureLinearFairBool_sign_secondMoment_one

/-- All `2q` real shot variables are mutually independent. -/
theorem pureLinearShots_iIndepFun (q : ℕ) :
    ProbabilityTheory.iIndepFun
      (fun index : PureLinearShotIndex q => pureLinearShot q index)
      (pureLinearSampleMeasure q) := by
  change ProbabilityTheory.iIndepFun
    (fun index omega => pureLinearBoolSign (omega index))
    (MeasureTheory.Measure.infinitePi
      (fun _ : PureLinearShotIndex q => pureLinearFairBoolMeasure))
  exact ProbabilityTheory.iIndepFun_infinitePi
    (P := fun _ : PureLinearShotIndex q => pureLinearFairBoolMeasure)
    (X := fun _ : PureLinearShotIndex q => pureLinearBoolSign)
    (fun _ => measurable_of_finite pureLinearBoolSign)

/-- The exact two-shot cross moment: one on the diagonal, zero off it.  The
off-diagonal equality is obtained from product-coordinate independence. -/
theorem pureLinearShot_crossMoment
    (q : ℕ) (a b : PureLinearShotIndex q) :
    (∫ omega, pureLinearShot q a omega * pureLinearShot q b omega
      ∂pureLinearSampleMeasure q) = if a = b then 1 else 0 := by
  by_cases hab : a = b
  · subst b
    rw [if_pos rfl]
    simpa [pow_two] using pureLinearShot_secondMoment_one q a
  · rw [if_neg hab]
    have hindependent : ProbabilityTheory.IndepFun
        (pureLinearShot q a) (pureLinearShot q b)
        (pureLinearSampleMeasure q) :=
      (pureLinearShots_iIndepFun q).indepFun hab
    calc
      (∫ omega, pureLinearShot q a omega * pureLinearShot q b omega
          ∂pureLinearSampleMeasure q) =
          (∫ omega, pureLinearShot q a omega
            ∂pureLinearSampleMeasure q) *
          (∫ omega, pureLinearShot q b omega
            ∂pureLinearSampleMeasure q) :=
        hindependent.integral_mul_eq_mul_integral
          (pureLinearShot_measurable q a).aestronglyMeasurable
          (pureLinearShot_measurable q b).aestronglyMeasurable
      _ = 0 := by
        rw [pureLinearShot_mean_zero, pureLinearShot_mean_zero]
        ring

/-- Integration commutes with a finite shot sum because the sample space is
finite. -/
theorem pureLinear_integral_sum
    {q : ℕ} (f : Fin q → PureLinearSampleSpace q → ℝ) :
    (∫ omega, ∑ shot : Fin q, f shot omega
      ∂pureLinearSampleMeasure q) =
      ∑ shot : Fin q,
        ∫ omega, f shot omega ∂pureLinearSampleMeasure q := by
  simpa using
    (MeasureTheory.integral_finsetSum
      (μ := pureLinearSampleMeasure q) Finset.univ
      (fun _shot _hshot => MeasureTheory.Integrable.of_finite))

/-- The analogous identity for a double finite shot sum. -/
theorem pureLinear_integral_doubleSum
    {q : ℕ}
    (f : Fin q → Fin q → PureLinearSampleSpace q → ℝ) :
    (∫ omega, ∑ first : Fin q, ∑ second : Fin q,
        f first second omega ∂pureLinearSampleMeasure q) =
      ∑ first : Fin q, ∑ second : Fin q,
        ∫ omega, f first second omega
          ∂pureLinearSampleMeasure q := by
  calc
    (∫ omega, ∑ first : Fin q, ∑ second : Fin q,
        f first second omega ∂pureLinearSampleMeasure q) =
        ∑ first : Fin q,
          ∫ omega, ∑ second : Fin q, f first second omega
            ∂pureLinearSampleMeasure q :=
      pureLinear_integral_sum
        (fun first omega => ∑ second : Fin q, f first second omega)
    _ = ∑ first : Fin q, ∑ second : Fin q,
        ∫ omega, f first second omega
          ∂pureLinearSampleMeasure q := by
      apply Finset.sum_congr rfl
      intro first _hfirst
      exact pureLinear_integral_sum (fun second => f first second)

/-- Sample mean on one canonical tangent Pauli axis. -/
def pureLinearCoordinateEstimator
    (q : ℕ) (axis : Fin 2) (omega : PureLinearSampleSpace q) : ℝ :=
  (∑ shot : Fin q, pureLinearShot q (axis, shot) omega) / (q : ℝ)

/-- Both coordinate sample means are exactly centered. -/
theorem pureLinearCoordinateEstimator_mean_zero
    (q : ℕ) (axis : Fin 2) :
    (∫ omega, pureLinearCoordinateEstimator q axis omega
      ∂pureLinearSampleMeasure q) = 0 := by
  calc
    (∫ omega, pureLinearCoordinateEstimator q axis omega
        ∂pureLinearSampleMeasure q) =
        (∫ omega, ∑ shot : Fin q,
          pureLinearShot q (axis, shot) omega
          ∂pureLinearSampleMeasure q) / (q : ℝ) := by
      simp only [pureLinearCoordinateEstimator]
      rw [MeasureTheory.integral_div]
    _ = (∑ shot : Fin q,
          ∫ omega, pureLinearShot q (axis, shot) omega
            ∂pureLinearSampleMeasure q) / (q : ℝ) := by
      rw [pureLinear_integral_sum]
    _ = 0 := by
      simp [pureLinearShot_mean_zero]

/-- Pointwise expansion of the squared sample mean into all shot pairs. -/
theorem pureLinearCoordinateEstimator_sq_expand
    (q : ℕ) (axis : Fin 2) (omega : PureLinearSampleSpace q) :
    (pureLinearCoordinateEstimator q axis omega) ^ 2 =
      (∑ first : Fin q, ∑ second : Fin q,
        pureLinearShot q (axis, first) omega *
          pureLinearShot q (axis, second) omega) / (q : ℝ) ^ 2 := by
  unfold pureLinearCoordinateEstimator
  calc
    ((∑ shot : Fin q, pureLinearShot q (axis, shot) omega) /
        (q : ℝ)) ^ 2 =
        ((∑ shot : Fin q, pureLinearShot q (axis, shot) omega) *
          (∑ shot : Fin q, pureLinearShot q (axis, shot) omega)) /
            (q : ℝ) ^ 2 := by ring
    _ = (∑ first : Fin q, ∑ second : Fin q,
        pureLinearShot q (axis, first) omega *
          pureLinearShot q (axis, second) omega) / (q : ℝ) ^ 2 := by
      rw [Finset.sum_mul_sum]

/-- Exact coordinate second moment `1/q`. -/
theorem pureLinearCoordinateEstimator_secondMoment
    {q : ℕ} (hq : 0 < q) (axis : Fin 2) :
    (∫ omega, (pureLinearCoordinateEstimator q axis omega) ^ 2
      ∂pureLinearSampleMeasure q) = 1 / (q : ℝ) := by
  have hqne : (q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hq)
  calc
    (∫ omega, (pureLinearCoordinateEstimator q axis omega) ^ 2
        ∂pureLinearSampleMeasure q) =
        ∫ omega, (∑ first : Fin q, ∑ second : Fin q,
          pureLinearShot q (axis, first) omega *
            pureLinearShot q (axis, second) omega) / (q : ℝ) ^ 2
          ∂pureLinearSampleMeasure q := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall
        (pureLinearCoordinateEstimator_sq_expand q axis)
    _ = (∫ omega, ∑ first : Fin q, ∑ second : Fin q,
          pureLinearShot q (axis, first) omega *
            pureLinearShot q (axis, second) omega
          ∂pureLinearSampleMeasure q) / (q : ℝ) ^ 2 := by
      rw [MeasureTheory.integral_div]
    _ = (∑ first : Fin q, ∑ second : Fin q,
          ∫ omega,
            pureLinearShot q (axis, first) omega *
              pureLinearShot q (axis, second) omega
            ∂pureLinearSampleMeasure q) / (q : ℝ) ^ 2 := by
      rw [pureLinear_integral_doubleSum]
    _ = (q : ℝ) / (q : ℝ) ^ 2 := by
      congr 1
      simp [pureLinearShot_crossMoment]
    _ = 1 / (q : ℝ) := by
      field_simp [hqne]

/-- Variance defined from the centered second moment. -/
def pureLinearCoordinateVariance
    (q : ℕ) (axis : Fin 2) : ℝ :=
  ∫ omega,
    (pureLinearCoordinateEstimator q axis omega -
      (∫ eta, pureLinearCoordinateEstimator q axis eta
        ∂pureLinearSampleMeasure q)) ^ 2
    ∂pureLinearSampleMeasure q

/-- Exact coordinate variance `1/q`. -/
theorem pureLinearCoordinateVariance_eq
    {q : ℕ} (hq : 0 < q) (axis : Fin 2) :
    pureLinearCoordinateVariance q axis = 1 / (q : ℝ) := by
  rw [pureLinearCoordinateVariance,
    pureLinearCoordinateEstimator_mean_zero]
  simpa using pureLinearCoordinateEstimator_secondMoment hq axis

/-- Pointwise expansion of two coordinate means into all cross-axis shot
pairs. -/
theorem pureLinearCoordinateEstimator_mul_expand
    (q : ℕ) (firstAxis secondAxis : Fin 2)
    (omega : PureLinearSampleSpace q) :
    pureLinearCoordinateEstimator q firstAxis omega *
        pureLinearCoordinateEstimator q secondAxis omega =
      (∑ first : Fin q, ∑ second : Fin q,
        pureLinearShot q (firstAxis, first) omega *
          pureLinearShot q (secondAxis, second) omega) / (q : ℝ) ^ 2 := by
  unfold pureLinearCoordinateEstimator
  calc
    ((∑ shot : Fin q, pureLinearShot q (firstAxis, shot) omega) /
        (q : ℝ)) *
      ((∑ shot : Fin q, pureLinearShot q (secondAxis, shot) omega) /
        (q : ℝ)) =
        ((∑ shot : Fin q, pureLinearShot q (firstAxis, shot) omega) *
          (∑ shot : Fin q, pureLinearShot q (secondAxis, shot) omega)) /
            (q : ℝ) ^ 2 := by ring
    _ = (∑ first : Fin q, ∑ second : Fin q,
        pureLinearShot q (firstAxis, first) omega *
          pureLinearShot q (secondAxis, second) omega) / (q : ℝ) ^ 2 := by
      rw [Finset.sum_mul_sum]

/-- Distinct coordinate sample means have exact cross moment zero. -/
theorem pureLinearCoordinateEstimator_crossMoment_zero
    {q : ℕ} (hq : 0 < q)
    {firstAxis secondAxis : Fin 2}
    (haxes : firstAxis ≠ secondAxis) :
    (∫ omega,
      pureLinearCoordinateEstimator q firstAxis omega *
        pureLinearCoordinateEstimator q secondAxis omega
      ∂pureLinearSampleMeasure q) = 0 := by
  have hqne : (q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hq)
  calc
    (∫ omega,
      pureLinearCoordinateEstimator q firstAxis omega *
        pureLinearCoordinateEstimator q secondAxis omega
      ∂pureLinearSampleMeasure q) =
        ∫ omega, (∑ first : Fin q, ∑ second : Fin q,
          pureLinearShot q (firstAxis, first) omega *
            pureLinearShot q (secondAxis, second) omega) / (q : ℝ) ^ 2
          ∂pureLinearSampleMeasure q := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall
        (pureLinearCoordinateEstimator_mul_expand
          q firstAxis secondAxis)
    _ = (∑ first : Fin q, ∑ second : Fin q,
          ∫ omega,
            pureLinearShot q (firstAxis, first) omega *
              pureLinearShot q (secondAxis, second) omega
            ∂pureLinearSampleMeasure q) / (q : ℝ) ^ 2 := by
      rw [MeasureTheory.integral_div,
        pureLinear_integral_doubleSum]
    _ = 0 := by
      simp [pureLinearShot_crossMoment, haxes]

/-- Cross-covariance of two coordinate sample means. -/
def pureLinearCoordinateCovariance
    (q : ℕ) (firstAxis secondAxis : Fin 2) : ℝ :=
  ∫ omega,
    (pureLinearCoordinateEstimator q firstAxis omega -
      (∫ eta, pureLinearCoordinateEstimator q firstAxis eta
        ∂pureLinearSampleMeasure q)) *
    (pureLinearCoordinateEstimator q secondAxis omega -
      (∫ eta, pureLinearCoordinateEstimator q secondAxis eta
        ∂pureLinearSampleMeasure q))
    ∂pureLinearSampleMeasure q

/-- The two canonical tangent-axis estimators have zero cross-covariance. -/
theorem pureLinearCoordinateCovariance_eq_zero
    {q : ℕ} (hq : 0 < q)
    {firstAxis secondAxis : Fin 2}
    (haxes : firstAxis ≠ secondAxis) :
    pureLinearCoordinateCovariance q firstAxis secondAxis = 0 := by
  rw [pureLinearCoordinateCovariance,
    pureLinearCoordinateEstimator_mean_zero,
    pureLinearCoordinateEstimator_mean_zero]
  simpa using
    pureLinearCoordinateEstimator_crossMoment_zero hq haxes

/-- Explicit specialization to the two canonical Pauli tangent axes. -/
theorem pureLinearCanonicalAxes_covariance_zero
    {q : ℕ} (hq : 0 < q) :
    pureLinearCoordinateCovariance q 0 1 = 0 := by
  exact pureLinearCoordinateCovariance_eq_zero hq (by decide)

/-! ## Two-coordinate tangent estimator and exact quadratic risk -/

/-- Identify the two real/imaginary pure tangent coordinates with the two
canonical tangent Pauli axes. -/
def pureLinearTangentAxis : QubitOracle.TangentIndex 1 → Fin 2
  | Sum.inl _ => 0
  | Sum.inr _ => 1

/-- The two-coordinate sample-mean estimator, viewed as a pure-qubit tangent
error at the north-pole truth. -/
def pureLinearEstimator
    (q : ℕ) (omega : PureLinearSampleSpace q) :
    QubitOracle.Paper.PureQubitTangent :=
  fun coordinate =>
    pureLinearCoordinateEstimator q (pureLinearTangentAxis coordinate) omega

/-- Its squared tangent norm is the sum of its two coordinate squares. -/
theorem pureLinearEstimator_tangentRadiusSq_eq
    (q : ℕ) (omega : PureLinearSampleSpace q) :
    QubitOracle.tangentRadiusSq (pureLinearEstimator q omega) =
      (pureLinearCoordinateEstimator q 0 omega) ^ 2 +
        (pureLinearCoordinateEstimator q 1 omega) ^ 2 := by
  simp [QubitOracle.tangentRadiusSq, pureLinearEstimator,
    pureLinearTangentAxis]

/-- The local pure Bures/infidelity quadratic loss. -/
def pureLinearQuadraticLoss
    (q : ℕ) (omega : PureLinearSampleSpace q) : ℝ :=
  QubitOracle.Paper.pureQubitQuadraticLossReal
    (pureLinearEstimator q omega)

/-- Pointwise coordinate expression `(1/4) ||error||^2`. -/
theorem pureLinearQuadraticLoss_eq
    (q : ℕ) (omega : PureLinearSampleSpace q) :
    pureLinearQuadraticLoss q omega =
      ((pureLinearCoordinateEstimator q 0 omega) ^ 2 +
        (pureLinearCoordinateEstimator q 1 omega) ^ 2) / 4 := by
  rw [pureLinearQuadraticLoss,
    QubitOracle.Paper.pureQubitQuadraticLossReal,
    pureLinearEstimator_tangentRadiusSq_eq]

/-- Total number of shots in the equal two-axis design. -/
def pureLinearTotalShots (q : ℕ) : ℕ := 2 * q

/-- Exact expected quadratic loss before multiplying by total shot count. -/
theorem pureLinearExpectedQuadraticLoss_eq
    {q : ℕ} (hq : 0 < q) :
    (∫ omega, pureLinearQuadraticLoss q omega
      ∂pureLinearSampleMeasure q) = 1 / (2 * (q : ℝ)) := by
  have hqne : (q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hq)
  calc
    (∫ omega, pureLinearQuadraticLoss q omega
        ∂pureLinearSampleMeasure q) =
        ∫ omega,
          ((pureLinearCoordinateEstimator q 0 omega) ^ 2 +
            (pureLinearCoordinateEstimator q 1 omega) ^ 2) / 4
          ∂pureLinearSampleMeasure q := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall (pureLinearQuadraticLoss_eq q)
    _ = ((∫ omega, (pureLinearCoordinateEstimator q 0 omega) ^ 2
            ∂pureLinearSampleMeasure q) +
          (∫ omega, (pureLinearCoordinateEstimator q 1 omega) ^ 2
            ∂pureLinearSampleMeasure q)) / 4 := by
      rw [MeasureTheory.integral_div,
        MeasureTheory.integral_add
          (MeasureTheory.Integrable.of_finite)
          (MeasureTheory.Integrable.of_finite)]
    _ = ((1 / (q : ℝ)) + (1 / (q : ℝ))) / 4 := by
      rw [pureLinearCoordinateEstimator_secondMoment hq,
        pureLinearCoordinateEstimator_secondMoment hq]
    _ = 1 / (2 * (q : ℝ)) := by
      field_simp [hqne]
      ring

/-- With `N = 2q` total shots, the expected local quadratic Bures/infidelity
risk has scaled value exactly one. -/
theorem pureLinearScaledExpectedQuadraticLoss_eq_one
    {q : ℕ} (hq : 0 < q) :
    (pureLinearTotalShots q : ℝ) *
      (∫ omega, pureLinearQuadraticLoss q omega
        ∂pureLinearSampleMeasure q) = 1 := by
  rw [pureLinearExpectedQuadraticLoss_eq hq]
  have hqne : (q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hq)
  simp only [pureLinearTotalShots, Nat.cast_mul, Nat.cast_ofNat]
  field_simp [hqne]

/-- The exact value agrees with the equal-information design constant already
proved in `OneQubitDesignOptimality`. -/
theorem pureLinearScaledRisk_eq_equalDesignConstant
    {q : ℕ} (hq : 0 < q) :
    (pureLinearTotalShots q : ℝ) *
      (∫ omega, pureLinearQuadraticLoss q omega
        ∂pureLinearSampleMeasure q) =
      (1 / 4 : ℝ) *
        QubitOracle.Paper.twoCoordinateReciprocalRisk (1 / 2) (1 / 2) := by
  rw [pureLinearScaledExpectedQuadraticLoss_eq_one hq,
    QubitOracle.Paper.pure_equal_design_attains_bures_constant]

/-! ## Exact physical infidelity transfer and honest Bures remainder -/

/-- Every individual Pauli sign lies in `[-1,1]`. -/
theorem pureLinearShot_bounds
    (q : ℕ) (index : PureLinearShotIndex q)
    (omega : PureLinearSampleSpace q) :
    -1 ≤ pureLinearShot q index omega ∧
      pureLinearShot q index omega ≤ 1 := by
  cases hvalue : omega index <;>
    simp [pureLinearShot, pureLinearBoolSign, hvalue]

/-- Every coordinate sample mean has absolute value at most one. -/
theorem pureLinearCoordinateEstimator_abs_le_one
    {q : ℕ} (hq : 0 < q) (axis : Fin 2)
    (omega : PureLinearSampleSpace q) :
    |pureLinearCoordinateEstimator q axis omega| ≤ 1 := by
  have hqreal : 0 < (q : ℝ) := by
    exact_mod_cast hq
  have hlower :
      (∑ _shot : Fin q, (-1 : ℝ)) ≤
        ∑ shot : Fin q, pureLinearShot q (axis, shot) omega := by
    apply Finset.sum_le_sum
    intro shot _hshot
    exact (pureLinearShot_bounds q (axis, shot) omega).1
  have hupper :
      (∑ shot : Fin q, pureLinearShot q (axis, shot) omega) ≤
        ∑ _shot : Fin q, (1 : ℝ) := by
    apply Finset.sum_le_sum
    intro shot _hshot
    exact (pureLinearShot_bounds q (axis, shot) omega).2
  rw [abs_le]
  constructor
  · unfold pureLinearCoordinateEstimator
    apply (le_div_iff₀ hqreal).2
    simpa using hlower
  · unfold pureLinearCoordinateEstimator
    apply (div_le_iff₀ hqreal).2
    simpa using hupper

/-- The two-coordinate estimator always remains inside radius squared two,
and therefore inside the radius-four pure chart. -/
theorem pureLinearEstimator_tangentRadiusSq_le_two
    {q : ℕ} (hq : 0 < q) (omega : PureLinearSampleSpace q) :
    QubitOracle.tangentRadiusSq (pureLinearEstimator q omega) ≤ 2 := by
  have hzero := pureLinearCoordinateEstimator_abs_le_one hq 0 omega
  have hone := pureLinearCoordinateEstimator_abs_le_one hq 1 omega
  have hzeroSq :
      (pureLinearCoordinateEstimator q 0 omega) ^ 2 ≤ 1 := by
    have hsquare :
        |pureLinearCoordinateEstimator q 0 omega| ^ 2 ≤ (1 : ℝ) ^ 2 := by
      gcongr
    simpa only [sq_abs, one_pow] using hsquare
  have honeSq :
      (pureLinearCoordinateEstimator q 1 omega) ^ 2 ≤ 1 := by
    have hsquare :
        |pureLinearCoordinateEstimator q 1 omega| ^ 2 ≤ (1 : ℝ) ^ 2 := by
      gcongr
    simpa only [sq_abs, one_pow] using hsquare
  rw [pureLinearEstimator_tangentRadiusSq_eq]
  linarith

/-- The estimator satisfies the exact pure-chart radius assumption. -/
theorem pureLinearEstimator_in_pureChart
    {q : ℕ} (hq : 0 < q) (omega : PureLinearSampleSpace q) :
    QubitOracle.tangentRadiusSq (pureLinearEstimator q omega) ≤ 4 := by
  exact (pureLinearEstimator_tangentRadiusSq_le_two hq omega).trans
    (by norm_num)

/-- Exact physical infidelity equals the local quadratic loss for every
realized estimator in the normalized rank-one chart. -/
theorem pureLinearChartInfidelity_eq_quadraticLoss
    {q : ℕ} (hq : 0 < q) (omega : PureLinearSampleSpace q) :
    QubitOracle.Paper.pureQubitChartInfidelity
        (pureLinearEstimator q omega) =
      pureLinearQuadraticLoss q omega := by
  simpa [pureLinearQuadraticLoss,
    QubitOracle.Paper.pureQubitQuadraticLossReal] using
    QubitOracle.Paper.pureQubitChartInfidelity_eq_quadratic
      (pureLinearEstimator q omega)
      (pureLinearEstimator_in_pureChart hq omega)

/-- Consequently the exact expected chart infidelity equals the expected
quadratic risk. -/
theorem pureLinearExpectedChartInfidelity_eq_quadraticRisk
    {q : ℕ} (hq : 0 < q) :
    (∫ omega,
      QubitOracle.Paper.pureQubitChartInfidelity
        (pureLinearEstimator q omega)
      ∂pureLinearSampleMeasure q) =
      ∫ omega, pureLinearQuadraticLoss q omega
        ∂pureLinearSampleMeasure q := by
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall
    (pureLinearChartInfidelity_eq_quadraticLoss hq)

/-- The exact physical chart-infidelity risk therefore also has scaled value
one. -/
theorem pureLinearScaledExpectedChartInfidelity_eq_one
    {q : ℕ} (hq : 0 < q) :
    (pureLinearTotalShots q : ℝ) *
      (∫ omega,
        QubitOracle.Paper.pureQubitChartInfidelity
          (pureLinearEstimator q omega)
        ∂pureLinearSampleMeasure q) = 1 := by
  rw [pureLinearExpectedChartInfidelity_eq_quadraticRisk hq]
  exact pureLinearScaledExpectedQuadraticLoss_eq_one hq

/-- Squared Bures loss has the existing nonnegative fourth-order remainder;
it is not falsely identified with the finite-sample quadratic loss. -/
theorem pureLinearChartBuresSq_remainder_bounds
    {q : ℕ} (hq : 0 < q) (omega : PureLinearSampleSpace q) :
    0 ≤ QubitOracle.Paper.pureQubitChartBuresSq
          (pureLinearEstimator q omega) -
        pureLinearQuadraticLoss q omega ∧
      QubitOracle.Paper.pureQubitChartBuresSq
          (pureLinearEstimator q omega) -
        pureLinearQuadraticLoss q omega ≤
          (QubitOracle.tangentRadiusSq
            (pureLinearEstimator q omega)) ^ 2 / 16 := by
  simpa [pureLinearQuadraticLoss,
    QubitOracle.Paper.pureQubitQuadraticLossReal,
    QubitOracle.Paper.pureQubitChartBuresSq_eq_buresChartLoss] using
    QubitOracle.buresChartLoss_remainder_bounds
      (pureLinearEstimator q omega)
      (pureLinearEstimator_in_pureChart hq omega)

/-- Integrated squared-Bures transfer with the exact fourth-radius remainder.
All integrability hypotheses close internally because the sample space is
finite. -/
theorem pureLinearExpectedChartBuresSq_bounds
    {q : ℕ} (hq : 0 < q) :
    (∫ omega, pureLinearQuadraticLoss q omega
      ∂pureLinearSampleMeasure q) ≤
        (∫ omega,
          QubitOracle.Paper.pureQubitChartBuresSq
            (pureLinearEstimator q omega)
          ∂pureLinearSampleMeasure q) ∧
      (∫ omega,
        QubitOracle.Paper.pureQubitChartBuresSq
          (pureLinearEstimator q omega)
        ∂pureLinearSampleMeasure q) ≤
        (∫ omega, pureLinearQuadraticLoss q omega
          ∂pureLinearSampleMeasure q) +
        (∫ omega,
          (QubitOracle.tangentRadiusSq
            (pureLinearEstimator q omega)) ^ 2
          ∂pureLinearSampleMeasure q) / 16 := by
  have hpointwise : ∀ omega : PureLinearSampleSpace q,
      pureLinearQuadraticLoss q omega ≤
          QubitOracle.Paper.pureQubitChartBuresSq
            (pureLinearEstimator q omega) ∧
        QubitOracle.Paper.pureQubitChartBuresSq
            (pureLinearEstimator q omega) ≤
          pureLinearQuadraticLoss q omega +
            (QubitOracle.tangentRadiusSq
              (pureLinearEstimator q omega)) ^ 2 / 16 := by
    intro omega
    have hb := pureLinearChartBuresSq_remainder_bounds hq omega
    constructor <;> linarith
  constructor
  · exact MeasureTheory.integral_mono
      MeasureTheory.Integrable.of_finite
      MeasureTheory.Integrable.of_finite
      (fun omega => (hpointwise omega).1)
  · calc
      (∫ omega,
        QubitOracle.Paper.pureQubitChartBuresSq
          (pureLinearEstimator q omega)
        ∂pureLinearSampleMeasure q) ≤
          ∫ omega,
            pureLinearQuadraticLoss q omega +
              (QubitOracle.tangentRadiusSq
                (pureLinearEstimator q omega)) ^ 2 / 16
            ∂pureLinearSampleMeasure q :=
        MeasureTheory.integral_mono
          MeasureTheory.Integrable.of_finite
          MeasureTheory.Integrable.of_finite
          (fun omega => (hpointwise omega).2)
      _ = (∫ omega, pureLinearQuadraticLoss q omega
            ∂pureLinearSampleMeasure q) +
          (∫ omega,
            (QubitOracle.tangentRadiusSq
              (pureLinearEstimator q omega)) ^ 2 / 16
            ∂pureLinearSampleMeasure q) := by
        rw [MeasureTheory.integral_add
          MeasureTheory.Integrable.of_finite
          MeasureTheory.Integrable.of_finite]
      _ = (∫ omega, pureLinearQuadraticLoss q omega
            ∂pureLinearSampleMeasure q) +
          (∫ omega,
            (QubitOracle.tangentRadiusSq
              (pureLinearEstimator q omega)) ^ 2
            ∂pureLinearSampleMeasure q) / 16 := by
        rw [MeasureTheory.integral_div]

/-- In particular, the finite-sample scaled squared-Bures risk is at least the
quadratic constant one.  Equality is not asserted because of the positive
fourth-order remainder. -/
theorem pureLinearScaledExpectedChartBuresSq_ge_one
    {q : ℕ} (hq : 0 < q) :
    1 ≤ (pureLinearTotalShots q : ℝ) *
      (∫ omega,
        QubitOracle.Paper.pureQubitChartBuresSq
          (pureLinearEstimator q omega)
        ∂pureLinearSampleMeasure q) := by
  have hshots : 0 ≤ (pureLinearTotalShots q : ℝ) := by positivity
  calc
    1 = (pureLinearTotalShots q : ℝ) *
        (∫ omega, pureLinearQuadraticLoss q omega
          ∂pureLinearSampleMeasure q) :=
      (pureLinearScaledExpectedQuadraticLoss_eq_one hq).symm
    _ ≤ (pureLinearTotalShots q : ℝ) *
        (∫ omega,
          QubitOracle.Paper.pureQubitChartBuresSq
            (pureLinearEstimator q omega)
          ∂pureLinearSampleMeasure q) :=
      mul_le_mul_of_nonneg_left
        (pureLinearExpectedChartBuresSq_bounds hq).1 hshots

end QubitOracle.Paper.OneQubitPureLinearEstimatorRisk
