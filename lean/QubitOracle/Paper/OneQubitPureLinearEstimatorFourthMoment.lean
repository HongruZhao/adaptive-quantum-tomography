import QubitOracle.Paper.OneQubitPureLinearEstimatorRisk

open Filter MeasureTheory ProbabilityTheory Topology
open scoped BigOperators

namespace QubitOracle.Paper.OneQubitPureLinearEstimatorFourthMoment

/-!
# Fourth moments for the finite pure-qubit linear estimator

The fair-Rademacher combinatorics below are proved internally.  The only
remaining probability-library boundary is exposed by
`PureLinearFiniteProductIntegralBridge`: it says exactly that the concrete
finite product integral has the raw one-axis fourth moment supplied by the
recursion, and that the squared sums on the two disjoint axes factor.

This file declares no axiom.  Results depending on that bridge take it as an
explicit argument.
-/

/-! ## Deterministic fair-Rademacher recursion -/

/-- The second moment produced by repeatedly adjoining one independent fair
Rademacher sign. -/
def fairRademacherSecondMoment : ℕ → ℝ
  | 0 => 0
  | q + 1 => fairRademacherSecondMoment q + 1

/-- The fourth moment produced by repeatedly adjoining one independent fair
Rademacher sign. -/
def fairRademacherFourthMoment : ℕ → ℝ
  | 0 => 0
  | q + 1 =>
      fairRademacherFourthMoment q +
        6 * fairRademacherSecondMoment q + 1

/-- Averaging the two possible new signs increases the second moment by one. -/
theorem fairRademacher_second_step (s : ℝ) :
    ((s + 1) ^ 2 + (s - 1) ^ 2) / 2 = s ^ 2 + 1 := by
  ring

/-- Averaging the two possible new signs gives the fourth-moment recursion. -/
theorem fairRademacher_fourth_step (s : ℝ) :
    ((s + 1) ^ 4 + (s - 1) ^ 4) / 2 = s ^ 4 + 6 * s ^ 2 + 1 := by
  ring

/-- Exact second moment of the combinatorial `q`-sign recursion. -/
theorem fairRademacherSecondMoment_eq (q : ℕ) :
    fairRademacherSecondMoment q = (q : ℝ) := by
  induction q with
  | zero => norm_num [fairRademacherSecondMoment]
  | succ q ih =>
      rw [fairRademacherSecondMoment, ih]
      simp only [Nat.cast_succ]

/-- Exact fourth moment of the combinatorial `q`-sign recursion. -/
theorem fairRademacherFourthMoment_eq (q : ℕ) :
    fairRademacherFourthMoment q =
      3 * (q : ℝ) ^ 2 - 2 * (q : ℝ) := by
  induction q with
  | zero => norm_num [fairRademacherFourthMoment]
  | succ q ih =>
      rw [fairRademacherFourthMoment, ih, fairRademacherSecondMoment_eq]
      simp only [Nat.cast_succ]
      ring

/-! ## Exact finite-product boundary -/

/-- The unnormalized sum of the `q` fair outcomes measured on one tangent
axis. -/
def pureLinearRawAxisSum
    (q : ℕ) (axis : Fin 2) :
    QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q → ℝ :=
  fun omega =>
    ∑ shot : Fin q,
      QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearShot
        q (axis, shot) omega

/--
The narrow finite-product integration bridge left explicit in this source
candidate.

The first field transports the proved fair-sign recursion to the actual raw
axis sum.  The second field is precisely the factorization of the two squared
axis sums supplied by independence of the two disjoint coordinate blocks.
Neither field assumes a normalized estimator moment or the desired radial
fourth moment.
-/
structure PureLinearFiniteProductIntegralBridge : Prop where
  rawAxisFourth :
    ∀ (q : ℕ) (axis : Fin 2),
      (∫ omega,
          pureLinearRawAxisSum q axis omega ^ 4
        ∂QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q) =
        fairRademacherFourthMoment q
  axisSquareFactorization :
    ∀ q : ℕ,
      (∫ omega,
          QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearCoordinateEstimator
              q (0 : Fin 2) omega ^ 2 *
            QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearCoordinateEstimator
              q (1 : Fin 2) omega ^ 2
        ∂QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q) =
        (∫ omega,
            QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearCoordinateEstimator
                q (0 : Fin 2) omega ^ 2
          ∂QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q) *
          (∫ omega,
              QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearCoordinateEstimator
                  q (1 : Fin 2) omega ^ 2
            ∂QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q)

/-! ## Consequences of the explicit bridge -/

/-- Exact fourth moment of one `q`-shot coordinate sample mean. -/
theorem pureLinearCoordinateEstimator_fourthMoment
    (bridge : PureLinearFiniteProductIntegralBridge)
    {q : ℕ} (hq : 0 < q) (axis : Fin 2) :
    (∫ omega,
        QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearCoordinateEstimator
            q axis omega ^ 4
      ∂QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q) =
      3 / (q : ℝ) ^ 2 - 2 / (q : ℝ) ^ 3 := by
  have hq0 : (q : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hq
  have hraw := bridge.rawAxisFourth q axis
  rw [fairRademacherFourthMoment_eq] at hraw
  calc
    (∫ omega,
        QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearCoordinateEstimator
            q axis omega ^ 4
      ∂QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q) =
        (∫ omega, pureLinearRawAxisSum q axis omega ^ 4
          ∂QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q) /
          (q : ℝ) ^ 4 := by
            simp only [
              QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearCoordinateEstimator,
              pureLinearRawAxisSum, div_pow]
            rw [integral_div]
    _ = (3 * (q : ℝ) ^ 2 - 2 * (q : ℝ)) / (q : ℝ) ^ 4 := by
          rw [hraw]
    _ = 3 / (q : ℝ) ^ 2 - 2 / (q : ℝ) ^ 3 := by
          field_simp [hq0]

/-- Independence of the two measurement blocks gives the exact mixed square
moment of the two coordinate sample means. -/
theorem pureLinearCoordinateEstimator_crossSquareMoment
    (bridge : PureLinearFiniteProductIntegralBridge)
    {q : ℕ} (hq : 0 < q) :
    (∫ omega,
        QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearCoordinateEstimator
            q (0 : Fin 2) omega ^ 2 *
          QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearCoordinateEstimator
            q (1 : Fin 2) omega ^ 2
      ∂QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q) =
      1 / (q : ℝ) ^ 2 := by
  rw [bridge.axisSquareFactorization]
  rw [
    QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearCoordinateEstimator_secondMoment
      hq (0 : Fin 2),
    QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearCoordinateEstimator_secondMoment
      hq (1 : Fin 2)]
  ring

/-- The squared Euclidean radius of the two-coordinate linear estimator. -/
noncomputable def pureLinearSquaredRadius
    (q : ℕ)
    (omega :
      QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.PureLinearSampleSpace q) : ℝ :=
  QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearCoordinateEstimator
      q (0 : Fin 2) omega ^ 2 +
    QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearCoordinateEstimator
      q (1 : Fin 2) omega ^ 2

private theorem finite_integrable_of_measurable
    {Omega : Type*} [MeasurableSpace Omega] [Fintype Omega]
    [MeasurableSingletonClass Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {f : Omega → ℝ} (hf : Measurable f) : Integrable f mu := by
  exact Integrable.of_finite

private theorem pureLinearCoordinateEstimator_measurable
    (q : ℕ) (axis : Fin 2) :
    Measurable
      (QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearCoordinateEstimator
        q axis) := by
  exact
    (Finset.measurable_fun_sum Finset.univ
      (fun shot _ =>
        QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearShot_measurable
          q (axis, shot))).div_const (q : ℝ)

/-- Exact fourth moment of the squared two-coordinate radius:
`E[(x^2+y^2)^2] = 8/q^2 - 4/q^3`. -/
theorem pureLinearSquaredRadius_fourthMoment
    (bridge : PureLinearFiniteProductIntegralBridge)
    {q : ℕ} (hq : 0 < q) :
    (∫ omega, pureLinearSquaredRadius q omega ^ 2
      ∂QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q) =
      8 / (q : ℝ) ^ 2 - 4 / (q : ℝ) ^ 3 := by
  let mu :=
    QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q
  let X :=
    QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearCoordinateEstimator
      q (0 : Fin 2)
  let Y :=
    QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearCoordinateEstimator
      q (1 : Fin 2)
  have hX : Measurable X := pureLinearCoordinateEstimator_measurable q (0 : Fin 2)
  have hY : Measurable Y := pureLinearCoordinateEstimator_measurable q (1 : Fin 2)
  have hX4 : Integrable (fun omega => X omega ^ 4) mu :=
    finite_integrable_of_measurable mu (hX.pow_const 4)
  have hY4 : Integrable (fun omega => Y omega ^ 4) mu :=
    finite_integrable_of_measurable mu (hY.pow_const 4)
  have hXY : Integrable (fun omega => X omega ^ 2 * Y omega ^ 2) mu :=
    finite_integrable_of_measurable mu
      ((hX.pow_const 2).mul (hY.pow_const 2))
  have hTwoXY : Integrable (fun omega => 2 * (X omega ^ 2 * Y omega ^ 2)) mu :=
    finite_integrable_of_measurable mu
      (measurable_const.mul ((hX.pow_const 2).mul (hY.pow_const 2)))
  have hexpand :
      ∀ omega,
        pureLinearSquaredRadius q omega ^ 2 =
          X omega ^ 4 + 2 * (X omega ^ 2 * Y omega ^ 2) + Y omega ^ 4 := by
    intro omega
    simp only [pureLinearSquaredRadius, X, Y]
    ring
  calc
    (∫ omega, pureLinearSquaredRadius q omega ^ 2 ∂mu) =
        ∫ omega,
          X omega ^ 4 + 2 * (X omega ^ 2 * Y omega ^ 2) + Y omega ^ 4
        ∂mu := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hexpand
    _ =
        (∫ omega, X omega ^ 4 ∂mu) +
          2 * (∫ omega, X omega ^ 2 * Y omega ^ 2 ∂mu) +
          (∫ omega, Y omega ^ 4 ∂mu) := by
            calc
              (∫ omega,
                  X omega ^ 4 + 2 * (X omega ^ 2 * Y omega ^ 2) +
                    Y omega ^ 4 ∂mu) =
                  (∫ omega,
                    X omega ^ 4 + 2 * (X omega ^ 2 * Y omega ^ 2) ∂mu) +
                    ∫ omega, Y omega ^ 4 ∂mu :=
                integral_add (hX4.add hTwoXY) hY4
              _ = (∫ omega, X omega ^ 4 ∂mu) +
                    2 * (∫ omega, X omega ^ 2 * Y omega ^ 2 ∂mu) +
                    (∫ omega, Y omega ^ 4 ∂mu) := by
                rw [integral_add hX4 hTwoXY, integral_const_mul]
    _ = 8 / (q : ℝ) ^ 2 - 4 / (q : ℝ) ^ 3 := by
          dsimp only [mu, X, Y]
          rw [
            pureLinearCoordinateEstimator_fourthMoment bridge hq (0 : Fin 2),
            pureLinearCoordinateEstimator_crossSquareMoment bridge hq,
            pureLinearCoordinateEstimator_fourthMoment bridge hq (1 : Fin 2)]
          ring

/-! ## Explicit fourth-order envelope and squeeze assembly -/

/-- The exact upper envelope obtained by multiplying the fourth-order Bures
remainder bound by the total shot count `N = 2q`. -/
noncomputable def pureLinearScaledBuresRemainderEnvelope (q : ℕ) : ℝ :=
  (QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearTotalShots q : ℝ) /
      16 *
    (∫ omega, pureLinearSquaredRadius q omega ^ 2
      ∂QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearSampleMeasure q)

/-- Exact finite-`q` value of the scaled fourth-order envelope. -/
theorem pureLinearScaledBuresRemainderEnvelope_eq
    (bridge : PureLinearFiniteProductIntegralBridge)
    {q : ℕ} (hq : 0 < q) :
    pureLinearScaledBuresRemainderEnvelope q =
      1 / (q : ℝ) - 1 / (2 * (q : ℝ) ^ 2) := by
  have hq0 : (q : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hq
  simp only [pureLinearScaledBuresRemainderEnvelope,
    QubitOracle.Paper.OneQubitPureLinearEstimatorRisk.pureLinearTotalShots,
    Nat.cast_mul, Nat.cast_ofNat]
  rw [pureLinearSquaredRadius_fourthMoment bridge hq]
  field_simp [hq0]
  ring

/-- The scaled fourth-order envelope tends to zero. -/
theorem pureLinearScaledBuresRemainderEnvelope_tendsto_zero
    (bridge : PureLinearFiniteProductIntegralBridge) :
    Tendsto pureLinearScaledBuresRemainderEnvelope atTop (𝓝 0) := by
  have hinv :
      Tendsto (fun q : ℕ => ((q : ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hclosed :
      Tendsto
        (fun q : ℕ =>
          (q : ℝ)⁻¹ - (1 / 2 : ℝ) * ((q : ℝ)⁻¹) ^ 2)
        atTop (𝓝 0) := by
    simpa using
      hinv.sub
        ((tendsto_const_nhds :
            Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2 : ℝ))).mul
          (hinv.pow 2))
  have heq :
      pureLinearScaledBuresRemainderEnvelope =ᶠ[atTop]
        (fun q : ℕ =>
          (q : ℝ)⁻¹ - (1 / 2 : ℝ) * ((q : ℝ)⁻¹) ^ 2) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with q hq
    rw [pureLinearScaledBuresRemainderEnvelope_eq bridge hq]
    simp only [one_div, div_eq_mul_inv]
    ring
  exact hclosed.congr' heq.symm

/-- Squeeze any explicitly supplied scaled Bures remainder between zero and
the proved fourth-order envelope.  The bound is deliberately an argument, so
this theorem does not pretend that the retained Bures module has already been
wired to the present source candidate. -/
theorem scaledBuresRemainder_tendsto_zero_of_explicit_bound
    (bridge : PureLinearFiniteProductIntegralBridge)
    (scaledRemainder : ℕ → ℝ)
    (hbound :
      ∀ q : ℕ, 0 < q →
        0 ≤ scaledRemainder q ∧
          scaledRemainder q ≤ pureLinearScaledBuresRemainderEnvelope q) :
    Tendsto scaledRemainder atTop (𝓝 0) := by
  have hnonnegative : ∀ᶠ q : ℕ in atTop, 0 ≤ scaledRemainder q := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with q hq
    exact (hbound q hq).1
  have hupper :
      ∀ᶠ q : ℕ in atTop,
        scaledRemainder q ≤ pureLinearScaledBuresRemainderEnvelope q := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with q hq
    exact (hbound q hq).2
  exact Filter.Tendsto.squeeze' tendsto_const_nhds
    (pureLinearScaledBuresRemainderEnvelope_tendsto_zero bridge)
    hnonnegative hupper

/-- Final risk assembly.  Once `scaledRemainder` is instantiated by the
existing squared-Bures remainder, its pointwise fourth-order bound supplies
`hbound`, while `hdecomp` is the exact quadratic-risk plus remainder identity. -/
theorem scaledExpectedSquaredBuresRisk_tendsto_one_of_explicit_remainder
    (bridge : PureLinearFiniteProductIntegralBridge)
    (scaledRisk scaledRemainder : ℕ → ℝ)
    (hbound :
      ∀ q : ℕ, 0 < q →
        0 ≤ scaledRemainder q ∧
          scaledRemainder q ≤ pureLinearScaledBuresRemainderEnvelope q)
    (hdecomp :
      ∀ q : ℕ, 0 < q → scaledRisk q = 1 + scaledRemainder q) :
    Tendsto scaledRisk atTop (𝓝 1) := by
  have hremainder :=
    scaledBuresRemainder_tendsto_zero_of_explicit_bound
      bridge scaledRemainder hbound
  have hsum : Tendsto (fun q : ℕ => 1 + scaledRemainder q) atTop (𝓝 1) := by
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add
        hremainder
  have heq :
      scaledRisk =ᶠ[atTop] (fun q : ℕ => 1 + scaledRemainder q) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with q hq
    exact hdecomp q hq
  exact hsum.congr' heq.symm

end QubitOracle.Paper.OneQubitPureLinearEstimatorFourthMoment
