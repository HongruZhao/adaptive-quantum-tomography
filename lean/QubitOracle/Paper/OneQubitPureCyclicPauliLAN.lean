import QubitOracle.Paper.OneQubitPureCyclicPauliIIDCLT
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# LAN for the pure one-qubit two-tangent-Pauli cycle

We use an exact Bloch-tangent chart at the north-pole representative.  Its two
tangent coordinates are linear and its radial coordinate is chosen so that
the Bloch norm is exactly one.  Hence all local states are genuinely pure.
Only the two regular tangent Pauli measurements are cycled.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace QubitOracle.Paper

open OneQubitPureLinearEstimatorRisk

noncomputable section

/-- The local transverse Bloch coordinate in the `N = 2q` experiment. -/
def pureCyclicPauliLocalTilt
    (q : ℕ) (h : Fin 2 -> ℝ) (axis : Fin 2) : ℝ :=
  Real.sqrt 2 * h axis / Real.sqrt q

/-- Exact pure-state Bloch chart with the first two coordinates tangent. -/
def pureCyclicPauliLocalBloch
    (q : ℕ) (h : Fin 2 -> ℝ) : Fin 3 -> ℝ :=
  ![pureCyclicPauliLocalTilt q h 0,
    pureCyclicPauliLocalTilt q h 1,
    Real.sqrt (1 - pureCyclicPauliLocalTilt q h 0 ^ 2 -
      pureCyclicPauliLocalTilt q h 1 ^ 2)]

/-- The exact chart domain at row `q`. -/
def PureCyclicPauliLocalChartValid
    (q : ℕ) (h : Fin 2 -> ℝ) : Prop :=
  0 < q ∧
    pureCyclicPauliLocalTilt q h 0 ^ 2 +
      pureCyclicPauliLocalTilt q h 1 ^ 2 <= 1

/-- Squared Euclidean Bloch norm, stated locally to keep this endpoint
independent of the general mixed-state import graph. -/
def pureCyclicPauliBlochNormSq (r : Fin 3 -> ℝ) : ℝ :=
  ∑ i : Fin 3, r i ^ 2

/-- Every valid local chart point is exactly a pure qubit Bloch vector. -/
theorem pureCyclicPauliLocalBloch_normSq_eq_one
    {q : ℕ} {h : Fin 2 -> ℝ}
    (hvalid : PureCyclicPauliLocalChartValid q h) :
    pureCyclicPauliBlochNormSq (pureCyclicPauliLocalBloch q h) = 1 := by
  have hradial : 0 <= 1 - pureCyclicPauliLocalTilt q h 0 ^ 2 -
      pureCyclicPauliLocalTilt q h 1 ^ 2 := by
    linarith [hvalid.2]
  rw [pureCyclicPauliBlochNormSq, Fin.sum_univ_three]
  simp [pureCyclicPauliLocalBloch]
  rw [Real.sq_sqrt hradial]
  ring

/-- The outcome stored in one complete tangent cycle. -/
def pureCyclicPauliBlockOutcome
    (axis : Fin 2) (block : PureCyclicPauliBlock) : Bool :=
  block (axis, (0 : Fin 1))

theorem pureCyclicPauliBlockCoordinate_eq_sign
    (axis : Fin 2) (block : PureCyclicPauliBlock) :
    pureCyclicPauliBlockCoordinate axis block =
      pureLinearBoolSign (pureCyclicPauliBlockOutcome axis block) := by
  simp [pureCyclicPauliBlockCoordinate, pureLinearCoordinateEstimator,
    pureLinearShot, pureCyclicPauliBlockOutcome]

theorem pureCyclicPauliBlockCoordinate_sq_one
    (axis : Fin 2) (block : PureCyclicPauliBlock) :
    pureCyclicPauliBlockCoordinate axis block ^ 2 = 1 := by
  rw [pureCyclicPauliBlockCoordinate_eq_sign]
  cases pureCyclicPauliBlockOutcome axis block <;>
    norm_num [pureLinearBoolSign]

theorem pureCyclicPauliBlockCoordinate_abs_eq_one
    (axis : Fin 2) (block : PureCyclicPauliBlock) :
    |pureCyclicPauliBlockCoordinate axis block| = 1 := by
  rw [pureCyclicPauliBlockCoordinate_eq_sign]
  cases pureCyclicPauliBlockOutcome axis block <;>
    norm_num [pureLinearBoolSign]

/-- Exact two-outcome tangent-Pauli Born probability in the pure chart. -/
def pureCyclicPauliLocalBornProbability
    (q : ℕ) (h : Fin 2 -> ℝ) (axis : Fin 2) (outcome : Bool) : ℝ :=
  if outcome then
    (1 + pureCyclicPauliLocalTilt q h axis) / 2
  else
    (1 - pureCyclicPauliLocalTilt q h axis) / 2

/-- Relative to the fair truth law, the exact Born factor is `1 + tilt*sign`. -/
theorem pureCyclicPauliLocalBornProbability_relative_fair
    (q : ℕ) (h : Fin 2 -> ℝ) (axis : Fin 2) (outcome : Bool) :
    pureCyclicPauliLocalBornProbability q h axis outcome / (1 / 2 : ℝ) =
      1 + pureCyclicPauliLocalTilt q h axis *
        pureLinearBoolSign outcome := by
  cases outcome <;>
    norm_num [pureCyclicPauliLocalBornProbability, pureLinearBoolSign] <;>
    ring

/-- One scalar likelihood perturbation in a complete cycle. -/
def pureCyclicPauliLikelihoodPerturbation
    (q : ℕ) (h : Fin 2 -> ℝ) (axis : Fin 2)
    (block : PureCyclicPauliBlock) : ℝ :=
  pureCyclicPauliLocalTilt q h axis *
    pureCyclicPauliBlockCoordinate axis block

theorem pureCyclicPauliLikelihoodPerturbation_eq_born_factor
    (q : ℕ) (h : Fin 2 -> ℝ) (axis : Fin 2)
    (block : PureCyclicPauliBlock) :
    1 + pureCyclicPauliLikelihoodPerturbation q h axis block =
      pureCyclicPauliLocalBornProbability q h axis
        (pureCyclicPauliBlockOutcome axis block) / (1 / 2 : ℝ) := by
  rw [pureCyclicPauliLocalBornProbability_relative_fair,
    pureCyclicPauliLikelihoodPerturbation,
    pureCyclicPauliBlockCoordinate_eq_sign]

/-- Second-order scalar logarithm residual. -/
def pureCyclicPauliLogRemainder (x : ℝ) : ℝ :=
  Real.log (1 + x) - x + x ^ 2 / 2

theorem pureCyclicPauliLog_exact_secondOrder (x : ℝ) :
    Real.log (1 + x) =
      x - x ^ 2 / 2 + pureCyclicPauliLogRemainder x := by
  unfold pureCyclicPauliLogRemainder
  ring

/-- Mathlib's real logarithm series bound specialized to second order. -/
theorem pureCyclicPauliLogRemainder_abs_le
    {x : ℝ} (hx : |x| < 1) :
    |pureCyclicPauliLogRemainder x| <=
      |x| ^ 3 / (1 - |x|) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -x)
    (by simpa using hx) 2
  have heq :
      -x + x ^ 2 / (1 + 1 : ℝ) + Real.log (1 + x) =
        pureCyclicPauliLogRemainder x := by
    unfold pureCyclicPauliLogRemainder
    ring
  simpa [Finset.sum_range_succ, abs_neg, heq] using h

theorem pureCyclicPauliLogRemainder_abs_le_two_cube
    {x : ℝ} (hx : |x| <= 1 / 2) :
    |pureCyclicPauliLogRemainder x| <= 2 * |x| ^ 3 := by
  have hxlt : |x| < 1 := lt_of_le_of_lt hx (by norm_num)
  have hden : 0 < 1 - |x| := by linarith
  calc
    |pureCyclicPauliLogRemainder x| <=
        |x| ^ 3 / (1 - |x|) := pureCyclicPauliLogRemainder_abs_le hxlt
    _ <= 2 * |x| ^ 3 := by
      apply (div_le_iff₀ hden).2
      have hcube : 0 <= |x| ^ 3 := by positivity
      have hfactor : 0 <= 2 * (1 - |x|) - 1 := by linarith
      nlinarith [mul_nonneg hcube hfactor]

/-- Linear perturbation sum inside one complete cycle. -/
def pureCyclicPauliBlockLinearTerm
    (q : ℕ) (h : Fin 2 -> ℝ) (block : PureCyclicPauliBlock) : ℝ :=
  pureCyclicPauliLikelihoodPerturbation q h 0 block +
    pureCyclicPauliLikelihoodPerturbation q h 1 block

/-- Quadratic perturbation sum inside one complete cycle. -/
def pureCyclicPauliBlockQuadraticTerm
    (q : ℕ) (h : Fin 2 -> ℝ) (block : PureCyclicPauliBlock) : ℝ :=
  pureCyclicPauliLikelihoodPerturbation q h 0 block ^ 2 +
    pureCyclicPauliLikelihoodPerturbation q h 1 block ^ 2

/-- Log-likelihood contribution of one complete tangent cycle. -/
def pureCyclicPauliBlockLogLikelihoodRatio
    (q : ℕ) (h : Fin 2 -> ℝ) (block : PureCyclicPauliBlock) : ℝ :=
  Real.log (1 + pureCyclicPauliLikelihoodPerturbation q h 0 block) +
    Real.log (1 + pureCyclicPauliLikelihoodPerturbation q h 1 block)

/-- Complete finite-row log-likelihood ratio on the common product space. -/
def pureCyclicPauliLogLikelihoodRatio
    (h : Fin 2 -> ℝ) (q : ℕ) (omega : PureCyclicPauliOmega) : ℝ :=
  ∑ k ∈ Finset.range q,
    pureCyclicPauliBlockLogLikelihoodRatio q h (omega k)

/-- Complete finite-row sum of scalar logarithm residuals. -/
def pureCyclicPauliLikelihoodRemainder
    (h : Fin 2 -> ℝ) (q : ℕ) (omega : PureCyclicPauliOmega) : ℝ :=
  if q = 0 then pureCyclicPauliFisherQuadratic h / 2
  else
    ∑ k ∈ Finset.range q,
      (pureCyclicPauliLogRemainder
          (pureCyclicPauliLikelihoodPerturbation q h 0 (omega k)) +
        pureCyclicPauliLogRemainder
          (pureCyclicPauliLikelihoodPerturbation q h 1 (omega k)))

theorem pureCyclicPauliBlockLogLikelihoodRatio_exact
    (q : ℕ) (h : Fin 2 -> ℝ) (block : PureCyclicPauliBlock) :
    pureCyclicPauliBlockLogLikelihoodRatio q h block =
      pureCyclicPauliBlockLinearTerm q h block -
        pureCyclicPauliBlockQuadraticTerm q h block / 2 +
        (pureCyclicPauliLogRemainder
          (pureCyclicPauliLikelihoodPerturbation q h 0 block) +
        pureCyclicPauliLogRemainder
          (pureCyclicPauliLikelihoodPerturbation q h 1 block)) := by
  rw [pureCyclicPauliBlockLogLikelihoodRatio,
    pureCyclicPauliLog_exact_secondOrder,
    pureCyclicPauliLog_exact_secondOrder]
  unfold pureCyclicPauliBlockLinearTerm pureCyclicPauliBlockQuadraticTerm
  ring

theorem pureCyclicPauliBlockLinearTerm_eq_score
    (q : ℕ) (h : Fin 2 -> ℝ) (block : PureCyclicPauliBlock) :
    pureCyclicPauliBlockLinearTerm q h block =
      (Real.sqrt q)⁻¹ * pureCyclicPauliBlockScore h block := by
  unfold pureCyclicPauliBlockLinearTerm
    pureCyclicPauliLikelihoodPerturbation pureCyclicPauliLocalTilt
    pureCyclicPauliBlockScore
  field_simp

theorem pureCyclicPauliBlockQuadraticTerm_eq_fisher_div
    {q : ℕ} (hq : 0 < q) (h : Fin 2 -> ℝ)
    (block : PureCyclicPauliBlock) :
    pureCyclicPauliBlockQuadraticTerm q h block =
      pureCyclicPauliFisherQuadratic h / q := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hsqrt : Real.sqrt (q : ℝ) ^ 2 = q :=
    Real.sq_sqrt (Nat.cast_nonneg q)
  unfold pureCyclicPauliBlockQuadraticTerm
    pureCyclicPauliLikelihoodPerturbation pureCyclicPauliLocalTilt
    pureCyclicPauliFisherQuadratic
  rw [mul_pow, mul_pow,
    pureCyclicPauliBlockCoordinate_sq_one,
    pureCyclicPauliBlockCoordinate_sq_one]
  simp only [div_pow, mul_pow]
  rw [hsqrt, Fin.sum_univ_two]
  field_simp [hq0]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) <= 2)]
  ring

theorem pureCyclicPauliLinearTerm_sum_eq_normalizedScore
    (q : ℕ) (h : Fin 2 -> ℝ) (omega : PureCyclicPauliOmega) :
    (∑ k ∈ Finset.range q,
      pureCyclicPauliBlockLinearTerm q h (omega k)) =
      pureCyclicPauliNormalizedScore h q omega := by
  simp_rw [pureCyclicPauliBlockLinearTerm_eq_score]
  rw [← Finset.mul_sum]
  rfl

theorem pureCyclicPauliQuadraticTerm_sum_eq_fisher
    {q : ℕ} (hq : 0 < q) (h : Fin 2 -> ℝ)
    (omega : PureCyclicPauliOmega) :
    (∑ k ∈ Finset.range q,
      pureCyclicPauliBlockQuadraticTerm q h (omega k)) =
      pureCyclicPauliFisherQuadratic h := by
  simp_rw [pureCyclicPauliBlockQuadraticTerm_eq_fisher_div hq h]
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp [hq0]

/-- Exact LAN algebra for every positive number of complete cycles. -/
theorem pureCyclicPauliLogLikelihoodRatio_exact_LAN
    {q : ℕ} (hq : 0 < q) (h : Fin 2 -> ℝ)
    (omega : PureCyclicPauliOmega) :
    pureCyclicPauliLogLikelihoodRatio h q omega =
      pureCyclicPauliNormalizedScore h q omega -
        pureCyclicPauliFisherQuadratic h / 2 +
        pureCyclicPauliLikelihoodRemainder h q omega := by
  unfold pureCyclicPauliLogLikelihoodRatio
  simp_rw [pureCyclicPauliBlockLogLikelihoodRatio_exact]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.sum_div]
  have hlinear := pureCyclicPauliLinearTerm_sum_eq_normalizedScore q h omega
  have hquadratic :=
    pureCyclicPauliQuadraticTerm_sum_eq_fisher hq h omega
  rw [hlinear]
  unfold pureCyclicPauliLikelihoodRemainder
  rw [if_neg hq.ne']
  exact congrArg
    (fun Q : ℝ =>
      pureCyclicPauliNormalizedScore h q omega - Q / 2 +
        ∑ k ∈ Finset.range q,
          (pureCyclicPauliLogRemainder
              (pureCyclicPauliLikelihoodPerturbation q h 0 (omega k)) +
            pureCyclicPauliLogRemainder
              (pureCyclicPauliLikelihoodPerturbation q h 1 (omega k))))
    hquadratic

/-- Uniform envelope for all scalar perturbations in row `q`. -/
def pureCyclicPauliPerturbationEnvelope
    (q : ℕ) (h : Fin 2 -> ℝ) : ℝ :=
  Real.sqrt 2 * max |h 0| |h 1| / Real.sqrt q

theorem pureCyclicPauliLikelihoodPerturbation_abs
    (q : ℕ) (h : Fin 2 -> ℝ) (axis : Fin 2)
    (block : PureCyclicPauliBlock) :
    |pureCyclicPauliLikelihoodPerturbation q h axis block| =
      Real.sqrt 2 * |h axis| / Real.sqrt q := by
  rw [pureCyclicPauliLikelihoodPerturbation, pureCyclicPauliLocalTilt,
    abs_mul, abs_div, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg 2),
    abs_of_nonneg (Real.sqrt_nonneg q),
    pureCyclicPauliBlockCoordinate_abs_eq_one]
  ring

theorem pureCyclicPauliLikelihoodPerturbation_abs_le_envelope
    (q : ℕ) (h : Fin 2 -> ℝ) (axis : Fin 2)
    (block : PureCyclicPauliBlock) :
    |pureCyclicPauliLikelihoodPerturbation q h axis block| <=
      pureCyclicPauliPerturbationEnvelope q h := by
  rw [pureCyclicPauliLikelihoodPerturbation_abs,
    pureCyclicPauliPerturbationEnvelope]
  have haxis : |h axis| <= max |h 0| |h 1| := by
    fin_cases axis
    · exact le_max_left _ _
    · exact le_max_right _ _
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left haxis (Real.sqrt_nonneg 2))
    (Real.sqrt_nonneg q)

theorem pureCyclicPauliPerturbationEnvelope_tendsto_zero
    (h : Fin 2 -> ℝ) :
    Tendsto (fun q : ℕ => pureCyclicPauliPerturbationEnvelope q h)
      atTop (nhds 0) := by
  have hsqrt : Tendsto (fun q : ℕ => Real.sqrt (q : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun q : ℕ => (Real.sqrt (q : ℝ))⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hsqrt
  simpa [pureCyclicPauliPerturbationEnvelope, div_eq_mul_inv] using
    hinv.const_mul (Real.sqrt 2 * max |h 0| |h 1|)

theorem pureCyclicPauliPerturbationEnvelope_eventually_le_half
    (h : Fin 2 -> ℝ) :
    ∀ᶠ q : ℕ in atTop,
      pureCyclicPauliPerturbationEnvelope q h <= 1 / 2 := by
  have hlt := (tendsto_order.1
    (pureCyclicPauliPerturbationEnvelope_tendsto_zero h)).2
      (1 / 2 : ℝ) (by norm_num)
  filter_upwards [hlt] with q hq
  exact le_of_lt hq

/-- Explicit `q^{-1/2}` envelope for the complete log remainder. -/
def pureCyclicPauliLikelihoodRemainderEnvelope
    (q : ℕ) (h : Fin 2 -> ℝ) : ℝ :=
  2 * ((Real.sqrt 2 * |h 0|) ^ 3 +
    (Real.sqrt 2 * |h 1|) ^ 3) / Real.sqrt q

theorem pureCyclicPauliLikelihoodRemainder_eq_sum
    {q : ℕ} (hq : 0 < q) (h : Fin 2 -> ℝ) :
    pureCyclicPauliLikelihoodRemainder h q =
      fun omega : PureCyclicPauliOmega =>
        ∑ k ∈ Finset.range q,
          (pureCyclicPauliLogRemainder
              (pureCyclicPauliLikelihoodPerturbation q h 0 (omega k)) +
            pureCyclicPauliLogRemainder
              (pureCyclicPauliLikelihoodPerturbation q h 1 (omega k))) := by
  funext omega
  simp [pureCyclicPauliLikelihoodRemainder, hq.ne']

theorem pureCyclicPauliLikelihoodRemainder_abs_le_envelope
    {q : ℕ} (hq : 0 < q) (h : Fin 2 -> ℝ)
    (hsmall : pureCyclicPauliPerturbationEnvelope q h <= 1 / 2)
    (omega : PureCyclicPauliOmega) :
    |pureCyclicPauliLikelihoodRemainder h q omega| <=
      pureCyclicPauliLikelihoodRemainderEnvelope q h := by
  have hsqrtPos : 0 < Real.sqrt (q : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hq)
  have hsqrtNe : Real.sqrt (q : ℝ) ≠ 0 := ne_of_gt hsqrtPos
  have hsqrtSq : Real.sqrt (q : ℝ) ^ 2 = q :=
    Real.sq_sqrt (Nat.cast_nonneg q)
  calc
    |pureCyclicPauliLikelihoodRemainder h q omega| =
        |∑ k ∈ Finset.range q,
          (pureCyclicPauliLogRemainder
              (pureCyclicPauliLikelihoodPerturbation q h 0 (omega k)) +
            pureCyclicPauliLogRemainder
              (pureCyclicPauliLikelihoodPerturbation q h 1 (omega k)))| := by
      rw [congrFun (pureCyclicPauliLikelihoodRemainder_eq_sum hq h) omega]
    _ <=
        ∑ k ∈ Finset.range q,
          |pureCyclicPauliLogRemainder
              (pureCyclicPauliLikelihoodPerturbation q h 0 (omega k)) +
            pureCyclicPauliLogRemainder
              (pureCyclicPauliLikelihoodPerturbation q h 1 (omega k))| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ k ∈ Finset.range q,
        (|pureCyclicPauliLogRemainder
            (pureCyclicPauliLikelihoodPerturbation q h 0 (omega k))| +
          |pureCyclicPauliLogRemainder
            (pureCyclicPauliLikelihoodPerturbation q h 1 (omega k))|) := by
      exact Finset.sum_le_sum fun k _ => abs_add_le _ _
    _ <= ∑ _k ∈ Finset.range q,
        (2 * (Real.sqrt 2 * |h 0| / Real.sqrt q) ^ 3 +
          2 * (Real.sqrt 2 * |h 1| / Real.sqrt q) ^ 3) := by
      apply Finset.sum_le_sum
      intro k _hk
      apply add_le_add
      · rw [← pureCyclicPauliLikelihoodPerturbation_abs q h 0 (omega k)]
        exact pureCyclicPauliLogRemainder_abs_le_two_cube
          ((pureCyclicPauliLikelihoodPerturbation_abs_le_envelope
            q h 0 (omega k)).trans hsmall)
      · rw [← pureCyclicPauliLikelihoodPerturbation_abs q h 1 (omega k)]
        exact pureCyclicPauliLogRemainder_abs_le_two_cube
          ((pureCyclicPauliLikelihoodPerturbation_abs_le_envelope
            q h 1 (omega k)).trans hsmall)
    _ = pureCyclicPauliLikelihoodRemainderEnvelope q h := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      unfold pureCyclicPauliLikelihoodRemainderEnvelope
      field_simp [hsqrtNe]
      rw [hsqrtSq]

theorem pureCyclicPauliLikelihoodRemainderEnvelope_tendsto_zero
    (h : Fin 2 -> ℝ) :
    Tendsto (fun q : ℕ => pureCyclicPauliLikelihoodRemainderEnvelope q h)
      atTop (nhds 0) := by
  have hsqrt : Tendsto (fun q : ℕ => Real.sqrt (q : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun q : ℕ => (Real.sqrt (q : ℝ))⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hsqrt
  simpa [pureCyclicPauliLikelihoodRemainderEnvelope, div_eq_mul_inv] using
    hinv.const_mul
      (2 * ((Real.sqrt 2 * |h 0|) ^ 3 +
        (Real.sqrt 2 * |h 1|) ^ 3))

/-- The complete pure cyclic likelihood remainder vanishes for every path. -/
theorem pureCyclicPauliLikelihoodRemainder_tendsto_zero
    (h : Fin 2 -> ℝ) (omega : PureCyclicPauliOmega) :
    Tendsto (fun q : ℕ => pureCyclicPauliLikelihoodRemainder h q omega)
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
  · filter_upwards [eventually_ge_atTop (1 : ℕ),
      pureCyclicPauliPerturbationEnvelope_eventually_le_half h]
      with q hq hsmall
    simpa [Real.norm_eq_abs] using
      pureCyclicPauliLikelihoodRemainder_abs_le_envelope hq h hsmall omega
  · exact pureCyclicPauliLikelihoodRemainderEnvelope_tendsto_zero h

/-- Measurability of every finite-row pure likelihood remainder. -/
theorem pureCyclicPauliLikelihoodRemainder_measurable
    (h : Fin 2 -> ℝ) (q : ℕ) :
    Measurable (pureCyclicPauliLikelihoodRemainder h q) := by
  by_cases hq : 0 < q
  · rw [pureCyclicPauliLikelihoodRemainder_eq_sum hq h]
    apply Finset.measurable_sum
    intro k _hk
    have hp (axis : Fin 2) : Measurable
        (fun omega : PureCyclicPauliOmega =>
          pureCyclicPauliLikelihoodPerturbation q h axis (omega k)) := by
      unfold pureCyclicPauliLikelihoodPerturbation
        pureCyclicPauliLocalTilt pureCyclicPauliBlockCoordinate
      fun_prop
    have hr (axis : Fin 2) : Measurable
        (fun omega : PureCyclicPauliOmega =>
          pureCyclicPauliLogRemainder
            (pureCyclicPauliLikelihoodPerturbation q h axis (omega k))) := by
      unfold pureCyclicPauliLogRemainder
      exact ((Real.measurable_log.comp (measurable_const.add (hp axis))).sub
        (hp axis)).add ((hp axis).pow_const 2 |>.div_const 2)
    exact (hr 0).add (hr 1)
  · have hq0 : q = 0 := Nat.eq_zero_of_not_pos hq
    subst q
    change Measurable (fun _ : PureCyclicPauliOmega =>
      pureCyclicPauliFisherQuadratic h / 2)
    fun_prop

theorem pureCyclicPauliLikelihoodRemainder_tendstoInMeasure
    (h : Fin 2 -> ℝ) :
    TendstoInMeasure pureCyclicPauliMeasure
      (pureCyclicPauliLikelihoodRemainder h) atTop
      (fun _ => (0 : ℝ)) := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro q
    exact (pureCyclicPauliLikelihoodRemainder_measurable h q).aestronglyMeasurable
  · filter_upwards with omega
    exact pureCyclicPauliLikelihoodRemainder_tendsto_zero h omega

/-- Scalar LAN, represented on the centered Gaussian probability space. -/
def PureCyclicPauliLAN (h : Fin 2 -> ℝ) : Prop :=
  TendstoInDistribution
    (pureCyclicPauliLogLikelihoodRatio h) atTop
    (fun z : ℝ => z - pureCyclicPauliFisherQuadratic h / 2)
    (fun _ => pureCyclicPauliMeasure)
    (gaussianReal 0 (pureCyclicPauliFisherQuadratic h).toNNReal)

/-- Complete kernel proof of scalar LAN for the pure tangent-Pauli cycle. -/
theorem pureCyclicPauli_LAN (h : Fin 2 -> ℝ) :
    PureCyclicPauliLAN h := by
  have hShift := (pureCyclicPauliNormalizedScore_CLT h).continuous_comp
    (g := fun z : ℝ => z - pureCyclicPauliFisherQuadratic h / 2)
    (by fun_prop)
  have hAdd := hShift.add_of_tendstoInMeasure_const
    (pureCyclicPauliLikelihoodRemainder_tendstoInMeasure h)
    (fun q => (pureCyclicPauliLikelihoodRemainder_measurable h q).aemeasurable)
  unfold PureCyclicPauliLAN
  apply TendstoInDistribution.congr
    (X := fun q omega =>
      (pureCyclicPauliNormalizedScore h q omega -
        pureCyclicPauliFisherQuadratic h / 2) +
        pureCyclicPauliLikelihoodRemainder h q omega)
    (Z := fun z : ℝ => z - pureCyclicPauliFisherQuadratic h / 2)
  · intro q
    filter_upwards with omega
    by_cases hq : 0 < q
    · rw [pureCyclicPauliLogLikelihoodRatio_exact_LAN hq]
    · have hq0 : q = 0 := Nat.eq_zero_of_not_pos hq
      subst q
      simp [pureCyclicPauliLogLikelihoodRatio,
        pureCyclicPauliNormalizedScore,
        pureCyclicPauliLikelihoodRemainder]
  · exact Filter.EventuallyEq.rfl
  · exact TendstoInDistribution.congr
      (fun q => Filter.Eventually.of_forall fun omega => by rfl)
      (Filter.Eventually.of_forall fun z => by simp [Function.comp_apply])
      hAdd

end

end QubitOracle.Paper
