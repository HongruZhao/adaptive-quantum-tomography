import QubitOracle.Paper.OneQubitMixedPolynomialPilotLANNegligible
import QubitOracle.Paper.OneQubitMixedPolynomialInformationConvergence
import QubitOracle.Paper.OneQubitMixedExactCycleTaylorRemainder
import QubitOracle.Paper.OneQubitMixedExactCycleObservedInformationLLN
import QubitOracle.Paper.OneQubitPolynomialTwoStageSchedule

/-!
# Total-scale residual certificate for the polynomial mixed-qubit protocol

This file uses the actual number of observations in one polynomial row:

* `3 * m^5` pilot observations;
* `3 * m^6` final observations, arranged as `m^6` complete three-axis cycles;
* `N_n = 3 * m^5 + 3 * m^6` observations in total.

The final-stage likelihood modules use the normalization `sqrt (3 * m^6)`.
The total-scale local direction is therefore

`h_n = sqrt ((3 * m^6) / N_n) * h`.

The file proves that this gives exactly the local perturbation
`theta + h / sqrt N_n`, lifts the pilot and conditional final-stage bounds to
the explicit joint finite-row measure, and constructs the complete LAN
residual certificate.  The only probabilistic input not proved algebraically
inside the qubit model is the already isolated finite-row Hoeffding contract
used by the polynomial information-convergence theorem.

The parser-defective final assembly module is deliberately not imported.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

namespace QubitOracle.Paper

noncomputable section

/-! ## Exact counts and total-scale normalization -/

/-- Number of complete three-Pauli pilot blocks in row `n`. -/
def mixedPolynomialTotalScalePilotBlocks (n : ℕ) : ℕ :=
  mixedPolynomialQPilot n

/-- Number of pilot observations in row `n`. -/
def mixedPolynomialTotalScalePilotObservations (n : ℕ) : ℕ :=
  3 * mixedPolynomialTotalScalePilotBlocks n

/-- Number of complete three-axis final cycles in row `n`. -/
def mixedPolynomialTotalScaleFinalCycles (n : ℕ) : ℕ :=
  mixedPolynomialRFinal n

/-- Number of final observations in row `n`. -/
def mixedPolynomialTotalScaleFinalObservations (n : ℕ) : ℕ :=
  3 * mixedPolynomialTotalScaleFinalCycles n

/-- Actual total number `N_n = 3*m^5 + 3*m^6` of observations. -/
def mixedPolynomialTotalScaleObservations (n : ℕ) : ℕ :=
  mixedPolynomialTotalScalePilotObservations n +
    mixedPolynomialTotalScaleFinalObservations n

@[simp] theorem mixedPolynomialTotalScalePilotBlocks_eq (n : ℕ) :
    mixedPolynomialTotalScalePilotBlocks n = (n + 1) ^ 5 := by
  simpa [mixedPolynomialTotalScalePilotBlocks] using
    (mixedPolynomialQPilot_eq n)

@[simp] theorem mixedPolynomialTotalScaleFinalCycles_eq (n : ℕ) :
    mixedPolynomialTotalScaleFinalCycles n = (n + 1) ^ 6 := by
  simpa [mixedPolynomialTotalScaleFinalCycles] using
    (mixedPolynomialRFinal_eq n)

@[simp] theorem mixedPolynomialTotalScalePilotObservations_eq (n : ℕ) :
    mixedPolynomialTotalScalePilotObservations n = 3 * (n + 1) ^ 5 := by
  simp [mixedPolynomialTotalScalePilotObservations]

@[simp] theorem mixedPolynomialTotalScaleFinalObservations_eq (n : ℕ) :
    mixedPolynomialTotalScaleFinalObservations n = 3 * (n + 1) ^ 6 := by
  simp [mixedPolynomialTotalScaleFinalObservations]

@[simp] theorem mixedPolynomialTotalScaleObservations_eq (n : ℕ) :
    mixedPolynomialTotalScaleObservations n =
      3 * (n + 1) ^ 5 + 3 * (n + 1) ^ 6 := by
  simp [mixedPolynomialTotalScaleObservations]

theorem mixedPolynomialTotalScalePilotBlocks_pos (n : ℕ) :
    0 < mixedPolynomialTotalScalePilotBlocks n := by
  simp [mixedPolynomialTotalScalePilotBlocks]

theorem mixedPolynomialTotalScaleFinalCycles_pos (n : ℕ) :
    0 < mixedPolynomialTotalScaleFinalCycles n := by
  simp [mixedPolynomialTotalScaleFinalCycles]

theorem mixedPolynomialTotalScaleFinalObservations_pos (n : ℕ) :
    0 < mixedPolynomialTotalScaleFinalObservations n := by
  unfold mixedPolynomialTotalScaleFinalObservations
  exact Nat.mul_pos (by norm_num)
    (mixedPolynomialTotalScaleFinalCycles_pos n)

theorem mixedPolynomialTotalScaleObservations_pos (n : ℕ) :
    0 < mixedPolynomialTotalScaleObservations n := by
  have hp := mixedPolynomialTotalScalePilotBlocks_pos n
  have hf := mixedPolynomialTotalScaleFinalCycles_pos n
  unfold mixedPolynomialTotalScaleObservations
    mixedPolynomialTotalScalePilotObservations
    mixedPolynomialTotalScaleFinalObservations
  omega

/-- Fraction of the actual total sample used by the final stage. -/
def mixedPolynomialTotalScaleFinalRatio (n : ℕ) : ℝ :=
  (mixedPolynomialTotalScaleFinalObservations n : ℝ) /
    (mixedPolynomialTotalScaleObservations n : ℝ)

/-- Square-root correction from final-stage scale to total scale. -/
def mixedPolynomialTotalScaleRootFinalRatio (n : ℕ) : ℝ :=
  Real.sqrt (mixedPolynomialTotalScaleFinalRatio n)

/-- Exact reduction of the final-to-total ratio to `m / (m + 1)`. -/
theorem mixedPolynomialTotalScaleFinalRatio_eq (n : ℕ) :
    mixedPolynomialTotalScaleFinalRatio n =
      (polynomialScheduleM n : ℝ) /
        ((polynomialScheduleM n : ℝ) + 1) := by
  unfold mixedPolynomialTotalScaleFinalRatio
  rw [mixedPolynomialTotalScaleFinalObservations_eq,
    mixedPolynomialTotalScaleObservations_eq]
  simp only [polynomialScheduleM, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  have hx : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hx]
  norm_num [Nat.cast_succ]
  ring

theorem mixedPolynomialTotalScaleFinalRatio_nonnegative (n : ℕ) :
    0 ≤ mixedPolynomialTotalScaleFinalRatio n := by
  unfold mixedPolynomialTotalScaleFinalRatio
  positivity

theorem mixedPolynomialTotalScaleFinalRatio_le_one (n : ℕ) :
    mixedPolynomialTotalScaleFinalRatio n ≤ 1 := by
  rw [mixedPolynomialTotalScaleFinalRatio_eq]
  have hm : 0 ≤ (polynomialScheduleM n : ℝ) := by positivity
  have hden : 0 < (polynomialScheduleM n : ℝ) + 1 := by positivity
  exact (div_le_one hden).2 (by linarith)

private theorem mixedPolynomialTotalScaleScheduleMReal_tendsto :
    Tendsto (fun n : ℕ => (polynomialScheduleM n : ℝ)) atTop atTop := by
  rw [tendsto_atTop]
  intro a
  filter_upwards
    [(tendsto_atTop.1 tendsto_natCast_atTop_atTop) a] with n hn
  calc
    a ≤ (n : ℝ) := hn
    _ ≤ (polynomialScheduleM n : ℝ) := by
      simp [polynomialScheduleM]

private theorem mixedPolynomialTotalScaleScheduleDenominator_tendsto :
    Tendsto
      (fun n : ℕ => (polynomialScheduleM n : ℝ) + 1)
      atTop atTop := by
  rw [tendsto_atTop]
  intro a
  filter_upwards
    [(tendsto_atTop.1 mixedPolynomialTotalScaleScheduleMReal_tendsto)
      (a - 1)] with n hn
  linarith

/-- The actual final-stage fraction tends to one. -/
theorem mixedPolynomialTotalScaleFinalRatio_tendsto_one :
    Tendsto mixedPolynomialTotalScaleFinalRatio atTop (nhds 1) := by
  have hinv :
      Tendsto
        (fun n : ℕ => ((polynomialScheduleM n : ℝ) + 1)⁻¹)
        atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp
      mixedPolynomialTotalScaleScheduleDenominator_tendsto
  have hrewrite :
      mixedPolynomialTotalScaleFinalRatio =
        fun n : ℕ => 1 - ((polynomialScheduleM n : ℝ) + 1)⁻¹ := by
    funext n
    rw [mixedPolynomialTotalScaleFinalRatio_eq]
    have hne : (polynomialScheduleM n : ℝ) + 1 ≠ 0 := by
      positivity
    field_simp [hne]
    ring
  rw [hrewrite]
  simpa using tendsto_const_nhds.sub hinv

/-- The square-root final-to-total correction tends to one. -/
theorem mixedPolynomialTotalScaleRootFinalRatio_tendsto_one :
    Tendsto mixedPolynomialTotalScaleRootFinalRatio atTop (nhds 1) := by
  unfold mixedPolynomialTotalScaleRootFinalRatio
  simpa [Function.comp_def] using
    Real.continuous_sqrt.continuousAt.tendsto.comp
      mixedPolynomialTotalScaleFinalRatio_tendsto_one

theorem mixedPolynomialTotalScaleRootFinalRatio_nonnegative (n : ℕ) :
    0 ≤ mixedPolynomialTotalScaleRootFinalRatio n :=
  Real.sqrt_nonneg _

theorem mixedPolynomialTotalScaleRootFinalRatio_le_one (n : ℕ) :
    mixedPolynomialTotalScaleRootFinalRatio n ≤ 1 := by
  have hsquare :
      mixedPolynomialTotalScaleRootFinalRatio n ^ 2 =
        mixedPolynomialTotalScaleFinalRatio n := by
    unfold mixedPolynomialTotalScaleRootFinalRatio
    exact Real.sq_sqrt
      (mixedPolynomialTotalScaleFinalRatio_nonnegative n)
  have hratio := mixedPolynomialTotalScaleFinalRatio_le_one n
  have hroot := mixedPolynomialTotalScaleRootFinalRatio_nonnegative n
  nlinarith

/-- The root correction is exactly the quotient of the two positive square
roots. -/
theorem mixedPolynomialTotalScaleRootFinalRatio_eq_sqrt_count_quotient
    (n : ℕ) :
    mixedPolynomialTotalScaleRootFinalRatio n =
      Real.sqrt (mixedPolynomialTotalScaleFinalObservations n : ℝ) /
        Real.sqrt (mixedPolynomialTotalScaleObservations n : ℝ) := by
  have hFinal :
      0 < (mixedPolynomialTotalScaleFinalObservations n : ℝ) := by
    exact_mod_cast mixedPolynomialTotalScaleFinalObservations_pos n
  unfold mixedPolynomialTotalScaleRootFinalRatio
    mixedPolynomialTotalScaleFinalRatio
  exact Real.sqrt_div (le_of_lt hFinal)
    (mixedPolynomialTotalScaleObservations n : ℝ)

/-- Direction used in the final-stage `sqrt (3*m^6)` normalization when the
scientific local parameter is normalized by the actual total count. -/
def mixedPolynomialTotalScaleDirection
    (n : ℕ) (h : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => mixedPolynomialTotalScaleRootFinalRatio n * h i

@[simp] theorem mixedPolynomialTotalScaleDirection_apply
    (n : ℕ) (h : Fin 3 → ℝ) (i : Fin 3) :
    mixedPolynomialTotalScaleDirection n h i =
      mixedPolynomialTotalScaleRootFinalRatio n * h i :=
  rfl

/-- The transported final local parameter is exactly
`theta + h / sqrt N_n`. -/
theorem mixedPolynomialTotalScaleLocalParameter_eq
    (theta h : Fin 3 → ℝ) (n : ℕ) :
    mixedExactCycleLocalParameter theta
        (mixedPolynomialTotalScaleDirection n h)
        (mixedPolynomialTotalScaleFinalCycles n) =
      fun i => theta i + h i /
        Real.sqrt (mixedPolynomialTotalScaleObservations n : ℝ) := by
  funext i
  have hFinal :
      0 < (mixedPolynomialTotalScaleFinalObservations n : ℝ) := by
    exact_mod_cast mixedPolynomialTotalScaleFinalObservations_pos n
  have hTotal :
      0 < (mixedPolynomialTotalScaleObservations n : ℝ) := by
    exact_mod_cast mixedPolynomialTotalScaleObservations_pos n
  have hsFinal :
      0 < Real.sqrt
        (mixedPolynomialTotalScaleFinalObservations n : ℝ) :=
    Real.sqrt_pos.2 hFinal
  have hsTotal :
      0 < Real.sqrt (mixedPolynomialTotalScaleObservations n : ℝ) :=
    Real.sqrt_pos.2 hTotal
  unfold mixedExactCycleLocalParameter mixedPolynomialTotalScaleDirection
  rw [mixedPolynomialTotalScaleRootFinalRatio_eq_sqrt_count_quotient]
  change theta i +
      ((Real.sqrt (mixedPolynomialTotalScaleFinalObservations n : ℝ) /
          Real.sqrt (mixedPolynomialTotalScaleObservations n : ℝ)) * h i) /
        Real.sqrt (mixedPolynomialTotalScaleFinalObservations n : ℝ) =
    theta i + h i /
      Real.sqrt (mixedPolynomialTotalScaleObservations n : ℝ)
  field_simp [ne_of_gt hsFinal, ne_of_gt hsTotal]

/-- The number of complete final cycles tends to infinity. -/
theorem mixedPolynomialTotalScaleFinalCycles_tendsto_atTop :
    Tendsto mixedPolynomialTotalScaleFinalCycles atTop atTop := by
  apply tendsto_atTop.2
  intro N
  filter_upwards [eventually_ge_atTop N] with n hn
  calc
    N ≤ n := hn
    _ ≤ n + 1 := Nat.le_succ n
    _ ≤ (n + 1) ^ 6 :=
      le_self_pow (by omega) (by norm_num)
    _ = mixedPolynomialTotalScaleFinalCycles n := by
      simp [mixedPolynomialTotalScaleFinalCycles]

/-! ## Scalar homogeneity needed for the transported direction -/

theorem mixedPolynomialTotalScale_blochDot_scale
    (c : ℝ) (h axis : Fin 3 → ℝ) :
    QubitOracle.blochDot (fun i => c * h i) axis =
      c * QubitOracle.blochDot h axis := by
  unfold QubitOracle.blochDot
  calc
    (∑ i : Fin 3, (c * h i) * axis i) =
        ∑ i : Fin 3, c * (h i * axis i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = c * ∑ i : Fin 3, h i * axis i := by
      rw [Finset.mul_sum]

theorem mixedPilotDirectionalEnvelope_scale
    (theta h : Fin 3 → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    mixedPilotDirectionalEnvelope theta (fun i => c * h i) =
      c * mixedPilotDirectionalEnvelope theta h := by
  unfold mixedPilotDirectionalEnvelope
  have habs (i : Fin 3) : |c * h i| = c * |h i| := by
    rw [abs_mul, abs_of_nonneg hc]
  simp_rw [habs]
  rw [← Finset.mul_sum]
  ring

theorem mixedProjectedScoreEnvelope_scale
    (theta h : Fin 3 → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    mixedProjectedScoreEnvelope theta (fun i => c * h i) =
      c * mixedProjectedScoreEnvelope theta h := by
  unfold mixedProjectedScoreEnvelope mixedProjectionL1
  have habs (i : Fin 3) : |c * h i| = c * |h i| := by
    rw [abs_mul, abs_of_nonneg hc]
  simp_rw [habs]
  rw [← Finset.mul_sum]
  ring

theorem mixedPilotOneShotDirectionalScore_scale
    (theta h : Fin 3 → ℝ) (c : ℝ) (j : Fin 3) (outcome : Bool) :
    mixedPilotOneShotDirectionalScore theta (fun i => c * h i) j outcome =
      c * mixedPilotOneShotDirectionalScore theta h j outcome := by
  unfold mixedPilotOneShotDirectionalScore
  ring

theorem mixedPilotBlockDirectionalScore_scale
    (theta h : Fin 3 → ℝ) (c : ℝ) (block : PauliPilotBlock) :
    mixedPilotBlockDirectionalScore theta (fun i => c * h i) block =
      c * mixedPilotBlockDirectionalScore theta h block := by
  unfold mixedPilotBlockDirectionalScore
  simp_rw [mixedPilotOneShotDirectionalScore_scale theta h c]
  rw [Finset.mul_sum]

theorem mixedPilotDirectionalScore_scale
    {q : ℕ} (theta h : Fin 3 → ℝ) (c : ℝ)
    (path : PauliPilotPath q) :
    mixedPilotDirectionalScore theta (fun i => c * h i) path =
      c * mixedPilotDirectionalScore theta h path := by
  unfold mixedPilotDirectionalScore
  simp_rw [mixedPilotBlockDirectionalScore_scale theta h c]
  rw [Finset.mul_sum]

theorem mixedPolynomialPilotNormalizedScore_scale
    (theta h : Fin 3 → ℝ) (c : ℝ) (n : ℕ)
    (path : PauliPilotPath (mixedPolynomialPilotBlocks n)) :
    mixedPolynomialPilotNormalizedScore theta (fun i => c * h i) n path =
      c * mixedPolynomialPilotNormalizedScore theta h n path := by
  unfold mixedPolynomialPilotNormalizedScore
  rw [mixedPilotDirectionalScore_scale theta h c path]
  ring

theorem mixedPolynomialPilotQuadraticEnvelope_scale
    (theta h : Fin 3 → ℝ) (c : ℝ) (hc : 0 ≤ c) (n : ℕ) :
    mixedPolynomialPilotQuadraticEnvelope theta (fun i => c * h i) n =
      c ^ 2 * mixedPolynomialPilotQuadraticEnvelope theta h n := by
  unfold mixedPolynomialPilotQuadraticEnvelope
  rw [mixedPilotDirectionalEnvelope_scale theta h c hc]
  ring

theorem mixedPolynomialPilotRemainderEnvelope_scale
    (theta h : Fin 3 → ℝ) (c : ℝ) (hc : 0 ≤ c) (n : ℕ) :
    mixedPolynomialPilotRemainderEnvelope theta (fun i => c * h i) n =
      c ^ 3 * mixedPolynomialPilotRemainderEnvelope theta h n := by
  unfold mixedPolynomialPilotRemainderEnvelope
  rw [mixedPilotDirectionalEnvelope_scale theta h c hc]
  ring

theorem mixedExactCycleCubicRemainderBound_scale
    (theta h : Fin 3 → ℝ) (c : ℝ) (hc : 0 ≤ c) (r : ℕ) :
    mixedExactCycleCubicRemainderBound theta (fun i => c * h i) r =
      c ^ 3 * mixedExactCycleCubicRemainderBound theta h r := by
  unfold mixedExactCycleCubicRemainderBound
  rw [mixedProjectedScoreEnvelope_scale theta h c hc]
  ring

theorem mixedExactCycleConditionalChebyshevBound_scale
    (theta h : Fin 3 → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (epsilon : ℝ) (r : ℕ) :
    mixedExactCycleConditionalChebyshevBound
        theta (fun i => c * h i) epsilon r =
      c ^ 4 * mixedExactCycleConditionalChebyshevBound theta h epsilon r := by
  unfold mixedExactCycleConditionalChebyshevBound
    mixedExactCycleObservedInformationVarianceConstant
  rw [mixedProjectedScoreEnvelope_scale theta h c hc]
  ring

/-! ## Explicit varying row law and elementary probability closure -/

/-- Actual finite sample space in polynomial row `n`. -/
abbrev MixedPolynomialTotalScaleRow (n : ℕ) :=
  MixedTwoStageFiniteRow
    (mixedPolynomialTotalScalePilotBlocks n)
    (mixedPolynomialTotalScaleFinalObservations n)

local instance mixedPolynomialTotalScalePilotMeasurableSpace (q : ℕ) :
    MeasurableSpace (PauliPilotPath q) := ⊤

local instance mixedPolynomialTotalScalePilotMeasurableSingletonClass (q : ℕ) :
    MeasurableSingletonClass (PauliPilotPath q) where
  measurableSet_singleton _ := MeasurableSet.of_discrete

local instance mixedPolynomialTotalScaleRowMeasurableSpace (n : ℕ) :
    MeasurableSpace (MixedPolynomialTotalScaleRow n) := ⊤

local instance mixedPolynomialTotalScaleRowMeasurableSingletonClass (n : ℕ) :
    MeasurableSingletonClass (MixedPolynomialTotalScaleRow n) where
  measurableSet_singleton _ := MeasurableSet.of_discrete

/-- Pilot-selected final frame in row `n`. -/
noncomputable def mixedPolynomialTotalScaleSelectedFrame
    (b : Fin 3 → ℝ) (n : ℕ) :
    PilotSelectedFinalFrame (mixedPolynomialTotalScalePilotBlocks n) :=
  mixedPolynomialPilotSelectedFinalFrame b n

/-- Explicit joint Born measure of one complete polynomial row. -/
def mixedPolynomialTotalScaleRowMeasure
    (theta b : Fin 3 → ℝ) (n : ℕ) :
    Measure (MixedPolynomialTotalScaleRow n) :=
  mixedTwoStageFiniteBornMeasure theta
    (mixedPolynomialTotalScaleSelectedFrame b n)

/-- Row-specific convergence in probability to zero. -/
def MixedPolynomialTotalScaleRowConvergesInProbability
    (theta b : Fin 3 → ℝ)
    (X : (n : ℕ) → MixedPolynomialTotalScaleRow n → ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    Tendsto
      (fun n : ℕ =>
        mixedPolynomialTotalScaleRowMeasure theta b n
          {row | epsilon ≤ |X n row|})
      atTop (nhds 0)

theorem mixedPolynomialTotalScaleRowConverges_congr
    (theta b : Fin 3 → ℝ)
    {X Y : (n : ℕ) → MixedPolynomialTotalScaleRow n → ℝ}
    (hXY : ∀ n row, X n row = Y n row)
    (hX : MixedPolynomialTotalScaleRowConvergesInProbability theta b X) :
    MixedPolynomialTotalScaleRowConvergesInProbability theta b Y := by
  intro epsilon hepsilon
  have hfun :
      (fun n : ℕ => mixedPolynomialTotalScaleRowMeasure theta b n
        {row | epsilon ≤ |X n row|}) =
      (fun n : ℕ => mixedPolynomialTotalScaleRowMeasure theta b n
        {row | epsilon ≤ |Y n row|}) := by
    funext n
    congr 1
    ext row
    simp only [Set.mem_setOf_eq, hXY n row]
  rw [← hfun]
  exact hX epsilon hepsilon

theorem mixedPolynomialTotalScaleRowConverges_neg
    (theta b : Fin 3 → ℝ)
    {X : (n : ℕ) → MixedPolynomialTotalScaleRow n → ℝ}
    (hX : MixedPolynomialTotalScaleRowConvergesInProbability theta b X) :
    MixedPolynomialTotalScaleRowConvergesInProbability theta b
      (fun n row => -X n row) := by
  intro epsilon hepsilon
  simpa only [abs_neg] using hX epsilon hepsilon

theorem mixedPolynomialTotalScaleRowConverges_add
    (theta b : Fin 3 → ℝ)
    {X Y : (n : ℕ) → MixedPolynomialTotalScaleRow n → ℝ}
    (hX : MixedPolynomialTotalScaleRowConvergesInProbability theta b X)
    (hY : MixedPolynomialTotalScaleRowConvergesInProbability theta b Y) :
    MixedPolynomialTotalScaleRowConvergesInProbability theta b
      (fun n row => X n row + Y n row) := by
  intro epsilon hepsilon
  have hhalf : 0 < epsilon / 2 := by linarith
  have hXt := hX (epsilon / 2) hhalf
  have hYt := hY (epsilon / 2) hhalf
  have hupper : ∀ n : ℕ,
      mixedPolynomialTotalScaleRowMeasure theta b n
          {row | epsilon ≤ |X n row + Y n row|} ≤
        mixedPolynomialTotalScaleRowMeasure theta b n
            {row | epsilon / 2 ≤ |X n row|} +
          mixedPolynomialTotalScaleRowMeasure theta b n
            {row | epsilon / 2 ≤ |Y n row|} := by
    intro n
    calc
      mixedPolynomialTotalScaleRowMeasure theta b n
          {row | epsilon ≤ |X n row + Y n row|} ≤
        mixedPolynomialTotalScaleRowMeasure theta b n
          ({row | epsilon / 2 ≤ |X n row|} ∪
            {row | epsilon / 2 ≤ |Y n row|}) := by
        apply measure_mono
        intro row hrow
        simp only [Set.mem_setOf_eq, Set.mem_union]
        change epsilon ≤ |X n row + Y n row| at hrow
        by_cases hx : epsilon / 2 ≤ |X n row|
        · exact Or.inl hx
        · right
          by_contra hy
          have hxlt : |X n row| < epsilon / 2 := lt_of_not_ge hx
          have hylt : |Y n row| < epsilon / 2 := lt_of_not_ge hy
          have hadd := abs_add_le (X n row) (Y n row)
          linarith
      _ ≤ mixedPolynomialTotalScaleRowMeasure theta b n
            {row | epsilon / 2 ≤ |X n row|} +
          mixedPolynomialTotalScaleRowMeasure theta b n
            {row | epsilon / 2 ≤ |Y n row|} :=
        measure_union_le _ _
  have hsum : Tendsto
      (fun n : ℕ =>
        mixedPolynomialTotalScaleRowMeasure theta b n
            {row | epsilon / 2 ≤ |X n row|} +
          mixedPolynomialTotalScaleRowMeasure theta b n
            {row | epsilon / 2 ≤ |Y n row|})
      atTop (nhds 0) := by
    simpa using hXt.add hYt
  exact Tendsto.squeeze tendsto_const_nhds hsum
    (fun _ => bot_le) hupper

theorem mixedPolynomialTotalScaleRowConverges_sub
    (theta b : Fin 3 → ℝ)
    {X Y : (n : ℕ) → MixedPolynomialTotalScaleRow n → ℝ}
    (hX : MixedPolynomialTotalScaleRowConvergesInProbability theta b X)
    (hY : MixedPolynomialTotalScaleRowConvergesInProbability theta b Y) :
    MixedPolynomialTotalScaleRowConvergesInProbability theta b
      (fun n row => X n row - Y n row) := by
  simpa only [sub_eq_add_neg] using
    mixedPolynomialTotalScaleRowConverges_add theta b hX
      (mixedPolynomialTotalScaleRowConverges_neg theta b hY)

theorem mixedPolynomialTotalScaleRowConverges_of_dominated
    (theta b : Fin 3 → ℝ)
    {X Y : (n : ℕ) → MixedPolynomialTotalScaleRow n → ℝ}
    (hdom : ∀ n row, |X n row| ≤ |Y n row|)
    (hY : MixedPolynomialTotalScaleRowConvergesInProbability theta b Y) :
    MixedPolynomialTotalScaleRowConvergesInProbability theta b X := by
  intro epsilon hepsilon
  have hupper : ∀ n : ℕ,
      mixedPolynomialTotalScaleRowMeasure theta b n
          {row | epsilon ≤ |X n row|} ≤
        mixedPolynomialTotalScaleRowMeasure theta b n
          {row | epsilon ≤ |Y n row|} := by
    intro n
    apply measure_mono
    intro row hrow
    exact hrow.trans (hdom n row)
  exact Tendsto.squeeze tendsto_const_nhds (hY epsilon hepsilon)
    (fun _ => bot_le) hupper

theorem mixedPolynomialTotalScaleRowConverges_of_eventually_uniform
    (theta b : Fin 3 → ℝ)
    {X : (n : ℕ) → MixedPolynomialTotalScaleRow n → ℝ}
    (B : ℕ → ℝ) (hB : Tendsto B atTop (nhds 0))
    (hbound : ∀ᶠ n : ℕ in atTop,
      ∀ row : MixedPolynomialTotalScaleRow n, |X n row| ≤ B n) :
    MixedPolynomialTotalScaleRowConvergesInProbability theta b X := by
  intro epsilon hepsilon
  have hsmall : ∀ᶠ n : ℕ in atTop, B n < epsilon :=
    (tendsto_order.1 hB).2 epsilon hepsilon
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hbound, hsmall] with n hnBound hnSmall
  have hempty :
      {row : MixedPolynomialTotalScaleRow n | epsilon ≤ |X n row|} = ∅ := by
    ext row
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact not_le_of_gt ((hnBound row).trans_lt hnSmall)
  rw [hempty, measure_empty]

/-- Lift a pilot-only row convergence statement to the complete joint law by
the exact pilot marginal. -/
theorem mixedPolynomialTotalScaleRowConverges_of_pilot
    (theta b : Fin 3 → ℝ)
    (hphysical : PauliPilotPhysicalBloch theta)
    (X : (n : ℕ) →
      PauliPilotPath (mixedPolynomialTotalScalePilotBlocks n) → ℝ)
    (hX : ∀ epsilon : ℝ, 0 < epsilon →
      Tendsto
        (fun n : ℕ =>
          pauliPilotBornProductMeasure theta
            {path | epsilon ≤ |X n path|})
        atTop (nhds 0)) :
    MixedPolynomialTotalScaleRowConvergesInProbability theta b
      (fun n row => X n row.1) := by
  intro epsilon hepsilon
  have hfun :
      (fun n : ℕ =>
        mixedPolynomialTotalScaleRowMeasure theta b n
          {row | epsilon ≤ |X n row.1|}) =
      (fun n : ℕ =>
        pauliPilotBornProductMeasure theta
          {path | epsilon ≤ |X n path|}) := by
    funext n
    change mixedTwoStageFiniteBornMeasure theta
        (mixedPolynomialTotalScaleSelectedFrame b n)
        ((fun row : MixedPolynomialTotalScaleRow n => row.1) ⁻¹'
          {path | epsilon ≤ |X n path|}) =
      pauliPilotBornProductMeasure theta
        {path | epsilon ≤ |X n path|}
    exact mixedTwoStageFiniteBornMeasure_pilotMarginal
      (T := mixedPolynomialTotalScaleFinalObservations n)
      theta (mixedPolynomialTotalScaleSelectedFrame b n)
      hphysical {path | epsilon ≤ |X n path|}
  rw [hfun]
  exact hX epsilon hepsilon

/-- Integrate a pilot-uniform conditional event bound under the explicit joint
row law. -/
theorem mixedPolynomialTotalScaleRowMeasure_dependentFinalEvent_le
    (theta b : Fin 3 → ℝ)
    (hphysical : PauliPilotPhysicalBloch theta)
    (n : ℕ)
    (event :
      (pilot : PauliPilotPath (mixedPolynomialTotalScalePilotBlocks n)) →
        Set (MixedTwoStageFinalPath
          (mixedPolynomialTotalScaleFinalObservations n)))
    (B : ℝ)
    (hconditional : ∀ pilot,
      mixedTwoStageConditionalFinalEventMass theta
          (mixedPolynomialTotalScaleSelectedFrame b n) pilot
          (event pilot) ≤ B) :
    mixedPolynomialTotalScaleRowMeasure theta b n
        {row | row.2 ∈ event row.1} ≤
      ENNReal.ofReal B := by
  classical
  rw [mixedPolynomialTotalScaleRowMeasure,
    mixedTwoStageFiniteBornMeasure_apply theta
      (mixedPolynomialTotalScaleSelectedFrame b n) hphysical]
  apply ENNReal.ofReal_le_ofReal
  calc
    (∑ row : MixedPolynomialTotalScaleRow n,
      if row ∈ {row | row.2 ∈ event row.1} then
        mixedTwoStageFiniteRowMass theta
          (mixedPolynomialTotalScaleSelectedFrame b n) row
      else 0) =
        ∑ pilot : PauliPilotPath
            (mixedPolynomialTotalScalePilotBlocks n),
          pauliPilotPathMass theta pilot *
            mixedTwoStageConditionalFinalEventMass theta
              (mixedPolynomialTotalScaleSelectedFrame b n) pilot
              (event pilot) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro pilot _
      simpa only [Set.mem_setOf_eq] using
        (mixedTwoStageFiniteRowMass_pilotFiberEvent_factorization
          theta (mixedPolynomialTotalScaleSelectedFrame b n)
          pilot (event pilot))
    _ ≤ ∑ pilot : PauliPilotPath
            (mixedPolynomialTotalScalePilotBlocks n),
          pauliPilotPathMass theta pilot * B := by
      apply Finset.sum_le_sum
      intro pilot _
      exact mul_le_mul_of_nonneg_left (hconditional pilot)
        (pauliPilotPathMass_nonnegative theta hphysical pilot)
    _ = B := by
      rw [← Finset.sum_mul, pauliPilotPathMass_sum_one]
      simp

/-! ## Pilot likelihood at the actual total scale -/

/-- Pilot likelihood contribution for the local perturbation normalized by the
actual total count. -/
def mixedPolynomialTotalScalePilotLogLikelihood
    (theta h : Fin 3 → ℝ) (n : ℕ)
    (path : PauliPilotPath (mixedPolynomialTotalScalePilotBlocks n)) : ℝ :=
  mixedPolynomialPilotLogLikelihood theta
    (mixedPolynomialTotalScaleDirection n h) n path

theorem mixedPolynomialTotalScalePilotErrorEnvelope_le
    (theta h : Fin 3 → ℝ) (hInterior : MixedPilotStrictInterior theta)
    (n : ℕ) :
    mixedPolynomialPilotLikelihoodErrorEnvelope theta
        (mixedPolynomialTotalScaleDirection n h) n ≤
      mixedPolynomialPilotLikelihoodErrorEnvelope theta h n := by
  let c := mixedPolynomialTotalScaleRootFinalRatio n
  have hc : 0 ≤ c := mixedPolynomialTotalScaleRootFinalRatio_nonnegative n
  have hc1 : c ≤ 1 := mixedPolynomialTotalScaleRootFinalRatio_le_one n
  have hc2 : c ^ 2 ≤ 1 := pow_le_one₀ hc hc1
  have hc3 : c ^ 3 ≤ 1 := pow_le_one₀ hc hc1
  have hquadNonneg :=
    mixedPolynomialPilotQuadraticEnvelope_nonneg theta h hInterior n
  have hremNonneg :=
    mixedPolynomialPilotRemainderEnvelope_nonneg theta h hInterior n
  unfold mixedPolynomialPilotLikelihoodErrorEnvelope
  rw [show mixedPolynomialTotalScaleDirection n h =
      (fun i => c * h i) by rfl,
    mixedPolynomialPilotQuadraticEnvelope_scale theta h c hc n,
    mixedPolynomialPilotRemainderEnvelope_scale theta h c hc n]
  exact add_le_add
    (div_le_div_of_nonneg_right
      (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hc2 hquadNonneg)
      (by norm_num))
    (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hc3 hremNonneg)

theorem mixedPolynomialTotalScalePilotTaylorCondition_eventually
    (theta h : Fin 3 → ℝ) (hInterior : MixedPilotStrictInterior theta) :
    ∀ᶠ n : ℕ in atTop,
      mixedPilotDirectionalEnvelope theta
          (mixedPolynomialTotalScaleDirection n h) /
        Real.sqrt (mixedPolynomialPilotLANScale n : ℝ) ≤ 1 / 2 := by
  have hfixed := mixedPolynomialPilotTaylorCondition_eventually
    theta h hInterior
  filter_upwards [hfixed] with n hn
  let c := mixedPolynomialTotalScaleRootFinalRatio n
  have hc : 0 ≤ c := mixedPolynomialTotalScaleRootFinalRatio_nonnegative n
  have hc1 : c ≤ 1 := mixedPolynomialTotalScaleRootFinalRatio_le_one n
  have hEnvelopeNonneg := mixedPilotDirectionalEnvelope_nonneg theta h hInterior
  have hscaledEnvelope :
      mixedPilotDirectionalEnvelope theta
          (mixedPolynomialTotalScaleDirection n h) ≤
        mixedPilotDirectionalEnvelope theta h := by
    rw [show mixedPolynomialTotalScaleDirection n h =
        (fun i => c * h i) by rfl,
      mixedPilotDirectionalEnvelope_scale theta h c hc]
    nlinarith [mul_nonneg (sub_nonneg.mpr hc1) hEnvelopeNonneg]
  exact (div_le_div_of_nonneg_right hscaledEnvelope
    (Real.sqrt_nonneg _)).trans hn

/-- The total-scale pilot likelihood is negligible under its finite pilot law.
This is proved uniformly from the fixed-direction score and deterministic
Taylor envelopes. -/
theorem mixedPolynomialTotalScalePilotLogLikelihood_negligibleInPilotProbability
    (theta h : Fin 3 → ℝ) (hInterior : MixedPilotStrictInterior theta) :
    ∀ epsilon : ℝ, 0 < epsilon →
      Tendsto
        (fun n : ℕ =>
          pauliPilotBornProductMeasure theta
            {path : PauliPilotPath
                (mixedPolynomialTotalScalePilotBlocks n) |
              epsilon ≤
                |mixedPolynomialTotalScalePilotLogLikelihood
                  theta h n path|})
        atTop (nhds 0) := by
  intro epsilon hepsilon
  have hhalf : 0 < epsilon / 2 := by linarith
  have hscore :=
    mixedPolynomialPilotNormalizedScore_convergesInProbability
      theta h hInterior (epsilon / 2) hhalf
  have hsmall :=
    mixedPolynomialTotalScalePilotTaylorCondition_eventually
      theta h hInterior
  have herrorSmall : ∀ᶠ n : ℕ in atTop,
      mixedPolynomialPilotLikelihoodErrorEnvelope theta h n < epsilon / 2 :=
    (tendsto_order.1
      (mixedPolynomialPilotLikelihoodErrorEnvelope_tendsto_zero theta h)).2
      (epsilon / 2) hhalf
  have hupper : ∀ᶠ n : ℕ in atTop,
      pauliPilotBornProductMeasure theta
          {path : PauliPilotPath
              (mixedPolynomialTotalScalePilotBlocks n) |
            epsilon ≤
              |mixedPolynomialTotalScalePilotLogLikelihood theta h n path|} ≤
        pauliPilotBornProductMeasure theta
          {path : PauliPilotPath
              (mixedPolynomialTotalScalePilotBlocks n) |
            epsilon / 2 ≤
              |mixedPolynomialPilotNormalizedScore theta h n path|} := by
    filter_upwards [hsmall, herrorSmall] with n hnSmall hnError
    apply measure_mono
    intro path hpath
    change epsilon / 2 ≤
      |mixedPolynomialPilotNormalizedScore theta h n path|
    by_contra hscoreNot
    have hscoreLt :
        |mixedPolynomialPilotNormalizedScore theta h n path| < epsilon / 2 :=
      lt_of_not_ge hscoreNot
    let c := mixedPolynomialTotalScaleRootFinalRatio n
    have hc : 0 ≤ c := mixedPolynomialTotalScaleRootFinalRatio_nonnegative n
    have hc1 : c ≤ 1 := mixedPolynomialTotalScaleRootFinalRatio_le_one n
    have hscaledScore :
        |mixedPolynomialPilotNormalizedScore theta
            (mixedPolynomialTotalScaleDirection n h) n path| ≤
          |mixedPolynomialPilotNormalizedScore theta h n path| := by
      rw [show mixedPolynomialTotalScaleDirection n h =
          (fun i => c * h i) by rfl,
        mixedPolynomialPilotNormalizedScore_scale theta h c n path,
        abs_mul, abs_of_nonneg hc]
      exact mul_le_of_le_one_left (abs_nonneg _) hc1
    have herror :=
      abs_mixedPolynomialPilotLogLikelihood_sub_score_le
        theta (mixedPolynomialTotalScaleDirection n h) hInterior n hnSmall path
    have herrorLe := mixedPolynomialTotalScalePilotErrorEnvelope_le
      theta h hInterior n
    have hlogUpper :
        |mixedPolynomialTotalScalePilotLogLikelihood theta h n path| <
          epsilon := by
      unfold mixedPolynomialTotalScalePilotLogLikelihood
      have htriangle :
          |mixedPolynomialPilotLogLikelihood theta
              (mixedPolynomialTotalScaleDirection n h) n path| ≤
            |mixedPolynomialPilotNormalizedScore theta
                (mixedPolynomialTotalScaleDirection n h) n path| +
              |mixedPolynomialPilotLogLikelihood theta
                  (mixedPolynomialTotalScaleDirection n h) n path -
                mixedPolynomialPilotNormalizedScore theta
                  (mixedPolynomialTotalScaleDirection n h) n path| := by
        calc
          |mixedPolynomialPilotLogLikelihood theta
              (mixedPolynomialTotalScaleDirection n h) n path| =
            |mixedPolynomialPilotNormalizedScore theta
                (mixedPolynomialTotalScaleDirection n h) n path +
              (mixedPolynomialPilotLogLikelihood theta
                  (mixedPolynomialTotalScaleDirection n h) n path -
                mixedPolynomialPilotNormalizedScore theta
                  (mixedPolynomialTotalScaleDirection n h) n path)| := by
              congr 1
              ring
          _ ≤ _ := abs_add_le _ _
      calc
        |mixedPolynomialPilotLogLikelihood theta
            (mixedPolynomialTotalScaleDirection n h) n path| ≤
          |mixedPolynomialPilotNormalizedScore theta
              (mixedPolynomialTotalScaleDirection n h) n path| +
            |mixedPolynomialPilotLogLikelihood theta
                (mixedPolynomialTotalScaleDirection n h) n path -
              mixedPolynomialPilotNormalizedScore theta
                (mixedPolynomialTotalScaleDirection n h) n path| := by
          exact htriangle
        _ ≤ |mixedPolynomialPilotNormalizedScore theta h n path| +
            mixedPolynomialPilotLikelihoodErrorEnvelope theta h n :=
          add_le_add hscaledScore (herror.trans herrorLe)
        _ < epsilon := by linarith
    exact (not_lt_of_ge hpath) hlogUpper
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hscore
    (Filter.Eventually.of_forall fun _ => bot_le) hupper

/-- The same pilot negligibility under the complete joint row law. -/
theorem mixedPolynomialTotalScalePilotLogLikelihood_negligibleInProbability
    (theta h b : Fin 3 → ℝ)
    (hInterior : MixedPilotStrictInterior theta) :
    MixedPolynomialTotalScaleRowConvergesInProbability theta b
      (fun n row =>
        mixedPolynomialTotalScalePilotLogLikelihood theta h n row.1) := by
  exact mixedPolynomialTotalScaleRowConverges_of_pilot theta b
    (mixedPilotStrictInterior_physical theta hInterior)
    (mixedPolynomialTotalScalePilotLogLikelihood theta h)
    (mixedPolynomialTotalScalePilotLogLikelihood_negligibleInPilotProbability
      theta h hInterior)

/-! ## Final-stage Taylor remainder at total scale -/

/-- Final conditional log likelihood after transporting the total-scale local
direction to the exact-cycle normalization. -/
def mixedPolynomialTotalScaleFinalLogLikelihood
    (theta h b : Fin 3 → ℝ) (n : ℕ)
    (row : MixedPolynomialTotalScaleRow n) : ℝ :=
  mixedExactCycleConditionalLogLikelihoodRatio theta
    (mixedPolynomialTotalScaleDirection n h)
    (mixedPolynomialTotalScaleSelectedFrame b n) row.1 row.2

/-- Final root-information score term at total scale. -/
def mixedPolynomialTotalScaleFinalLinearScore
    (theta h b : Fin 3 → ℝ) (n : ℕ)
    (row : MixedPolynomialTotalScaleRow n) : ℝ :=
  mixedExactCycleLinearScoreTerm theta
    (mixedPolynomialTotalScaleDirection n h)
    (mixedPolynomialTotalScaleSelectedFrame b n) row.1 row.2

/-- Final-stage cubic Taylor remainder at total scale. -/
def mixedPolynomialTotalScaleFinalTaylorRemainder
    (theta h b : Fin 3 → ℝ) (n : ℕ)
    (row : MixedPolynomialTotalScaleRow n) : ℝ :=
  mixedExactCycleTaylorRemainder theta
    (mixedPolynomialTotalScaleDirection n h)
    (mixedPolynomialTotalScaleSelectedFrame b n) row.1 row.2

theorem mixedPolynomialTotalScaleFinalTaylorRemainder_convergesInProbability
    (theta h b : Fin 3 → ℝ)
    (hInterior : QubitOracle.blochNormSq theta < 1) :
    MixedPolynomialTotalScaleRowConvergesInProbability theta b
      (mixedPolynomialTotalScaleFinalTaylorRemainder theta h b) := by
  let B : ℕ → ℝ := fun n =>
    mixedExactCycleCubicRemainderBound theta h
      (mixedPolynomialTotalScaleFinalCycles n)
  have hB : Tendsto B atTop (nhds 0) :=
    (mixedExactCycleCubicRemainderBound_tendsto_zero theta h).comp
      mixedPolynomialTotalScaleFinalCycles_tendsto_atTop
  have hsmallFixed : ∀ᶠ n : ℕ in atTop,
      mixedProjectedScoreEnvelope theta h /
          Real.sqrt
            (3 * mixedPolynomialTotalScaleFinalCycles n : ℕ) ≤ 1 / 2 :=
    mixedPolynomialTotalScaleFinalCycles_tendsto_atTop.eventually
      (mixedExactCycleNormalizedEnvelope_eventually_le_half theta h)
  have hbound : ∀ᶠ n : ℕ in atTop,
      ∀ row : MixedPolynomialTotalScaleRow n,
        |mixedPolynomialTotalScaleFinalTaylorRemainder theta h b n row| ≤
          B n := by
    filter_upwards [hsmallFixed] with n hnSmall
    intro row
    let c := mixedPolynomialTotalScaleRootFinalRatio n
    have hc : 0 ≤ c := mixedPolynomialTotalScaleRootFinalRatio_nonnegative n
    have hc1 : c ≤ 1 := mixedPolynomialTotalScaleRootFinalRatio_le_one n
    have hEnvelopeNonneg :=
      mixedExactCycleProjectedScoreEnvelope_nonnegative theta h hInterior
    have hscaledEnvelope :
        mixedProjectedScoreEnvelope theta
            (mixedPolynomialTotalScaleDirection n h) ≤
          mixedProjectedScoreEnvelope theta h := by
      rw [show mixedPolynomialTotalScaleDirection n h =
          (fun i => c * h i) by rfl,
        mixedProjectedScoreEnvelope_scale theta h c hc]
      nlinarith [mul_nonneg (sub_nonneg.mpr hc1) hEnvelopeNonneg]
    have hsmallScaled :
        mixedProjectedScoreEnvelope theta
            (mixedPolynomialTotalScaleDirection n h) /
          Real.sqrt
            (3 * mixedPolynomialTotalScaleFinalCycles n : ℕ) ≤ 1 / 2 :=
      (div_le_div_of_nonneg_right hscaledEnvelope (Real.sqrt_nonneg _)).trans
        hnSmall
    have hTaylor := mixedExactCycleTaylorRemainder_abs_le_cubicBound
      theta (mixedPolynomialTotalScaleDirection n h)
      (mixedPolynomialTotalScaleSelectedFrame b n) row.1 row.2
      hInterior (mixedPolynomialTotalScaleFinalCycles_pos n) hsmallScaled
    have hfixedBoundNonneg : 0 ≤ B n := by
      unfold B mixedExactCycleCubicRemainderBound
      exact div_nonneg
        (mul_nonneg (by norm_num)
          (pow_nonneg hEnvelopeNonneg 3)) (Real.sqrt_nonneg _)
    have hc3 : c ^ 3 ≤ 1 := pow_le_one₀ hc hc1
    have hscaledBound :
        mixedExactCycleCubicRemainderBound theta
            (mixedPolynomialTotalScaleDirection n h)
            (mixedPolynomialTotalScaleFinalCycles n) ≤ B n := by
      rw [show mixedPolynomialTotalScaleDirection n h =
          (fun i => c * h i) by rfl,
        mixedExactCycleCubicRemainderBound_scale theta h c hc]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hc3 hfixedBoundNonneg
    exact hTaylor.trans hscaledBound
  exact mixedPolynomialTotalScaleRowConverges_of_eventually_uniform
    theta b B hB hbound

/-! ## Observed information under the joint row law -/

/-- Observed final quadratic score at total scale. -/
def mixedPolynomialTotalScaleObservedQuadratic
    (theta h b : Fin 3 → ℝ) (n : ℕ)
    (row : MixedPolynomialTotalScaleRow n) : ℝ :=
  mixedExactCycleObservedQuadraticTerm theta
    (mixedPolynomialTotalScaleDirection n h)
    (mixedPolynomialTotalScaleSelectedFrame b n) row.1 row.2

/-- Conditional expected final quadratic score. -/
def mixedPolynomialTotalScaleExpectedFisher
    (theta h b : Fin 3 → ℝ) (n : ℕ)
    (pilot : PauliPilotPath (mixedPolynomialTotalScalePilotBlocks n)) : ℝ :=
  mixedExactCycleObservedQuadraticConditionalExpectation
    (r := mixedPolynomialTotalScaleFinalCycles n) theta
    (mixedPolynomialTotalScaleDirection n h)
    (mixedPolynomialTotalScaleSelectedFrame b n) pilot

/-- Centered observed-information fluctuation. -/
def mixedPolynomialTotalScaleObservedInformationCentered
    (theta h b : Fin 3 → ℝ) (n : ℕ)
    (row : MixedPolynomialTotalScaleRow n) : ℝ :=
  mixedPolynomialTotalScaleObservedQuadratic theta h b n row -
    mixedPolynomialTotalScaleExpectedFisher theta h b n row.1

set_option maxHeartbeats 800000 in
theorem mixedPolynomialTotalScaleObservedInformationCentered_convergesInProbability
    (theta h b : Fin 3 → ℝ)
    (hInterior : QubitOracle.blochNormSq theta < 1) :
    MixedPolynomialTotalScaleRowConvergesInProbability theta b
      (mixedPolynomialTotalScaleObservedInformationCentered theta h b) := by
  intro epsilon hepsilon
  let B : ℕ → ℝ := fun n =>
    mixedExactCycleConditionalChebyshevBound theta
      (mixedPolynomialTotalScaleDirection n h) epsilon
      (mixedPolynomialTotalScaleFinalCycles n)
  have hBreal : Tendsto B atTop (nhds 0) := by
    have hc : Tendsto
        (fun n : ℕ => mixedPolynomialTotalScaleRootFinalRatio n ^ 4)
        atTop (nhds (1 : ℝ)) := by
      simpa using mixedPolynomialTotalScaleRootFinalRatio_tendsto_one.pow 4
    have hfixed : Tendsto
        (fun n : ℕ => mixedExactCycleConditionalChebyshevBound
          theta h epsilon (mixedPolynomialTotalScaleFinalCycles n))
        atTop (nhds 0) :=
      (mixedExactCycleConditionalChebyshevBound_tendsto_zero theta h epsilon).comp
        mixedPolynomialTotalScaleFinalCycles_tendsto_atTop
    have hproduct := hc.mul hfixed
    have hproduct0 : Tendsto
        (fun n : ℕ =>
          mixedPolynomialTotalScaleRootFinalRatio n ^ 4 *
            mixedExactCycleConditionalChebyshevBound theta h epsilon
              (mixedPolynomialTotalScaleFinalCycles n))
        atTop (nhds 0) := by
      simpa using hproduct
    refine hproduct0.congr' (Filter.Eventually.of_forall fun n => ?_)
    exact (mixedExactCycleConditionalChebyshevBound_scale theta h
      (mixedPolynomialTotalScaleRootFinalRatio n)
      (mixedPolynomialTotalScaleRootFinalRatio_nonnegative n)
      epsilon (mixedPolynomialTotalScaleFinalCycles n)).symm
  have hB : Tendsto (fun n => ENNReal.ofReal (B n)) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hBreal
  have hupper : ∀ n : ℕ,
      mixedPolynomialTotalScaleRowMeasure theta b n
          {row | epsilon ≤
            |mixedPolynomialTotalScaleObservedInformationCentered
              theta h b n row|} ≤
        ENNReal.ofReal (B n) := by
    intro n
    apply mixedPolynomialTotalScaleRowMeasure_dependentFinalEvent_le
      theta b (le_of_lt hInterior) n
      (fun pilot =>
        {finalPath | epsilon ≤
          |mixedExactCycleObservedQuadraticTerm theta
              (mixedPolynomialTotalScaleDirection n h)
              (mixedPolynomialTotalScaleSelectedFrame b n)
              pilot finalPath -
            mixedExactCycleObservedQuadraticConditionalExpectation theta
              (mixedPolynomialTotalScaleDirection n h)
              (mixedPolynomialTotalScaleSelectedFrame b n) pilot|})
      (B n)
    intro pilot
    change mixedExactCycleConditionalDeviationProbability theta
        (mixedPolynomialTotalScaleDirection n h)
        (mixedPolynomialTotalScaleSelectedFrame b n)
        pilot epsilon ≤ B n
    exact mixedExactCycleConditionalDeviationProbability_le_chebyshevBound
      theta (mixedPolynomialTotalScaleDirection n h)
      (mixedPolynomialTotalScaleSelectedFrame b n) pilot epsilon
      hInterior hepsilon (mixedPolynomialTotalScaleFinalCycles_pos n)
  exact Tendsto.squeeze tendsto_const_nhds hB
    (fun _ => bot_le) hupper

/-! ## Fisher convergence with the moving direction `h_n` -/

theorem mixedPolynomialTotalScaleExpectedFisher_eq_information
    (theta g b : Fin 3 → ℝ) (n : ℕ)
    (pilot : PauliPilotPath (mixedPolynomialTotalScalePilotBlocks n))
    (hInterior : QubitOracle.blochNormSq theta < 1) :
    mixedExactCycleObservedQuadraticConditionalExpectation
        (r := mixedPolynomialTotalScaleFinalCycles n) theta g
        (mixedPolynomialTotalScaleSelectedFrame b n) pilot =
      mixedPolynomialNormalizedDirectionalInformation
        theta g b n pilot := by
  rw [mixedExactCycleObservedQuadraticConditionalExpectation_eq_fisher
    theta g (mixedPolynomialTotalScaleSelectedFrame b n) pilot
    hInterior (mixedPolynomialTotalScaleFinalCycles_pos n)]
  unfold mixedExactCycleNormalizedDirectionalFisher
    mixedExactCycleOneShotNormalizedDirectionalFisher
    mixedPolynomialNormalizedDirectionalInformation
    mixedTwoStageFinalDirectionalFisherTerm
    mixedPolynomialTotalScaleSelectedFrame
    mixedPolynomialTotalScaleFinalCycles
    mixedPolynomialTFinal
  rw [Finset.sum_div]
  rfl

theorem mixedPolynomialNormalizedDirectionalInformation_scale
    (theta h b : Fin 3 → ℝ) (c : ℝ) (n : ℕ)
    (pilot : PauliPilotPath (mixedPolynomialTotalScalePilotBlocks n)) :
    mixedPolynomialNormalizedDirectionalInformation
        theta (fun i => c * h i) b n pilot =
      c ^ 2 *
        mixedPolynomialNormalizedDirectionalInformation
          theta h b n pilot := by
  unfold mixedPolynomialNormalizedDirectionalInformation
    mixedTwoStageFinalDirectionalFisherTerm
  have hsum :
      (∑ t : Fin (mixedPolynomialTFinal n),
        QubitOracle.blochDot (fun i => c * h i)
            (mixedTwoStageFinalAxis
              (mixedPolynomialPilotSelectedFinalFrame b n)
              pilot t) ^ 2 /
          (1 - QubitOracle.blochDot theta
            (mixedTwoStageFinalAxis
              (mixedPolynomialPilotSelectedFinalFrame b n)
              pilot t) ^ 2)) =
        c ^ 2 *
          ∑ t : Fin (mixedPolynomialTFinal n),
            QubitOracle.blochDot h
                (mixedTwoStageFinalAxis
                  (mixedPolynomialPilotSelectedFinalFrame b n)
                  pilot t) ^ 2 /
              (1 - QubitOracle.blochDot theta
                (mixedTwoStageFinalAxis
                  (mixedPolynomialPilotSelectedFinalFrame b n)
                  pilot t) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [mixedPolynomialTotalScale_blochDot_scale]
    ring
  rw [hsum]
  ring

/-- Expected Fisher at the moving direction, minus the fixed limiting Fisher. -/
def mixedPolynomialTotalScaleFisherError
    (theta h b : Fin 3 → ℝ) (n : ℕ)
    (row : MixedPolynomialTotalScaleRow n) : ℝ :=
  mixedPolynomialTotalScaleExpectedFisher theta h b n row.1 -
    mixedPolynomialTruthFrameDirectionalInformation theta h b

theorem mixedPolynomialTotalScaleFisherError_decomposition
    (theta h b : Fin 3 → ℝ) (n : ℕ)
    (row : MixedPolynomialTotalScaleRow n)
    (hInterior : QubitOracle.blochNormSq theta < 1) :
    mixedPolynomialTotalScaleFisherError theta h b n row =
      mixedPolynomialTotalScaleRootFinalRatio n ^ 2 *
        (mixedPolynomialNormalizedDirectionalInformation
            theta h b n row.1 -
          mixedPolynomialTruthFrameDirectionalInformation
            theta h b) +
      (mixedPolynomialTotalScaleRootFinalRatio n ^ 2 - 1) *
        mixedPolynomialTruthFrameDirectionalInformation
          theta h b := by
  unfold mixedPolynomialTotalScaleFisherError
    mixedPolynomialTotalScaleExpectedFisher
  rw [mixedPolynomialTotalScaleExpectedFisher_eq_information
    theta (mixedPolynomialTotalScaleDirection n h) b n row.1 hInterior]
  rw [show mixedPolynomialTotalScaleDirection n h =
      (fun i => mixedPolynomialTotalScaleRootFinalRatio n * h i) by rfl]
  rw [mixedPolynomialNormalizedDirectionalInformation_scale]
  ring

theorem mixedPolynomialTotalScaleFisherError_convergesInProbability
    (theta h b : Fin 3 → ℝ)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hHoeffding : MixedPolynomialFinitePilotHoeffdingContracts
      theta (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)) :
    MixedPolynomialTotalScaleRowConvergesInProbability theta b
      (mixedPolynomialTotalScaleFisherError theta h b) := by
  let fixedError : (n : ℕ) →
      PauliPilotPath (mixedPolynomialTotalScalePilotBlocks n) → ℝ :=
    fun n pilot =>
      mixedPolynomialNormalizedDirectionalInformation
          theta h b n pilot -
        mixedPolynomialTruthFrameDirectionalInformation theta h b
  have hfixedPilot : ∀ epsilon : ℝ, 0 < epsilon →
      Tendsto
        (fun n : ℕ => pauliPilotBornProductMeasure theta
          {pilot | epsilon ≤ |fixedError n pilot|})
        atTop (nhds 0) :=
    mixedPolynomialNormalizedDirectionalInformation_convergesInProbability
      b theta h hTruth hSeed hHoeffding
  have hfixed :
      MixedPolynomialTotalScaleRowConvergesInProbability theta b
        (fun n row => fixedError n row.1) :=
    mixedPolynomialTotalScaleRowConverges_of_pilot theta b
      (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)
      fixedError hfixedPilot
  let scaledError : (n : ℕ) → MixedPolynomialTotalScaleRow n → ℝ :=
    fun n row => mixedPolynomialTotalScaleRootFinalRatio n ^ 2 *
      fixedError n row.1
  have hscaled :
      MixedPolynomialTotalScaleRowConvergesInProbability theta b scaledError := by
    apply mixedPolynomialTotalScaleRowConverges_of_dominated theta b
      (Y := fun n row => fixedError n row.1)
    · intro n row
      have hc0 := mixedPolynomialTotalScaleRootFinalRatio_nonnegative n
      have hc1 := mixedPolynomialTotalScaleRootFinalRatio_le_one n
      rw [show scaledError n row =
          mixedPolynomialTotalScaleRootFinalRatio n ^ 2 *
            fixedError n row.1 by rfl,
        abs_mul, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ hc0 hc1)
    · exact hfixed
  let drift : (n : ℕ) → ℝ := fun n =>
    (mixedPolynomialTotalScaleRootFinalRatio n ^ 2 - 1) *
      mixedPolynomialTruthFrameDirectionalInformation theta h b
  have hdriftLimit : Tendsto (fun n => |drift n|) atTop (nhds 0) := by
    have hc2 : Tendsto
        (fun n : ℕ => mixedPolynomialTotalScaleRootFinalRatio n ^ 2)
        atTop (nhds (1 : ℝ)) := by
      simpa using mixedPolynomialTotalScaleRootFinalRatio_tendsto_one.pow 2
    have hdiff : Tendsto
        (fun n => mixedPolynomialTotalScaleRootFinalRatio n ^ 2 - 1)
        atTop (nhds 0) := by
      simpa using hc2.sub
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))
    have hmul := hdiff.mul
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ =>
          mixedPolynomialTruthFrameDirectionalInformation
            theta h b)
        atTop
        (nhds (mixedPolynomialTruthFrameDirectionalInformation
          theta h b)))
    simpa [drift] using hmul.abs
  have hdrift :
      MixedPolynomialTotalScaleRowConvergesInProbability theta b
        (fun n (_row : MixedPolynomialTotalScaleRow n) => drift n) := by
    apply mixedPolynomialTotalScaleRowConverges_of_eventually_uniform
      theta b (fun n => |drift n|) hdriftLimit
    exact Filter.Eventually.of_forall fun n row => le_rfl
  have hsum := mixedPolynomialTotalScaleRowConverges_add theta b hscaled hdrift
  refine mixedPolynomialTotalScaleRowConverges_congr theta b
    (X := fun n row => scaledError n row + drift n) ?_ hsum
  intro n row
  exact (mixedPolynomialTotalScaleFisherError_decomposition
    theta h b n row hTruth.2).symm

/-! ## Complete residual and certificate -/

/-- Complete pilot-plus-final log likelihood at the actual total local scale. -/
def mixedPolynomialTotalScaleCompleteLogLikelihood
    (theta h b : Fin 3 → ℝ) (n : ℕ)
    (row : MixedPolynomialTotalScaleRow n) : ℝ :=
  mixedPolynomialTotalScalePilotLogLikelihood theta h n row.1 +
    mixedPolynomialTotalScaleFinalLogLikelihood theta h b n row

/-- Complete residual after retaining the final linear score and subtracting
half of the fixed limiting directional Fisher information. -/
def mixedPolynomialTotalScaleResidual
    (theta h b : Fin 3 → ℝ) (n : ℕ)
    (row : MixedPolynomialTotalScaleRow n) : ℝ :=
  mixedPolynomialTotalScalePilotLogLikelihood theta h n row.1 +
    mixedPolynomialTotalScaleFinalTaylorRemainder theta h b n row -
    (mixedPolynomialTotalScaleObservedQuadratic theta h b n row -
      mixedPolynomialTruthFrameDirectionalInformation theta h b) / 2

/-- Exact complete-row LAN algebra before taking probability limits. -/
theorem mixedPolynomialTotalScaleCompleteLogLikelihood_exact
    (theta h b : Fin 3 → ℝ) (n : ℕ)
    (row : MixedPolynomialTotalScaleRow n) :
    mixedPolynomialTotalScaleCompleteLogLikelihood theta h b n row =
      mixedPolynomialTotalScaleFinalLinearScore theta h b n row -
        mixedPolynomialTruthFrameDirectionalInformation theta h b / 2 +
      mixedPolynomialTotalScaleResidual theta h b n row := by
  unfold mixedPolynomialTotalScaleCompleteLogLikelihood
    mixedPolynomialTotalScaleFinalLogLikelihood
  rw [mixedExactCycleConditionalLogLikelihoodRatio_exactTaylor
    theta (mixedPolynomialTotalScaleDirection n h)
    (mixedPolynomialTotalScaleSelectedFrame b n) row.1 row.2]
  unfold mixedPolynomialTotalScaleResidual
    mixedPolynomialTotalScaleFinalLinearScore
    mixedPolynomialTotalScaleFinalTaylorRemainder
    mixedPolynomialTotalScaleObservedQuadratic
  ring

theorem mixedPolynomialTotalScaleResidual_convergesInProbability
    (theta h b : Fin 3 → ℝ)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hHoeffding : MixedPolynomialFinitePilotHoeffdingContracts
      theta (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)) :
    MixedPolynomialTotalScaleRowConvergesInProbability theta b
      (mixedPolynomialTotalScaleResidual theta h b) := by
  have hPilot :=
    mixedPolynomialTotalScalePilotLogLikelihood_negligibleInProbability
      theta h b hTruth.2
  have hTaylor :=
    mixedPolynomialTotalScaleFinalTaylorRemainder_convergesInProbability
      theta h b hTruth.2
  have hObserved :=
    mixedPolynomialTotalScaleObservedInformationCentered_convergesInProbability
      theta h b hTruth.2
  have hFisher :=
    mixedPolynomialTotalScaleFisherError_convergesInProbability
      theta h b hTruth hSeed hHoeffding
  have hObservedPlusFisher :=
    mixedPolynomialTotalScaleRowConverges_add theta b hObserved hFisher
  have hObservedMinusTruth :
      MixedPolynomialTotalScaleRowConvergesInProbability theta b
        (fun n row =>
          mixedPolynomialTotalScaleObservedQuadratic theta h b n row -
            mixedPolynomialTruthFrameDirectionalInformation
              theta h b) := by
    refine mixedPolynomialTotalScaleRowConverges_congr theta b
      (X := fun n row =>
        mixedPolynomialTotalScaleObservedInformationCentered theta h b n row +
          mixedPolynomialTotalScaleFisherError theta h b n row)
      ?_ hObservedPlusFisher
    intro n row
    unfold mixedPolynomialTotalScaleObservedInformationCentered
      mixedPolynomialTotalScaleFisherError
    ring
  have hHalf :
      MixedPolynomialTotalScaleRowConvergesInProbability theta b
        (fun n row =>
          (mixedPolynomialTotalScaleObservedQuadratic theta h b n row -
            mixedPolynomialTruthFrameDirectionalInformation
              theta h b) / 2) := by
    apply mixedPolynomialTotalScaleRowConverges_of_dominated theta b
      (Y := fun n row =>
        mixedPolynomialTotalScaleObservedQuadratic theta h b n row -
          mixedPolynomialTruthFrameDirectionalInformation
            theta h b)
    · intro n row
      rw [abs_div]
      norm_num <;> nlinarith [abs_nonneg
        (mixedPolynomialTotalScaleObservedQuadratic theta h b n row -
          mixedPolynomialTruthFrameDirectionalInformation theta h b)]
    · exact hObservedMinusTruth
  have hPilotTaylor :=
    mixedPolynomialTotalScaleRowConverges_add theta b hPilot hTaylor
  have hResidualForm :=
    mixedPolynomialTotalScaleRowConverges_sub theta b hPilotTaylor hHalf
  refine mixedPolynomialTotalScaleRowConverges_congr theta b
    (X := fun n row =>
      (mixedPolynomialTotalScalePilotLogLikelihood theta h n row.1 +
        mixedPolynomialTotalScaleFinalTaylorRemainder theta h b n row) -
      (mixedPolynomialTotalScaleObservedQuadratic theta h b n row -
            mixedPolynomialTruthFrameDirectionalInformation
          theta h b) / 2)
    ?_ hResidualForm
  intro n row
  rfl

/-- A clean proposition packaging both exact finite-row LAN algebra and
row-specific convergence of the complete residual. -/
def MixedPolynomialTotalScaleResidualCertificate
    (theta h b : Fin 3 → ℝ) : Prop :=
  (∀ n : ℕ, ∀ row : MixedPolynomialTotalScaleRow n,
    mixedPolynomialTotalScaleCompleteLogLikelihood theta h b n row =
      mixedPolynomialTotalScaleFinalLinearScore theta h b n row -
        mixedPolynomialTruthFrameDirectionalInformation theta h b / 2 +
      mixedPolynomialTotalScaleResidual theta h b n row) ∧
  MixedPolynomialTotalScaleRowConvergesInProbability theta b
    (mixedPolynomialTotalScaleResidual theta h b)

/-- Construct the total-scale residual certificate for the concrete mixed
one-qubit polynomial protocol. -/
theorem mixedPolynomialTotalScaleResidualCertificate_construct
    (theta h b : Fin 3 → ℝ)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hHoeffding : MixedPolynomialFinitePilotHoeffdingContracts
      theta (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)) :
    MixedPolynomialTotalScaleResidualCertificate theta h b := by
  constructor
  · intro n row
    exact mixedPolynomialTotalScaleCompleteLogLikelihood_exact
      theta h b n row
  · exact mixedPolynomialTotalScaleResidual_convergesInProbability
      theta h b hTruth hSeed hHoeffding

end

end QubitOracle.Paper
