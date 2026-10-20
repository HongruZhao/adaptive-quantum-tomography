import QubitOracle.Paper.OneQubitMixedUniformLocalProbabilityEnvelopeClosed

namespace QubitOracle.Paper

noncomputable section

/-- A fixed-center envelope for the exact squared-Bures Taylor remainder.
The local truth may vary, but its Bloch-ball gap is required to stay above half
of the center gap. -/
def mixedExactCycleUniformBuresTransferEnvelope
    (theta : RLSVector 3) (q : ℕ) : ℝ :=
  let qR : ℝ := q
  let gap := (1 - blochNormSq theta) / 2
  let eta := gap / 8
  54 / gap ^ 2 * (Real.sqrt qR)⁻¹
    + 90 / gap ^ 3 * qR⁻¹
    + 90 / eta ^ 4 * qR⁻¹
    + 45 / (4 * gap * eta ^ 2) * qR⁻¹

/-- The concrete one-qubit exact Bures remainder is uniformly dominated by the
fixed-center envelope whenever the local Bloch-ball gap is at least half the
center gap. -/
theorem mixedFrameExactBuresTransferRate_le_uniformEnvelope
    (theta z : RLSVector 3)
    (q : ℕ)
    (hInterior : blochNormSq theta < 1)
    (hMargin : (1 - blochNormSq theta) / 2 ≤ 1 - blochNormSq z) :
    mixedFrameExactBuresTransferRate z q ≤
      mixedExactCycleUniformBuresTransferEnvelope theta q := by
  have hGap : 0 < (1 - blochNormSq theta) / 2 := by
    linarith
  have hLocalGap : 0 < 1 - blochNormSq z :=
    lt_of_lt_of_le hGap hMargin
  have hEta :
      (1 - blochNormSq theta) / 2 / 8 ≤
        mixedBuresFidelityLocalRadius z := by
    rw [mixedBuresFidelityLocalRadius]
    linarith
  have hSqrtInv : 0 ≤ (Real.sqrt (q : ℝ))⁻¹ := by positivity
  have hQInv : 0 ≤ ((q : ℝ))⁻¹ := by positivity
  simp only [mixedFrameExactBuresTransferRate,
    mixedExactCycleUniformBuresTransferEnvelope]
  gcongr


/-- The fixed-center envelope is at most sixteen times the ordinary fixed-state
Bures transfer rate. -/
theorem mixedExactCycleUniformBuresTransferEnvelope_le_sixteen
    (theta : RLSVector 3)
    (q : ℕ)
    (hInterior : blochNormSq theta < 1) :
    mixedExactCycleUniformBuresTransferEnvelope theta q ≤
      16 * mixedFrameExactBuresTransferRate theta q := by
  let G : ℝ := 1 - blochNormSq theta
  let A : ℝ := (Real.sqrt (q : ℝ))⁻¹
  let B : ℝ := ((q : ℝ))⁻¹
  let a : ℝ := 54 / G ^ 2 * A
  let c : ℝ := 90 / G ^ 3 * B
  let d : ℝ := 90 / (G / 8) ^ 4 * B
  let e : ℝ := 45 / (4 * G * (G / 8) ^ 2) * B
  have hG : 0 < G := by
    dsimp [G]
    linarith
  have hGNe : G ≠ 0 := ne_of_gt hG
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hEnvelope :
      mixedExactCycleUniformBuresTransferEnvelope theta q =
        4 * a + 8 * c + 16 * d + 8 * e := by
    change
      54 / (G / 2) ^ 2 * A
          + 90 / (G / 2) ^ 3 * B
          + 90 / (G / 2 / 8) ^ 4 * B
          + 45 / (4 * (G / 2) * (G / 2 / 8) ^ 2) * B =
        4 * a + 8 * c + 16 * d + 8 * e
    dsimp only [a, c, d, e]
    field_simp [hGNe]
    <;> ring
  have hRate :
      mixedFrameExactBuresTransferRate theta q = a + c + d + e := by
    change
      54 / G ^ 2 * A
          + 90 / G ^ 3 * B
          + 90 / (G / 8) ^ 4 * B
          + 45 / (4 * G * (G / 8) ^ 2) * B =
        a + c + d + e
    rfl
  rw [hEnvelope, hRate]
  nlinarith

/-- Along the concrete polynomial final-stage schedule, the fixed-center
uniform Bures envelope vanishes. -/
theorem mixedExactCycleUniformBuresTransferEnvelope_tendsto_zero
    (theta : RLSVector 3)
    (hInterior : blochNormSq theta < 1) :
    Filter.Tendsto
      (fun n => mixedExactCycleUniformBuresTransferEnvelope theta
        (mixedUniformLocalExactCycleQFinal n))
      Filter.atTop (nhds 0) := by
  have hBase := mixedPolynomialExactBuresTransferRate_tendsto_zero theta hInterior
  have hUpper :
      Filter.Tendsto
        (fun n => 16 * mixedFrameExactBuresTransferRate theta
          (mixedUniformLocalExactCycleQFinal n))
        Filter.atTop (nhds 0) := by
    simpa only [mixedUniformLocalExactCycleQFinal, mul_zero] using
      (tendsto_const_nhds.mul hBase :
        Filter.Tendsto
          (fun n => 16 * mixedFrameExactBuresTransferRate theta
            (mixedPolynomialQuadraticQFinal n))
          Filter.atTop (nhds (16 * 0)))
  refine squeeze_zero' ?_ ?_ hUpper
  · exact Filter.Eventually.of_forall fun n => by
      have hGap : 0 < (1 - blochNormSq theta) / 2 := by linarith
      simp only [mixedExactCycleUniformBuresTransferEnvelope]
      positivity
  · exact Filter.Eventually.of_forall fun n =>
      mixedExactCycleUniformBuresTransferEnvelope_le_sixteen
        theta (mixedUniformLocalExactCycleQFinal n) hInterior

/-- The exact squared-Bures Taylor remainder vanishes uniformly over every
bounded local-direction ball in the concrete one-qubit exact cycle. -/
theorem mixedExactCycleLocal_uniform_BuresTransferRate_tendsto_zero
    (theta : RLSVector 3)
    (H : ℝ)
    (hInterior : blochNormSq theta < 1)
    (epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ n in Filter.atTop,
      ∀ h : RLSVector 3,
        MixedLocalDirectionBall H h →
          mixedFrameExactBuresTransferRate
              (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h)
              (mixedUniformLocalExactCycleQFinal n) <
            epsilon := by
  have hEnvelopeLimit :=
    mixedExactCycleUniformBuresTransferEnvelope_tendsto_zero theta hInterior
  have hEnvelopeSmall :
      ∀ᶠ n in Filter.atTop,
        mixedExactCycleUniformBuresTransferEnvelope theta
            (mixedUniformLocalExactCycleQFinal n) < epsilon :=
    (tendsto_order.1 hEnvelopeLimit).2 epsilon hepsilon
  filter_upwards
    [mixedExactCycleLocal_uniform_remainder_margin theta H hInterior,
      hEnvelopeSmall] with n hMargin hSmall
  intro h hBall
  exact lt_of_le_of_lt
    (mixedFrameExactBuresTransferRate_le_uniformEnvelope
      theta
      (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h)
      (mixedUniformLocalExactCycleQFinal n)
      hInterior (hMargin h hBall).1)
    hSmall

/-- The concrete final-stage sample size `(n+1)^6` diverges after casting to
the reals. -/
theorem mixedUniformLocalExactCycleQFinal_real_tendsto_atTop :
    Filter.Tendsto
      (fun n => (mixedUniformLocalExactCycleQFinal n : ℝ))
      Filter.atTop Filter.atTop := by
  have hNat :
      Filter.Tendsto mixedUniformLocalExactCycleQFinal
        Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro m
    filter_upwards [Filter.eventually_ge_atTop m] with n hn
    rw [mixedUniformLocalExactCycleQFinal_eq, polynomialScheduleM]
    calc
      m ≤ n := hn
      _ ≤ n.succ := Nat.le_succ n
      _ ≤ n.succ ^ 6 := Nat.le_pow (by norm_num)
  exact tendsto_natCast_atTop_atTop.comp hNat

/-- Consequently, the reciprocal final-stage size vanishes. -/
theorem mixedUniformLocalExactCycleQFinal_reciprocal_tendsto_zero :
    Filter.Tendsto
      (fun n => ((mixedUniformLocalExactCycleQFinal n : ℝ))⁻¹)
      Filter.atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp
    mixedUniformLocalExactCycleQFinal_real_tendsto_atTop

/-- A fixed-center envelope for the fourth-moment correction relating ordinary
infidelity to squared Bures loss. -/
def mixedExactCycleUniformBuresSecondMomentEnvelope
    (theta : RLSVector 3) (q : ℕ) : ℝ :=
  let gap := (1 - blochNormSq theta) / 2
  let coefficient := 13 / (32 * gap)
  let eta := gap / 8
  (45 * coefficient ^ 2 + 180 / eta ^ 4) / (q : ℝ)

/-- The local fourth-moment rate is uniformly bounded by the fixed-center
envelope under the common interior-gap condition. -/
theorem mixedFrameScaledBuresSecondMomentRate_le_uniformEnvelope
    (theta z : RLSVector 3)
    (q : ℕ)
    (hInterior : blochNormSq theta < 1)
    (hMargin : (1 - blochNormSq theta) / 2 ≤ 1 - blochNormSq z) :
    mixedFrameScaledBuresSecondMomentRate z q ≤
      mixedExactCycleUniformBuresSecondMomentEnvelope theta q := by
  have hGap : 0 < (1 - blochNormSq theta) / 2 := by linarith
  have hLocalGap : 0 < 1 - blochNormSq z :=
    lt_of_lt_of_le hGap hMargin
  have hCoefficient :
      mixedBuresLocalQuadraticEnvelopeCoefficient z ≤
        13 / (32 * ((1 - blochNormSq theta) / 2)) := by
    rw [mixedBuresLocalQuadraticEnvelopeCoefficient]
    gcongr
  have hCoefficientNonnegative :
      0 ≤ mixedBuresLocalQuadraticEnvelopeCoefficient z := by
    rw [mixedBuresLocalQuadraticEnvelopeCoefficient]
    positivity
  have hEta :
      (1 - blochNormSq theta) / 2 / 8 ≤
        mixedBuresFidelityLocalRadius z := by
    rw [mixedBuresFidelityLocalRadius]
    linarith
  simp only [mixedFrameScaledBuresSecondMomentRate,
    mixedExactCycleUniformBuresSecondMomentEnvelope]
  gcongr

/-- The uniform fourth-moment envelope vanishes along the concrete polynomial
final-stage schedule. -/
theorem mixedExactCycleUniformBuresSecondMomentEnvelope_tendsto_zero
    (theta : RLSVector 3)
    (hInterior : blochNormSq theta < 1) :
    Filter.Tendsto
      (fun n => mixedExactCycleUniformBuresSecondMomentEnvelope theta
        (mixedUniformLocalExactCycleQFinal n))
      Filter.atTop (nhds 0) := by
  let C : ℝ :=
    45 * (13 / (32 * ((1 - blochNormSq theta) / 2))) ^ 2
      + 180 / (((1 - blochNormSq theta) / 2) / 8) ^ 4
  have hProduct :
      Filter.Tendsto
        (fun n => C * ((mixedUniformLocalExactCycleQFinal n : ℝ))⁻¹)
        Filter.atTop (nhds (C * 0)) :=
    tendsto_const_nhds.mul
      mixedUniformLocalExactCycleQFinal_reciprocal_tendsto_zero
  simpa only [mixedExactCycleUniformBuresSecondMomentEnvelope,
    div_eq_mul_inv, mul_zero, C] using hProduct

/-- The ordinary-infidelity fourth-moment correction vanishes uniformly over
every bounded local-direction ball. -/
theorem mixedExactCycleLocal_uniform_BuresSecondMomentRate_tendsto_zero
    (theta : RLSVector 3)
    (H : ℝ)
    (hInterior : blochNormSq theta < 1)
    (epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ n in Filter.atTop,
      ∀ h : RLSVector 3,
        MixedLocalDirectionBall H h →
          mixedFrameScaledBuresSecondMomentRate
              (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h)
              (mixedUniformLocalExactCycleQFinal n) <
            epsilon := by
  have hEnvelopeLimit :=
    mixedExactCycleUniformBuresSecondMomentEnvelope_tendsto_zero
      theta hInterior
  have hEnvelopeSmall :
      ∀ᶠ n in Filter.atTop,
        mixedExactCycleUniformBuresSecondMomentEnvelope theta
            (mixedUniformLocalExactCycleQFinal n) < epsilon :=
    (tendsto_order.1 hEnvelopeLimit).2 epsilon hepsilon
  filter_upwards
    [mixedExactCycleLocal_uniform_remainder_margin theta H hInterior,
      hEnvelopeSmall] with n hMargin hSmall
  intro h hBall
  exact lt_of_le_of_lt
    (mixedFrameScaledBuresSecondMomentRate_le_uniformEnvelope
      theta
      (mixedLocalAlternative theta mixedUniformLocalExactCycleN n h)
      (mixedUniformLocalExactCycleQFinal n)
      hInterior (hMargin h hBall).1)
    hSmall

end

end QubitOracle.Paper
