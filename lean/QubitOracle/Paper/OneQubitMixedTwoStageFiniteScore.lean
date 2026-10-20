import QubitOracle.Paper.OneQubitMixedTwoStageFiniteLaw

/-!
# Finite directional scores for the mixed two-stage law

This module works only with the explicit finite-row mass from
`OneQubitMixedTwoStageFiniteLaw`.  It proves the two-outcome score identities
algebraically and lifts them through the pilot-conditional finite product by
finite sums.  No conditional-expectation, martingale, infinite-protocol, LAN,
or asymptotic API is used.
-/

open scoped BigOperators

namespace QubitOracle.Paper

noncomputable section

/-! ## One-shot directional score -/

/-- Binary Born weight for a fixed physical qubit axis. -/
def mixedTwoStageAxisBornProbability
    (theta axis : Fin 3 → ℝ) (outcome : Bool) : ℝ :=
  if outcome then
    (1 + QubitOracle.blochDot axis theta) / 2
  else
    (1 - QubitOracle.blochDot axis theta) / 2

/-- Scalar score in local direction `h` for one binary final observation. -/
def mixedTwoStageAxisDirectionalScore
    (theta h axis : Fin 3 → ℝ) (outcome : Bool) : ℝ :=
  pauliOutcomeSign outcome * QubitOracle.blochDot h axis /
    (1 + pauliOutcomeSign outcome * QubitOracle.blochDot theta axis)

/-- Symmetry of the concrete real Bloch dot product, recorded locally so the
Born weight and score denominator use the same scalar overlap. -/
theorem mixedTwoStageScore_blochDot_comm (x z : Fin 3 → ℝ) :
    QubitOracle.blochDot x z = QubitOracle.blochDot z x := by
  unfold QubitOracle.blochDot
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Interior physicality and a unit axis give the strictly positive Fisher
denominator. -/
theorem mixedTwoStageAxisFisherDenominator_pos
    (theta axis : Fin 3 → ℝ)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hAxis : QubitOracle.blochNormSq axis = 1) :
    0 < 1 - QubitOracle.blochDot theta axis ^ 2 := by
  have hCauchy :
      QubitOracle.blochDot theta axis ^ 2 ≤
        QubitOracle.blochNormSq theta * QubitOracle.blochNormSq axis := by
    simpa [QubitOracle.blochDot, QubitOracle.blochNormSq] using
      (Finset.sum_mul_sq_le_sq_mul_sq
        (Finset.univ : Finset (Fin 3)) theta axis)
  have hSquare :
      QubitOracle.blochDot theta axis ^ 2 ≤
        QubitOracle.blochNormSq theta := by
    calc
      QubitOracle.blochDot theta axis ^ 2 ≤
          QubitOracle.blochNormSq theta * QubitOracle.blochNormSq axis :=
        hCauchy
      _ = QubitOracle.blochNormSq theta := by rw [hAxis, mul_one]
  exact sub_pos.mpr (hSquare.trans_lt hInterior)

/-- The scalar overlap with every unit axis lies strictly between `-1` and
`1` at an interior truth. -/
theorem mixedTwoStageAxisOverlap_mem_Ioo
    (theta axis : Fin 3 → ℝ)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hAxis : QubitOracle.blochNormSq axis = 1) :
    -1 < QubitOracle.blochDot theta axis ∧
      QubitOracle.blochDot theta axis < 1 := by
  have hden := mixedTwoStageAxisFisherDenominator_pos
    theta axis hInterior hAxis
  constructor
  · nlinarith [sq_nonneg (QubitOracle.blochDot theta axis + 1)]
  · nlinarith [sq_nonneg (QubitOracle.blochDot theta axis - 1)]

/-- First two-point Born identity: the directional score has exact mean zero. -/
theorem mixedTwoStageAxisDirectionalScore_bornMean_zero
    (theta h axis : Fin 3 → ℝ)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hAxis : QubitOracle.blochNormSq axis = 1) :
    (∑ outcome : Bool,
      mixedTwoStageAxisBornProbability theta axis outcome *
        mixedTwoStageAxisDirectionalScore theta h axis outcome) = 0 := by
  have hz := mixedTwoStageAxisOverlap_mem_Ioo
    theta axis hInterior hAxis
  have hminus : 1 - QubitOracle.blochDot theta axis ≠ 0 :=
    ne_of_gt (sub_pos.mpr hz.2)
  have hplus : 1 + QubitOracle.blochDot theta axis ≠ 0 :=
    ne_of_gt (by linarith [hz.1])
  have hcomm : QubitOracle.blochDot axis theta =
      QubitOracle.blochDot theta axis :=
    mixedTwoStageScore_blochDot_comm axis theta
  simp only [Fintype.sum_bool, mixedTwoStageAxisBornProbability,
    mixedTwoStageAxisDirectionalScore]
  rw [hcomm]
  simp [pauliOutcomeSign]
  field_simp [hminus, hplus]
  have hcancel :
      (1 - QubitOracle.blochDot theta axis) *
          (1 - QubitOracle.blochDot theta axis)⁻¹ = 1 :=
    mul_inv_cancel₀ hminus
  linear_combination
    (-QubitOracle.blochDot h axis) * hcancel

/-- Second two-point Born identity: the score square is the directional
one-shot Fisher information. -/
theorem mixedTwoStageAxisDirectionalScore_bornSquare
    (theta h axis : Fin 3 → ℝ)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hAxis : QubitOracle.blochNormSq axis = 1) :
    (∑ outcome : Bool,
      mixedTwoStageAxisBornProbability theta axis outcome *
        mixedTwoStageAxisDirectionalScore theta h axis outcome ^ 2) =
      QubitOracle.blochDot h axis ^ 2 /
        (1 - QubitOracle.blochDot theta axis ^ 2) := by
  have hz := mixedTwoStageAxisOverlap_mem_Ioo
    theta axis hInterior hAxis
  have hden := mixedTwoStageAxisFisherDenominator_pos
    theta axis hInterior hAxis
  have hminus : 1 - QubitOracle.blochDot theta axis ≠ 0 :=
    ne_of_gt (sub_pos.mpr hz.2)
  have hplus : 1 + QubitOracle.blochDot theta axis ≠ 0 :=
    ne_of_gt (by linarith [hz.1])
  have hquadratic :
      1 - QubitOracle.blochDot theta axis ^ 2 ≠ 0 := ne_of_gt hden
  have hcomm : QubitOracle.blochDot axis theta =
      QubitOracle.blochDot theta axis :=
    mixedTwoStageScore_blochDot_comm axis theta
  have hminusSquare :
      1 - QubitOracle.blochDot theta axis * 2 +
          QubitOracle.blochDot theta axis ^ 2 ≠ 0 := by
    rw [show
      1 - QubitOracle.blochDot theta axis * 2 +
          QubitOracle.blochDot theta axis ^ 2 =
        (1 - QubitOracle.blochDot theta axis) ^ 2 by ring]
    exact pow_ne_zero 2 hminus
  have hplusSquare :
      1 + QubitOracle.blochDot theta axis * 2 +
          QubitOracle.blochDot theta axis ^ 2 ≠ 0 := by
    rw [show
      1 + QubitOracle.blochDot theta axis * 2 +
          QubitOracle.blochDot theta axis ^ 2 =
        (1 + QubitOracle.blochDot theta axis) ^ 2 by ring]
    exact pow_ne_zero 2 hplus
  simp only [Fintype.sum_bool, mixedTwoStageAxisBornProbability,
    mixedTwoStageAxisDirectionalScore]
  rw [hcomm]
  simp [pauliOutcomeSign]
  field_simp [hminus, hplus, hquadratic, hminusSquare, hplusSquare]
  have hcancel :
      (1 - QubitOracle.blochDot theta axis * 2 +
          QubitOracle.blochDot theta axis ^ 2) *
        (1 - QubitOracle.blochDot theta axis * 2 +
          QubitOracle.blochDot theta axis ^ 2)⁻¹ = 1 :=
    mul_inv_cancel₀ hminusSquare
  linear_combination
    (QubitOracle.blochDot h axis ^ 2 *
      (1 + QubitOracle.blochDot theta axis) ^ 2) * hcancel

/-! ## Specialization to one final shot -/

/-- Directional score at a specified final shot of the concrete finite row. -/
def mixedTwoStageFinalShotDirectionalScore
    {q T : ℕ} (theta h : Fin 3 → ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) (t : Fin T) (outcome : Bool) : ℝ :=
  mixedTwoStageAxisDirectionalScore theta h
    (mixedTwoStageFinalAxis selected pilot t) outcome

/-- The concrete final Born probability is the fixed-axis Born weight at the
pilot-selected cyclic axis. -/
@[simp]
theorem mixedTwoStageFinalBornProbability_eq_axisBornProbability
    {q T : ℕ} (theta : Fin 3 → ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) (t : Fin T) (outcome : Bool) :
    mixedTwoStageFinalBornProbability theta selected pilot t outcome =
      mixedTwoStageAxisBornProbability theta
        (mixedTwoStageFinalAxis selected pilot t) outcome :=
  rfl

/-- Two-point centering at one concrete final shot. -/
theorem mixedTwoStageFinalShotDirectionalScore_bornMean_zero
    {q T : ℕ} (theta h : Fin 3 → ℝ)
    (selected : PilotSelectedFinalFrame q)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (pilot : PauliPilotPath q) (t : Fin T) :
    (∑ outcome : Bool,
      mixedTwoStageFinalBornProbability theta selected pilot t outcome *
        mixedTwoStageFinalShotDirectionalScore
          theta h selected pilot t outcome) = 0 := by
  simpa [mixedTwoStageFinalShotDirectionalScore] using
    (mixedTwoStageAxisDirectionalScore_bornMean_zero
      theta h (mixedTwoStageFinalAxis selected pilot t)
      hInterior (mixedTwoStageFinalAxis_unit selected pilot t))

/-- Two-point score-square identity at one concrete final shot. -/
theorem mixedTwoStageFinalShotDirectionalScore_bornSquare
    {q T : ℕ} (theta h : Fin 3 → ℝ)
    (selected : PilotSelectedFinalFrame q)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (pilot : PauliPilotPath q) (t : Fin T) :
    (∑ outcome : Bool,
      mixedTwoStageFinalBornProbability theta selected pilot t outcome *
        mixedTwoStageFinalShotDirectionalScore
          theta h selected pilot t outcome ^ 2) =
      QubitOracle.blochDot h
          (mixedTwoStageFinalAxis selected pilot t) ^ 2 /
        (1 - QubitOracle.blochDot theta
          (mixedTwoStageFinalAxis selected pilot t) ^ 2) := by
  simpa [mixedTwoStageFinalShotDirectionalScore] using
    (mixedTwoStageAxisDirectionalScore_bornSquare
      theta h (mixedTwoStageFinalAxis selected pilot t)
      hInterior (mixedTwoStageFinalAxis_unit selected pilot t))

/-! ## One-coordinate finite-product lifting -/

/-- The score at final time `t`, evaluated on a complete final path. -/
def mixedTwoStageFinalPathDirectionalScore
    {q T : ℕ} (theta h : Fin 3 → ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) (t : Fin T)
    (finalPath : MixedTwoStageFinalPath T) : ℝ :=
  mixedTwoStageFinalShotDirectionalScore
    theta h selected pilot t (finalPath t)

private def mixedTwoStageMarkedFinalFactor
    {q T : ℕ} (theta : Fin 3 → ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) (target current : Fin T)
    (observable : Bool → ℝ) (outcome : Bool) : ℝ :=
  mixedTwoStageFinalBornProbability theta selected pilot current outcome *
    (if current = target then observable outcome else 1)

private theorem mixedTwoStageMarkedFinalFactor_prod
    {q T : ℕ} (theta : Fin 3 → ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) (target : Fin T)
    (observable : Bool → ℝ)
    (finalPath : MixedTwoStageFinalPath T) :
    (∏ current : Fin T,
      mixedTwoStageMarkedFinalFactor theta selected pilot
        target current observable (finalPath current)) =
      mixedTwoStageConditionalFinalPathMass
          theta selected pilot finalPath *
        observable (finalPath target) := by
  unfold mixedTwoStageMarkedFinalFactor
    mixedTwoStageConditionalFinalPathMass
  rw [Finset.prod_mul_distrib]
  have hobservable :
      (∏ current : Fin T,
        if current = target then observable (finalPath current) else 1) =
        observable (finalPath target) := by
    rw [Finset.prod_eq_single target]
    · simp
    · intro current _ hcurrent
      simp [hcurrent]
    · simp
  rw [hobservable]

/-- A one-coordinate observable under the conditional final product reduces
exactly to its one-shot Born expectation. -/
theorem mixedTwoStageConditionalFinal_singleShotExpectation
    {q T : ℕ} (theta : Fin 3 → ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) (target : Fin T)
    (observable : Bool → ℝ) :
    (∑ finalPath : MixedTwoStageFinalPath T,
      mixedTwoStageConditionalFinalPathMass
          theta selected pilot finalPath *
        observable (finalPath target)) =
      ∑ outcome : Bool,
        mixedTwoStageFinalBornProbability
            theta selected pilot target outcome *
          observable outcome := by
  calc
    (∑ finalPath : MixedTwoStageFinalPath T,
      mixedTwoStageConditionalFinalPathMass
          theta selected pilot finalPath *
        observable (finalPath target)) =
        ∑ finalPath : MixedTwoStageFinalPath T,
          ∏ current : Fin T,
            mixedTwoStageMarkedFinalFactor theta selected pilot
              target current observable (finalPath current) := by
      apply Finset.sum_congr rfl
      intro finalPath _
      exact (mixedTwoStageMarkedFinalFactor_prod
        theta selected pilot target observable finalPath).symm
    _ = ∏ current : Fin T,
        ∑ outcome : Bool,
          mixedTwoStageMarkedFinalFactor theta selected pilot
            target current observable outcome := by
      exact (Fintype.prod_sum (fun current outcome =>
        mixedTwoStageMarkedFinalFactor theta selected pilot
          target current observable outcome)).symm
    _ = ∑ outcome : Bool,
        mixedTwoStageFinalBornProbability
            theta selected pilot target outcome *
          observable outcome := by
      rw [Finset.prod_eq_single target]
      · simp [mixedTwoStageMarkedFinalFactor]
      · intro current _ hcurrent
        simp only [mixedTwoStageMarkedFinalFactor, if_neg hcurrent, mul_one]
        exact mixedTwoStageFinalBornProbability_sum_one
          theta selected pilot current
      · simp

/-- Item 3: every final score has conditional mean zero given the completed
pilot, expressed entirely as a finite weighted sum. -/
theorem mixedTwoStageConditionalFinalScore_mean_zero
    {q T : ℕ} (theta h : Fin 3 → ℝ)
    (selected : PilotSelectedFinalFrame q)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (pilot : PauliPilotPath q) (t : Fin T) :
    (∑ finalPath : MixedTwoStageFinalPath T,
      mixedTwoStageConditionalFinalPathMass
          theta selected pilot finalPath *
        mixedTwoStageFinalPathDirectionalScore
          theta h selected pilot t finalPath) = 0 := by
  calc
    (∑ finalPath : MixedTwoStageFinalPath T,
      mixedTwoStageConditionalFinalPathMass
          theta selected pilot finalPath *
        mixedTwoStageFinalPathDirectionalScore
          theta h selected pilot t finalPath) =
      ∑ outcome : Bool,
        mixedTwoStageFinalBornProbability theta selected pilot t outcome *
          mixedTwoStageFinalShotDirectionalScore
            theta h selected pilot t outcome := by
      simpa [mixedTwoStageFinalPathDirectionalScore] using
        (mixedTwoStageConditionalFinal_singleShotExpectation
          theta selected pilot t
          (mixedTwoStageFinalShotDirectionalScore
            theta h selected pilot t))
    _ = 0 := mixedTwoStageFinalShotDirectionalScore_bornMean_zero
      theta h selected hInterior pilot t

/-- Conditional second moment of one final score. -/
theorem mixedTwoStageConditionalFinalScore_square
    {q T : ℕ} (theta h : Fin 3 → ℝ)
    (selected : PilotSelectedFinalFrame q)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (pilot : PauliPilotPath q) (t : Fin T) :
    (∑ finalPath : MixedTwoStageFinalPath T,
      mixedTwoStageConditionalFinalPathMass
          theta selected pilot finalPath *
        mixedTwoStageFinalPathDirectionalScore
          theta h selected pilot t finalPath ^ 2) =
      QubitOracle.blochDot h
          (mixedTwoStageFinalAxis selected pilot t) ^ 2 /
        (1 - QubitOracle.blochDot theta
          (mixedTwoStageFinalAxis selected pilot t) ^ 2) := by
  calc
    (∑ finalPath : MixedTwoStageFinalPath T,
      mixedTwoStageConditionalFinalPathMass
          theta selected pilot finalPath *
        mixedTwoStageFinalPathDirectionalScore
          theta h selected pilot t finalPath ^ 2) =
      ∑ outcome : Bool,
        mixedTwoStageFinalBornProbability theta selected pilot t outcome *
          mixedTwoStageFinalShotDirectionalScore
            theta h selected pilot t outcome ^ 2 := by
      simpa [mixedTwoStageFinalPathDirectionalScore] using
        (mixedTwoStageConditionalFinal_singleShotExpectation
          theta selected pilot t
          (fun outcome =>
            mixedTwoStageFinalShotDirectionalScore
              theta h selected pilot t outcome ^ 2))
    _ = QubitOracle.blochDot h
          (mixedTwoStageFinalAxis selected pilot t) ^ 2 /
        (1 - QubitOracle.blochDot theta
          (mixedTwoStageFinalAxis selected pilot t) ^ 2) :=
      mixedTwoStageFinalShotDirectionalScore_bornSquare
        theta h selected hInterior pilot t

/-! ## Distinct-coordinate cross moments -/

private def mixedTwoStageDoubleMarkedFinalFactor
    {q T : ℕ} (theta h : Fin 3 → ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) (s t current : Fin T)
    (outcome : Bool) : ℝ :=
  mixedTwoStageFinalBornProbability theta selected pilot current outcome *
      (if current = s then
        mixedTwoStageFinalShotDirectionalScore
          theta h selected pilot s outcome
      else 1) *
    (if current = t then
      mixedTwoStageFinalShotDirectionalScore
        theta h selected pilot t outcome
    else 1)

private theorem mixedTwoStageDoubleMarkedFinalFactor_prod
    {q T : ℕ} (theta h : Fin 3 → ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q) (s t : Fin T)
    (finalPath : MixedTwoStageFinalPath T) :
    (∏ current : Fin T,
      mixedTwoStageDoubleMarkedFinalFactor
        theta h selected pilot s t current (finalPath current)) =
      mixedTwoStageConditionalFinalPathMass
          theta selected pilot finalPath *
        (mixedTwoStageFinalPathDirectionalScore
            theta h selected pilot s finalPath *
          mixedTwoStageFinalPathDirectionalScore
            theta h selected pilot t finalPath) := by
  have hs :
      (∏ current : Fin T,
        if current = s then
          mixedTwoStageFinalShotDirectionalScore
            theta h selected pilot s (finalPath current)
        else 1) =
        mixedTwoStageFinalPathDirectionalScore
          theta h selected pilot s finalPath := by
    rw [Finset.prod_eq_single s]
    · simp [mixedTwoStageFinalPathDirectionalScore]
    · intro current _ hcurrent
      simp [hcurrent]
    · simp
  have ht :
      (∏ current : Fin T,
        if current = t then
          mixedTwoStageFinalShotDirectionalScore
            theta h selected pilot t (finalPath current)
        else 1) =
        mixedTwoStageFinalPathDirectionalScore
          theta h selected pilot t finalPath := by
    rw [Finset.prod_eq_single t]
    · simp [mixedTwoStageFinalPathDirectionalScore]
    · intro current _ hcurrent
      simp [hcurrent]
    · simp
  unfold mixedTwoStageDoubleMarkedFinalFactor
    mixedTwoStageConditionalFinalPathMass
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, hs, ht]
  ring

/-- Item 4: scores at distinct final times have zero conditional cross moment. -/
theorem mixedTwoStageConditionalFinalScore_cross_zero
    {q T : ℕ} (theta h : Fin 3 → ℝ)
    (selected : PilotSelectedFinalFrame q)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (pilot : PauliPilotPath q) (s t : Fin T) (hst : s ≠ t) :
    (∑ finalPath : MixedTwoStageFinalPath T,
      mixedTwoStageConditionalFinalPathMass
          theta selected pilot finalPath *
        (mixedTwoStageFinalPathDirectionalScore
            theta h selected pilot s finalPath *
          mixedTwoStageFinalPathDirectionalScore
            theta h selected pilot t finalPath)) = 0 := by
  calc
    (∑ finalPath : MixedTwoStageFinalPath T,
      mixedTwoStageConditionalFinalPathMass
          theta selected pilot finalPath *
        (mixedTwoStageFinalPathDirectionalScore
            theta h selected pilot s finalPath *
          mixedTwoStageFinalPathDirectionalScore
            theta h selected pilot t finalPath)) =
      ∑ finalPath : MixedTwoStageFinalPath T,
        ∏ current : Fin T,
          mixedTwoStageDoubleMarkedFinalFactor
            theta h selected pilot s t current (finalPath current) := by
      apply Finset.sum_congr rfl
      intro finalPath _
      exact (mixedTwoStageDoubleMarkedFinalFactor_prod
        theta h selected pilot s t finalPath).symm
    _ = ∏ current : Fin T,
        ∑ outcome : Bool,
          mixedTwoStageDoubleMarkedFinalFactor
            theta h selected pilot s t current outcome := by
      exact (Fintype.prod_sum (fun current outcome =>
        mixedTwoStageDoubleMarkedFinalFactor
          theta h selected pilot s t current outcome)).symm
    _ = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ s) (by
        simpa [mixedTwoStageDoubleMarkedFinalFactor, hst] using
          (mixedTwoStageFinalShotDirectionalScore_bornMean_zero
            theta h selected hInterior pilot s))

/-! ## Conditional second moment of the total final score -/

/-- Sum of all scalar final-shot scores in direction `h`. -/
def mixedTwoStageFinalPathDirectionalScoreSum
    {q T : ℕ} (theta h : Fin 3 → ℝ)
    (selected : PilotSelectedFinalFrame q)
    (pilot : PauliPilotPath q)
    (finalPath : MixedTwoStageFinalPath T) : ℝ :=
  ∑ t : Fin T,
    mixedTwoStageFinalPathDirectionalScore
      theta h selected pilot t finalPath

/-- Item 5: the conditional second moment of the total final score is exactly
the sum of the one-shot directional Fisher terms. -/
theorem mixedTwoStageConditionalFinalScoreSum_secondMoment
    {q T : ℕ} (theta h : Fin 3 → ℝ)
    (selected : PilotSelectedFinalFrame q)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (pilot : PauliPilotPath q) :
    (∑ finalPath : MixedTwoStageFinalPath T,
      mixedTwoStageConditionalFinalPathMass
          theta selected pilot finalPath *
        mixedTwoStageFinalPathDirectionalScoreSum
          theta h selected pilot finalPath ^ 2) =
      ∑ t : Fin T,
        QubitOracle.blochDot h
            (mixedTwoStageFinalAxis selected pilot t) ^ 2 /
          (1 - QubitOracle.blochDot theta
            (mixedTwoStageFinalAxis selected pilot t) ^ 2) := by
  calc
    (∑ finalPath : MixedTwoStageFinalPath T,
      mixedTwoStageConditionalFinalPathMass
          theta selected pilot finalPath *
        mixedTwoStageFinalPathDirectionalScoreSum
          theta h selected pilot finalPath ^ 2) =
      ∑ finalPath : MixedTwoStageFinalPath T,
        ∑ s : Fin T, ∑ t : Fin T,
          mixedTwoStageConditionalFinalPathMass
              theta selected pilot finalPath *
            (mixedTwoStageFinalPathDirectionalScore
                theta h selected pilot s finalPath *
              mixedTwoStageFinalPathDirectionalScore
                theta h selected pilot t finalPath) := by
      apply Finset.sum_congr rfl
      intro finalPath _
      unfold mixedTwoStageFinalPathDirectionalScoreSum
      rw [pow_two, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    _ = ∑ s : Fin T,
        ∑ finalPath : MixedTwoStageFinalPath T,
          ∑ t : Fin T,
            mixedTwoStageConditionalFinalPathMass
                theta selected pilot finalPath *
              (mixedTwoStageFinalPathDirectionalScore
                  theta h selected pilot s finalPath *
                mixedTwoStageFinalPathDirectionalScore
                  theta h selected pilot t finalPath) := by
      rw [Finset.sum_comm]
    _ = ∑ s : Fin T, ∑ t : Fin T,
        ∑ finalPath : MixedTwoStageFinalPath T,
          mixedTwoStageConditionalFinalPathMass
              theta selected pilot finalPath *
            (mixedTwoStageFinalPathDirectionalScore
                theta h selected pilot s finalPath *
              mixedTwoStageFinalPathDirectionalScore
                theta h selected pilot t finalPath) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
    _ = ∑ s : Fin T, ∑ t : Fin T,
        if s = t then
          QubitOracle.blochDot h
              (mixedTwoStageFinalAxis selected pilot s) ^ 2 /
            (1 - QubitOracle.blochDot theta
              (mixedTwoStageFinalAxis selected pilot s) ^ 2)
        else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      by_cases hst : s = t
      · subst t
        simp only [if_pos]
        simpa [pow_two] using
          (mixedTwoStageConditionalFinalScore_square
            theta h selected hInterior pilot s)
      · rw [if_neg hst]
        exact mixedTwoStageConditionalFinalScore_cross_zero
          theta h selected hInterior pilot s t hst
    _ = ∑ t : Fin T,
        QubitOracle.blochDot h
            (mixedTwoStageFinalAxis selected pilot t) ^ 2 /
          (1 - QubitOracle.blochDot theta
            (mixedTwoStageFinalAxis selected pilot t) ^ 2) := by
      simp

end

end QubitOracle.Paper
