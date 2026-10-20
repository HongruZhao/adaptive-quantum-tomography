import QubitOracle.Paper.MixedScoreMoments
import QubitOracle.Paper.MixedProbabilityFloor

namespace QubitOracle.Paper

noncomputable section

open scoped BigOperators

/-- Euclidean Bloch radius of a mixed-qubit parameter. -/
def mixedInteriorRadius (theta : Fin 3 → ℝ) : ℝ :=
  Real.sqrt (QubitOracle.blochNormSq theta)

/-- Distance of the Bloch radius from the pure-state boundary. -/
def mixedInteriorGap (theta : Fin 3 → ℝ) : ℝ :=
  1 - mixedInteriorRadius theta

/-- The finite-coordinate `l1` size used for a path-independent projection bound. -/
def mixedProjectionL1 (h : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, |h i|

/-- The explicit envelope for a scalar score projected in direction `h`. -/
def mixedProjectedScoreEnvelope (theta h : Fin 3 → ℝ) : ℝ :=
  mixedProjectionL1 h * (mixedInteriorGap theta)⁻¹

/-- Select the scalar natural score for either binary projective outcome. -/
def mixedAxisOutcomeScalarScore (theta u : Fin 3 → ℝ) : BinaryOutcome → ℝ
  | .plus =>
      QubitOracle.binaryAxisPlusScore (QubitOracle.blochDot theta u)
  | .minus =>
      QubitOracle.binaryAxisMinusScore (QubitOracle.blochDot theta u)

/-- Select the mixed-qubit score vector for either binary projective outcome. -/
def mixedAxisOutcomeScoreVector (theta u : Fin 3 → ℝ) :
    BinaryOutcome → Fin 3 → ℝ
  | .plus => mixedAxisPlusScoreVector theta u
  | .minus => mixedAxisMinusScoreVector theta u

/-- Scalar projection of the one-observation score vector. -/
def mixedAxisProjectedScore
    (theta u h : Fin 3 → ℝ) (y : BinaryOutcome) : ℝ :=
  ∑ i : Fin 3, h i * mixedAxisOutcomeScoreVector theta u y i

private theorem mixedEnvelope_blochNormSq_nonneg (x : Fin 3 → ℝ) :
    0 ≤ QubitOracle.blochNormSq x := by
  unfold QubitOracle.blochNormSq
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (x i))

theorem mixedInteriorRadius_sq (theta : Fin 3 → ℝ) :
    mixedInteriorRadius theta ^ 2 = QubitOracle.blochNormSq theta := by
  unfold mixedInteriorRadius
  exact Real.sq_sqrt (mixedEnvelope_blochNormSq_nonneg theta)

theorem mixedInteriorRadius_nonneg (theta : Fin 3 → ℝ) :
    0 ≤ mixedInteriorRadius theta := by
  exact Real.sqrt_nonneg _

theorem mixedInteriorRadius_lt_one
    (theta : Fin 3 → ℝ)
    (hInterior : QubitOracle.blochNormSq theta < 1) :
    mixedInteriorRadius theta < 1 := by
  have hsq := mixedInteriorRadius_sq theta
  have hnonneg := mixedInteriorRadius_nonneg theta
  nlinarith

theorem mixedInteriorGap_pos
    (theta : Fin 3 → ℝ)
    (hInterior : QubitOracle.blochNormSq theta < 1) :
    0 < mixedInteriorGap theta := by
  unfold mixedInteriorGap
  linarith [mixedInteriorRadius_lt_one theta hInterior]

/-- Cauchy-Schwarz turns the physical Bloch interior margin into a uniform
axis-independent bound on the Born parameter. -/
theorem mixedAxis_abs_blochDot_le_radius
    (theta u : Fin 3 → ℝ)
    (hu : QubitOracle.blochNormSq u = 1) :
    |QubitOracle.blochDot theta u| ≤ mixedInteriorRadius theta := by
  have hcs := QubitOracle.bloch_cauchy_schwarz theta u
  have hdotSq :
      QubitOracle.blochDot theta u ^ 2 ≤
        QubitOracle.blochNormSq theta := by
    rw [hu] at hcs
    simpa using hcs
  have habsSq :
      |QubitOracle.blochDot theta u| ^ 2 ≤
        mixedInteriorRadius theta ^ 2 := by
    rw [sq_abs, mixedInteriorRadius_sq]
    exact hdotSq
  have habsNonneg : 0 ≤ |QubitOracle.blochDot theta u| := abs_nonneg _
  have hradiusNonneg := mixedInteriorRadius_nonneg theta
  nlinarith

/-- Uniform lower bound for either binary Born probability. -/
theorem mixedAxisBornProbability_floor
    (theta u : Fin 3 → ℝ)
    (hu : QubitOracle.blochNormSq u = 1)
    (y : BinaryOutcome) :
    mixedInteriorGap theta / 2 ≤
      binaryBornProbability (QubitOracle.blochDot theta u) y := by
  simpa [mixedInteriorGap] using
    (binaryBornProbability_lower_bound
      (QubitOracle.blochDot theta u) (mixedInteriorRadius theta)
      (mixedAxis_abs_blochDot_le_radius theta u hu) y)

/-- Uniform lower bound for either natural-score denominator. -/
theorem mixedAxisScoreDenominator_floor
    (theta u : Fin 3 → ℝ)
    (hu : QubitOracle.blochNormSq u = 1)
    (y : BinaryOutcome) :
    mixedInteriorGap theta ≤
      1 + y.sign * QubitOracle.blochDot theta u := by
  simpa [mixedInteriorGap] using
    (signed_denominator_lower_bound
      (QubitOracle.blochDot theta u) (mixedInteriorRadius theta)
      (mixedAxis_abs_blochDot_le_radius theta u hu) y)

/-- The two Born-probability floors displayed in the usual plus/minus notation. -/
theorem mixedAxisBornProbability_floors
    (theta u : Fin 3 → ℝ)
    (hu : QubitOracle.blochNormSq u = 1) :
    mixedInteriorGap theta / 2 ≤
        QubitOracle.binaryAxisPlusProbability
          (QubitOracle.blochDot theta u) ∧
      mixedInteriorGap theta / 2 ≤
        QubitOracle.binaryAxisMinusProbability
          (QubitOracle.blochDot theta u) := by
  constructor
  · simpa [binaryBornProbability, BinaryOutcome.sign,
      QubitOracle.binaryAxisPlusProbability] using
      (mixedAxisBornProbability_floor theta u hu BinaryOutcome.plus)
  · simpa [binaryBornProbability, BinaryOutcome.sign,
      QubitOracle.binaryAxisMinusProbability, sub_eq_add_neg] using
      (mixedAxisBornProbability_floor theta u hu BinaryOutcome.minus)

/-- The two score-denominator floors displayed explicitly. -/
theorem mixedAxisScoreDenominator_floors
    (theta u : Fin 3 → ℝ)
    (hu : QubitOracle.blochNormSq u = 1) :
    mixedInteriorGap theta ≤ 1 + QubitOracle.blochDot theta u ∧
      mixedInteriorGap theta ≤ 1 - QubitOracle.blochDot theta u := by
  constructor
  · simpa [BinaryOutcome.sign] using
      (mixedAxisScoreDenominator_floor theta u hu BinaryOutcome.plus)
  · simpa [BinaryOutcome.sign, sub_eq_add_neg] using
      (mixedAxisScoreDenominator_floor theta u hu BinaryOutcome.minus)

theorem mixedAxisBornProbabilities_pos
    (theta u : Fin 3 → ℝ)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hu : QubitOracle.blochNormSq u = 1) :
    0 < QubitOracle.binaryAxisPlusProbability
          (QubitOracle.blochDot theta u) ∧
      0 < QubitOracle.binaryAxisMinusProbability
          (QubitOracle.blochDot theta u) := by
  have hgap : 0 < mixedInteriorGap theta :=
    mixedInteriorGap_pos theta hInterior
  have hfloorPos : 0 < mixedInteriorGap theta / 2 :=
    div_pos hgap (by norm_num)
  have hfloors := mixedAxisBornProbability_floors theta u hu
  exact ⟨lt_of_lt_of_le hfloorPos hfloors.1,
    lt_of_lt_of_le hfloorPos hfloors.2⟩

theorem mixedAxisPlusScore_abs_le
    (theta u : Fin 3 → ℝ)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hu : QubitOracle.blochNormSq u = 1) :
    |QubitOracle.binaryAxisPlusScore (QubitOracle.blochDot theta u)| ≤
      (mixedInteriorGap theta)⁻¹ := by
  have hgap : 0 < mixedInteriorGap theta :=
    mixedInteriorGap_pos theta hInterior
  have hden := (mixedAxisScoreDenominator_floors theta u hu).1
  have hdenPos : 0 < 1 + QubitOracle.blochDot theta u :=
    lt_of_lt_of_le hgap hden
  change |(1 + QubitOracle.blochDot theta u)⁻¹| ≤
    (mixedInteriorGap theta)⁻¹
  rw [abs_inv, abs_of_pos hdenPos]
  simpa [one_div] using (one_div_le_one_div_of_le hgap hden)

theorem mixedAxisMinusScore_abs_le
    (theta u : Fin 3 → ℝ)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hu : QubitOracle.blochNormSq u = 1) :
    |QubitOracle.binaryAxisMinusScore (QubitOracle.blochDot theta u)| ≤
      (mixedInteriorGap theta)⁻¹ := by
  have hgap : 0 < mixedInteriorGap theta :=
    mixedInteriorGap_pos theta hInterior
  have hden := (mixedAxisScoreDenominator_floors theta u hu).2
  have hdenPos : 0 < 1 - QubitOracle.blochDot theta u :=
    lt_of_lt_of_le hgap hden
  change |-(1 - QubitOracle.blochDot theta u)⁻¹| ≤
    (mixedInteriorGap theta)⁻¹
  rw [abs_neg, abs_inv, abs_of_pos hdenPos]
  simpa [one_div] using (one_div_le_one_div_of_le hgap hden)

/-- Outcome-uniform scalar-score envelope. -/
theorem mixedAxisOutcomeScalarScore_abs_le
    (theta u : Fin 3 → ℝ)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hu : QubitOracle.blochNormSq u = 1)
    (y : BinaryOutcome) :
    |mixedAxisOutcomeScalarScore theta u y| ≤
      (mixedInteriorGap theta)⁻¹ := by
  cases y with
  | plus => exact mixedAxisPlusScore_abs_le theta u hInterior hu
  | minus => exact mixedAxisMinusScore_abs_le theta u hInterior hu

/-- Every coordinate of a unit Bloch axis has absolute value at most one. -/
theorem unitBlochAxis_coordinate_abs_le_one
    (u : Fin 3 → ℝ)
    (hu : QubitOracle.blochNormSq u = 1)
    (i : Fin 3) :
    |u i| ≤ 1 := by
  have hiSq : u i ^ 2 ≤ QubitOracle.blochNormSq u := by
    unfold QubitOracle.blochNormSq
    exact Finset.single_le_sum
      (fun j _ => sq_nonneg (u j)) (Finset.mem_univ i)
  rw [hu] at hiSq
  have habsSq : |u i| ^ 2 ≤ 1 := by
    simpa [sq_abs] using hiSq
  nlinarith [abs_nonneg (u i)]

theorem mixedAxisOutcomeScoreVector_apply
    (theta u : Fin 3 → ℝ) (y : BinaryOutcome) (i : Fin 3) :
    mixedAxisOutcomeScoreVector theta u y i =
      mixedAxisOutcomeScalarScore theta u y * u i := by
  cases y <;> rfl

/-- Path-independent envelope for every coordinate of every binary score. -/
theorem mixedAxisOutcomeScore_coordinate_abs_le
    (theta u : Fin 3 → ℝ)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hu : QubitOracle.blochNormSq u = 1)
    (y : BinaryOutcome) (i : Fin 3) :
    |mixedAxisOutcomeScoreVector theta u y i| ≤
      (mixedInteriorGap theta)⁻¹ := by
  rw [mixedAxisOutcomeScoreVector_apply, abs_mul]
  calc
    |mixedAxisOutcomeScalarScore theta u y| * |u i| ≤
        (mixedInteriorGap theta)⁻¹ * 1 := by
      exact mul_le_mul
        (mixedAxisOutcomeScalarScore_abs_le theta u hInterior hu y)
        (unitBlochAxis_coordinate_abs_le_one u hu i)
        (abs_nonneg _)
        (inv_nonneg.mpr (le_of_lt (mixedInteriorGap_pos theta hInterior)))
    _ = (mixedInteriorGap theta)⁻¹ := mul_one _

/-- Path-independent envelope for the score projected in any fixed direction.
The finite-coordinate constant is exactly
`(sum_i |h_i|) / (1 - sqrt (blochNormSq theta))`. -/
theorem mixedAxisProjectedScore_abs_le
    (theta u h : Fin 3 → ℝ)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hu : QubitOracle.blochNormSq u = 1)
    (y : BinaryOutcome) :
    |mixedAxisProjectedScore theta u h y| ≤
      mixedProjectedScoreEnvelope theta h := by
  unfold mixedAxisProjectedScore mixedProjectedScoreEnvelope
  calc
    |∑ i : Fin 3, h i * mixedAxisOutcomeScoreVector theta u y i| ≤
        ∑ i : Fin 3, |h i * mixedAxisOutcomeScoreVector theta u y i| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, |h i| * (mixedInteriorGap theta)⁻¹ := by
      refine Finset.sum_le_sum ?_
      intro i hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (mixedAxisOutcomeScore_coordinate_abs_le
          theta u hInterior hu y i)
        (abs_nonneg (h i))
    _ = mixedProjectionL1 h * (mixedInteriorGap theta)⁻¹ := by
      simp [mixedProjectionL1, Finset.sum_mul]

/-- The projected envelope in fully displayed quotient form. -/
theorem mixedAxisProjectedScore_abs_le_explicit
    (theta u h : Fin 3 → ℝ)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hu : QubitOracle.blochNormSq u = 1)
    (y : BinaryOutcome) :
    |mixedAxisProjectedScore theta u h y| ≤
      (∑ i : Fin 3, |h i|) /
        (1 - Real.sqrt (QubitOracle.blochNormSq theta)) := by
  simpa [mixedProjectedScoreEnvelope, mixedProjectionL1,
    mixedInteriorGap, mixedInteriorRadius, div_eq_mul_inv] using
    (mixedAxisProjectedScore_abs_le theta u h hInterior hu y)

/-- Deterministic certificate that discharges a uniform score-envelope premise
for a fixed nonzero interior mixed-qubit truth. The nonzero hypothesis records
the intended truth stratum; only strict interiority is needed analytically. -/
structure MixedUniformScoreEnvelopeCertificate
    (theta : Fin 3 → ℝ) : Prop where
  nonzero : 0 < QubitOracle.blochNormSq theta
  interior : QubitOracle.blochNormSq theta < 1
  gap_pos : 0 < mixedInteriorGap theta
  bornProbabilityFloor :
    ∀ (u : Fin 3 → ℝ), QubitOracle.blochNormSq u = 1 →
      ∀ y : BinaryOutcome,
        mixedInteriorGap theta / 2 ≤
          binaryBornProbability (QubitOracle.blochDot theta u) y
  scoreDenominatorFloor :
    ∀ (u : Fin 3 → ℝ), QubitOracle.blochNormSq u = 1 →
      ∀ y : BinaryOutcome,
        mixedInteriorGap theta ≤
          1 + y.sign * QubitOracle.blochDot theta u
  coordinateScoreBound :
    ∀ (u : Fin 3 → ℝ), QubitOracle.blochNormSq u = 1 →
      ∀ (y : BinaryOutcome) (i : Fin 3),
        |mixedAxisOutcomeScoreVector theta u y i| ≤
          (mixedInteriorGap theta)⁻¹
  projectedScoreBound :
    ∀ (u h : Fin 3 → ℝ), QubitOracle.blochNormSq u = 1 →
      ∀ y : BinaryOutcome,
        |mixedAxisProjectedScore theta u h y| ≤
          mixedProjectedScoreEnvelope theta h

theorem mixedUniformScoreEnvelopeCertificate
    (theta : Fin 3 → ℝ)
    (hNonzero : 0 < QubitOracle.blochNormSq theta)
    (hInterior : QubitOracle.blochNormSq theta < 1) :
    MixedUniformScoreEnvelopeCertificate theta := by
  refine ⟨hNonzero, hInterior, mixedInteriorGap_pos theta hInterior,
    ?_, ?_, ?_, ?_⟩
  · intro u hu y
    exact mixedAxisBornProbability_floor theta u hu y
  · intro u hu y
    exact mixedAxisScoreDenominator_floor theta u hu y
  · intro u hu y i
    exact mixedAxisOutcomeScore_coordinate_abs_le theta u hInterior hu y i
  · intro u h hu y
    exact mixedAxisProjectedScore_abs_le theta u h hInterior hu y

namespace Label

/-- Paper-facing deterministic qubit reduction for the mixed score envelope. -/
theorem lem_SI_mixed_uniform_score_envelope_qubit
    (theta : Fin 3 → ℝ)
    (hNonzero : 0 < QubitOracle.blochNormSq theta)
    (hInterior : QubitOracle.blochNormSq theta < 1) :
    MixedUniformScoreEnvelopeCertificate theta :=
  mixedUniformScoreEnvelopeCertificate theta hNonzero hInterior

end Label

end

end QubitOracle.Paper
