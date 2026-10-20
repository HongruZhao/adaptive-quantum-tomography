import QubitOracle.FiniteGillMassar
/-!
# Fisher information for one-axis mixed-qubit measurements

This file formalizes the paper's equality case for a binary projective
measurement along a unit Bloch axis.  The associated classical Fisher matrix
is the rank-one outer product `u u^T`, divided by
`1 - (r dot u)^2`.  Contracting it with the inverse SLD Fisher matrix
`I - r r^T` gives exactly one.

The final section records the underlying two-outcome score calculation.
-/

namespace QubitOracle

noncomputable section

/-- Fisher matrix of the binary qubit measurement along the Bloch axis `u`. -/
def mixedAxisFisher (r u : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (1 - (blochDot r u) ^ 2)⁻¹ • blochOuter u

/-- For an interior Bloch vector and a unit axis, the binary Fisher
denominator is strictly positive. -/
theorem mixedAxisFisher_denominator_pos
    (r u : Fin 3 → ℝ) (hr : blochNormSq r < 1)
    (hu : blochNormSq u = 1) :
    0 < 1 - (blochDot r u) ^ 2 := by
  rw [sub_pos]
  calc
    (blochDot r u) ^ 2 ≤ blochNormSq r * blochNormSq u :=
      bloch_cauchy_schwarz r u
    _ = blochNormSq r := by simp [hu]
    _ < 1 := hr

/-- The paper's one-axis equality
`trace ((I - r r^T) I_u) = 1` for an interior Bloch vector and a unit axis. -/
theorem trace_qubitSLDFisherInv_mul_mixedAxisFisher
    (r u : Fin 3 → ℝ) (hr : blochNormSq r < 1)
    (hu : blochNormSq u = 1) :
    Matrix.trace (qubitSLDFisherInv r * mixedAxisFisher r u) = 1 := by
  have hdenom : 1 - (blochDot r u) ^ 2 ≠ 0 :=
    ne_of_gt (mixedAxisFisher_denominator_pos r u hr hu)
  rw [mixedAxisFisher, Matrix.mul_smul, Matrix.trace_smul,
    trace_qubitSLDFisherInv_mul_blochOuter]
  simp only [smul_eq_mul]
  rw [hu]
  simpa [hdenom]

/-! ## Binary score calculation -/

/-- Probability of the outcome aligned with the measurement axis. -/
def binaryAxisPlusProbability (t : ℝ) : ℝ :=
  (1 + t) / 2

/-- Probability of the outcome anti-aligned with the measurement axis. -/
def binaryAxisMinusProbability (t : ℝ) : ℝ :=
  (1 - t) / 2

/-- Score of the aligned outcome for the scalar parameter `t = r dot u`. -/
def binaryAxisPlusScore (t : ℝ) : ℝ :=
  (1 + t)⁻¹

/-- Score of the anti-aligned outcome for the scalar parameter
`t = r dot u`. -/
def binaryAxisMinusScore (t : ℝ) : ℝ :=
  -(1 - t)⁻¹

/-- The displayed scores are the probability derivatives divided by the
corresponding probabilities. -/
theorem binaryAxis_scores_eq_probabilityDerivative_ratio
    (t : ℝ) (ht : t ^ 2 < 1) :
    binaryAxisPlusScore t =
        ((1 : ℝ) / 2) / binaryAxisPlusProbability t ∧
      binaryAxisMinusScore t =
        (-(1 : ℝ) / 2) / binaryAxisMinusProbability t := by
  have hplus : 1 + t ≠ 0 := by
    intro hzero
    have ht_eq : t = -1 := by linarith
    rw [ht_eq] at ht
    norm_num at ht
  have hminus : 1 - t ≠ 0 := by
    intro hzero
    have ht_eq : t = 1 := by linarith
    rw [ht_eq] at ht
    norm_num at ht
  constructor
  · simp only [binaryAxisPlusScore, binaryAxisPlusProbability]
    field_simp [hplus] <;> ring
  · simp only [binaryAxisMinusScore, binaryAxisMinusProbability]
    field_simp [hminus] <;> ring

/-- The binary score has zero expectation. -/
theorem binaryAxis_expectedScore_eq_zero
    (t : ℝ) (ht : t ^ 2 < 1) :
    binaryAxisPlusProbability t * binaryAxisPlusScore t +
        binaryAxisMinusProbability t * binaryAxisMinusScore t = 0 := by
  have hplus : 1 + t ≠ 0 := by
    intro hzero
    have ht_eq : t = -1 := by linarith
    rw [ht_eq] at ht
    norm_num at ht
  have hminus : 1 - t ≠ 0 := by
    intro hzero
    have ht_eq : t = 1 := by linarith
    rw [ht_eq] at ht
    norm_num at ht
  simp only [binaryAxisPlusProbability, binaryAxisMinusProbability,
    binaryAxisPlusScore, binaryAxisMinusScore]
  field_simp [hplus, hminus] <;> ring

/-- Scalar Fisher information of the two binary outcomes. -/
def binaryAxisFisherScalar (t : ℝ) : ℝ :=
  binaryAxisPlusProbability t * (binaryAxisPlusScore t) ^ 2 +
    binaryAxisMinusProbability t * (binaryAxisMinusScore t) ^ 2

/-- The binary Fisher information is `1 / (1 - t^2)`. -/
theorem binaryAxisFisherScalar_eq
    (t : ℝ) (ht : t ^ 2 < 1) :
    binaryAxisFisherScalar t = (1 - t ^ 2)⁻¹ := by
  have hplus : 1 + t ≠ 0 := by
    intro hzero
    have ht_eq : t = -1 := by linarith
    rw [ht_eq] at ht
    norm_num at ht
  have hminus : 1 - t ≠ 0 := by
    intro hzero
    have ht_eq : t = 1 := by linarith
    rw [ht_eq] at ht
    norm_num at ht
  have hdenom : 1 - t ^ 2 ≠ 0 := ne_of_gt (sub_pos.mpr ht)
  simp only [binaryAxisFisherScalar, binaryAxisPlusProbability,
    binaryAxisMinusProbability, binaryAxisPlusScore, binaryAxisMinusScore]
  field_simp [hplus, hminus, hdenom] <;> ring

/-- The rank-one matrix definition is exactly the scalar binary Fisher
information multiplying `u u^T`. -/
theorem mixedAxisFisher_eq_binaryAxisFisherScalar_smul
    (r u : Fin 3 → ℝ) (hr : blochNormSq r < 1)
    (hu : blochNormSq u = 1) :
    mixedAxisFisher r u =
      binaryAxisFisherScalar (blochDot r u) • blochOuter u := by
  have hdot : (blochDot r u) ^ 2 < 1 :=
    sub_pos.mp (mixedAxisFisher_denominator_pos r u hr hu)
  rw [binaryAxisFisherScalar_eq (blochDot r u) hdot]
  rfl


end

end QubitOracle
