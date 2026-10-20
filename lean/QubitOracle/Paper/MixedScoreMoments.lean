import QubitOracle.Paper.MixedAxisFisher

/-!
# Exact mixed-qubit score moments

This module lifts the checked binary score calculation to the three-component
Bloch score used in the adaptive LAN argument.  The sole regularity premise is
the exact positivity condition `(θ · u)^2 < 1` for the two Born outcomes.
-/

namespace QubitOracle.Paper

noncomputable section

/-- Score vector for the `+` outcome of the projective measurement along `u`. -/
def mixedAxisPlusScoreVector (theta u : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => QubitOracle.binaryAxisPlusScore (QubitOracle.blochDot theta u) * u i

/-- Score vector for the `-` outcome of the projective measurement along `u`. -/
def mixedAxisMinusScoreVector (theta u : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => QubitOracle.binaryAxisMinusScore (QubitOracle.blochDot theta u) * u i

/-- The conditional mixed-axis score has mean zero entrywise. -/
theorem mixedAxisScore_mean_zero
    (theta u : Fin 3 → ℝ)
    (hregular : QubitOracle.blochDot theta u ^ 2 < 1) :
    ∀ i,
      QubitOracle.binaryAxisPlusProbability (QubitOracle.blochDot theta u) *
          mixedAxisPlusScoreVector theta u i +
        QubitOracle.binaryAxisMinusProbability (QubitOracle.blochDot theta u) *
          mixedAxisMinusScoreVector theta u i = 0 := by
  intro i
  let t := QubitOracle.blochDot theta u
  have hcenter := QubitOracle.binaryAxis_expectedScore_eq_zero t hregular
  change
    QubitOracle.binaryAxisPlusProbability t *
          (QubitOracle.binaryAxisPlusScore t * u i) +
        QubitOracle.binaryAxisMinusProbability t *
          (QubitOracle.binaryAxisMinusScore t * u i) = 0
  calc
    _ = (QubitOracle.binaryAxisPlusProbability t *
            QubitOracle.binaryAxisPlusScore t +
          QubitOracle.binaryAxisMinusProbability t *
            QubitOracle.binaryAxisMinusScore t) * u i := by ring
    _ = 0 := by rw [hcenter]; ring

/-- The conditional second score moment is exactly the mixed-axis Fisher
information matrix, entry by entry. -/
theorem mixedAxisScore_secondMoment_eq_fisher
    (theta u : Fin 3 → ℝ)
    (hregular : QubitOracle.blochDot theta u ^ 2 < 1) :
    ∀ i j,
      QubitOracle.binaryAxisPlusProbability (QubitOracle.blochDot theta u) *
            mixedAxisPlusScoreVector theta u i *
            mixedAxisPlusScoreVector theta u j +
        QubitOracle.binaryAxisMinusProbability (QubitOracle.blochDot theta u) *
            mixedAxisMinusScoreVector theta u i *
            mixedAxisMinusScoreVector theta u j =
          QubitOracle.mixedAxisFisher theta u i j := by
  intro i j
  let t := QubitOracle.blochDot theta u
  change
    QubitOracle.binaryAxisPlusProbability t *
            (QubitOracle.binaryAxisPlusScore t * u i) *
            (QubitOracle.binaryAxisPlusScore t * u j) +
        QubitOracle.binaryAxisMinusProbability t *
            (QubitOracle.binaryAxisMinusScore t * u i) *
            (QubitOracle.binaryAxisMinusScore t * u j) =
      QubitOracle.mixedAxisFisher theta u i j
  calc
    _ = QubitOracle.binaryAxisFisherScalar t * (u i * u j) := by
      simp only [QubitOracle.binaryAxisFisherScalar]
      ring
    _ = (1 - t ^ 2)⁻¹ * (u i * u j) := by
      rw [QubitOracle.binaryAxisFisherScalar_eq t hregular]
    _ = QubitOracle.mixedAxisFisher theta u i j := by
      simp [QubitOracle.mixedAxisFisher, QubitOracle.blochOuter,
        Matrix.smul_apply, smul_eq_mul, t]

namespace Label

/-- Supplement equation `eq:SI_mixed_score_moments`. -/
theorem eq_SI_mixed_score_moments
    (theta u : Fin 3 → ℝ)
    (hregular : QubitOracle.blochDot theta u ^ 2 < 1) :
    (∀ i,
      QubitOracle.binaryAxisPlusProbability (QubitOracle.blochDot theta u) *
          mixedAxisPlusScoreVector theta u i +
        QubitOracle.binaryAxisMinusProbability (QubitOracle.blochDot theta u) *
          mixedAxisMinusScoreVector theta u i = 0) ∧
    (∀ i j,
      QubitOracle.binaryAxisPlusProbability (QubitOracle.blochDot theta u) *
            mixedAxisPlusScoreVector theta u i *
            mixedAxisPlusScoreVector theta u j +
        QubitOracle.binaryAxisMinusProbability (QubitOracle.blochDot theta u) *
            mixedAxisMinusScoreVector theta u i *
            mixedAxisMinusScoreVector theta u j =
          QubitOracle.mixedAxisFisher theta u i j) :=
  ⟨mixedAxisScore_mean_zero theta u hregular,
    mixedAxisScore_secondMoment_eq_fisher theta u hregular⟩

end Label

end

end QubitOracle.Paper
