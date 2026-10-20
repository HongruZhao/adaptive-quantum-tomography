import QubitOracle.Paper.OneQubitMixedPolynomialInformationConvergence
import QubitOracle.Paper.OneQubitVaryingRowHallHeydeReduction

/-!
# Closed Hall--Heyde score CLT for the polynomial mixed-qubit protocol

Coordinate `n` uses exactly `(n+1)^5` complete Pauli pilot blocks and
`(n+1)^6` complete selected-frame cycles. All model-specific probability,
Fisher-information, row-size, and Lindeberg claims are proved in Lean. The
last score-CLT theorem uses only the cited Hall--Heyde Corollary 3.1 atom.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace QubitOracle.Paper

noncomputable section

open MixedExactCycleScalarTriangularArrayData

theorem mixedPolynomialTruthFrameDirectionalInformation_nonnegative_closed
    (theta h b : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    0 ≤ mixedPolynomialTruthFrameDirectionalInformation theta h b := by
  have hDomain : LocalContinuousFrameDomain b theta := ⟨hTruth.1, hSeed⟩
  unfold mixedPolynomialTruthFrameDirectionalInformation
    mixedPolynomialFrameDirectionalInformation
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro k _hk
  apply div_nonneg (sq_nonneg _)
  apply sub_nonneg.mpr
  have hUnit :
      blochNormSq
          (mixedTwoStageFrameAxis (localContinuousQubitFrame b theta) k) = 1 := by
    change blochNormSq
      (qubitFrameAxis (localContinuousQubitFrame b theta) k) = 1
    exact localContinuousQubitFrame_axis_unit hDomain k
  calc
    blochDot theta
          (mixedTwoStageFrameAxis (localContinuousQubitFrame b theta) k) ^ 2 ≤
        blochNormSq theta *
          blochNormSq
            (mixedTwoStageFrameAxis (localContinuousQubitFrame b theta) k) :=
      blochDot_sq_le_normSq_mul_normSq theta _
    _ = blochNormSq theta := by rw [hUnit, mul_one]
    _ ≤ 1 := le_of_lt hTruth.2

/-- The row datum at protocol index `n`; its internal exact-cycle index is
later set to `mixedPolynomialRFinal n`. -/
def mixedPolynomialHallHeydeRowData
    (b theta h : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (n : ℕ) : MixedExactCycleScalarTriangularArrayData :=
  MixedExactCycleScalarTriangularArrayData.mk
    (fun _r => mixedPolynomialQPilot n) theta h
    (fun _r => mixedPolynomialPilotSelectedFinalFrame b n)
    (mixedPolynomialTruthFrameDirectionalInformation theta h b)
    (mixedPolynomialTruthFrameDirectionalInformation_nonnegative_closed
      theta h b hTruth hSeed)
    hTruth.2

abbrev mixedPolynomialHallHeydeRowSize : ℕ → ℕ :=
  mixedPolynomialRFinal

abbrev MixedPolynomialHallHeydeCommonOmega
    (b theta h : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :=
  CommonOmega (mixedPolynomialHallHeydeRowData b theta h hTruth hSeed)
    mixedPolynomialHallHeydeRowSize

/-- The exact predictable Fisher expression is the paper's normalized
directional information at every protocol row. -/
theorem mixedPolynomialHallHeydeRowData_explicitFisher_eq
    (b theta h : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (n : ℕ)
    (path : PauliPilotPath (mixedPolynomialQPilot n)) :
    MixedExactCycleScalarTriangularArrayData.explicitNormalizedFisher
        (mixedPolynomialHallHeydeRowData b theta h hTruth hSeed n)
        (mixedPolynomialHallHeydeRowSize n) path =
      mixedPolynomialNormalizedDirectionalInformation theta h b n path := by
  simp only [mixedPolynomialHallHeydeRowData,
    MixedExactCycleScalarTriangularArrayData.explicitNormalizedFisher,
    mixedExactCycleNormalizedDirectionalFisher,
    mixedExactCycleOneShotNormalizedDirectionalFisher]
  rw [← Finset.sum_div]
  rfl

/-- The finite row measure is exactly the explicit two-stage Born measure. -/
theorem mixedPolynomialHallHeydeRowData_rowMeasure_eq
    (b theta h : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (n : ℕ) :
    MixedExactCycleScalarTriangularArrayData.mathlibRowMeasure
        (mixedPolynomialHallHeydeRowData b theta h hTruth hSeed n)
        (mixedPolynomialHallHeydeRowSize n) =
      mixedTwoStageFiniteBornMeasure theta
        (mixedPolynomialPilotSelectedFinalFrame b n) := by
  unfold mixedPolynomialHallHeydeRowData
    MixedExactCycleScalarTriangularArrayData.mathlibRowMeasure
    mixedTwoStageFiniteBornMeasure
  congr 1
  funext row
  congr 1
  rw [ENNReal.coe_nnreal_eq]
  rfl

/-- Exact Pauli-pilot marginal under every polynomial two-stage row law. -/
theorem mixedPolynomialHallHeydeRowData_pilotMarginal
    (b theta h : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (n : ℕ) (event : Set (PauliPilotPath (mixedPolynomialQPilot n))) :
    MixedExactCycleScalarTriangularArrayData.mathlibRowMeasure
        (mixedPolynomialHallHeydeRowData b theta h hTruth hSeed n)
        (mixedPolynomialHallHeydeRowSize n)
          ((fun row => row.1) ⁻¹' event) =
      pauliPilotBornProductMeasure theta event := by
  rw [mixedPolynomialHallHeydeRowData_rowMeasure_eq]
  exact mixedTwoStageFiniteBornMeasure_pilotMarginal theta
    (mixedPolynomialPilotSelectedFinalFrame b n)
    (mixedNonzeroInterior_pauliPilotPhysical theta hTruth) event

/-- Common-space Fisher deviation probability equals the paper's finite pilot
deviation probability, with no asymptotic theorem used. -/
theorem mixedPolynomialHallHeyde_commonDeviationProbability_eq
    (b theta h : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (epsilon : ℝ) (n : ℕ) :
    let A := mixedPolynomialHallHeydeRowData b theta h hTruth hSeed
    commonMeasure A mixedPolynomialHallHeydeRowSize
        {omega |
          epsilon ≤
            |(A n).explicitNormalizedFisher
                (mixedPolynomialHallHeydeRowSize n) (omega n).1 -
              mixedPolynomialTruthFrameDirectionalInformation theta h b|} =
      pauliPilotBornProductMeasure theta
        {path |
          epsilon ≤
            |mixedPolynomialNormalizedDirectionalInformation theta h b n path -
              mixedPolynomialTruthFrameDirectionalInformation theta h b|} := by
  let A := mixedPolynomialHallHeydeRowData b theta h hTruth hSeed
  let pilotEvent : Set (PauliPilotPath (mixedPolynomialQPilot n)) :=
    {path |
      epsilon ≤
        |mixedPolynomialNormalizedDirectionalInformation theta h b n path -
          mixedPolynomialTruthFrameDirectionalInformation theta h b|}
  have hCommonRow := commonDeviationProbability_eq_row A
    mixedPolynomialHallHeydeRowSize
    (fun m row => (A m).explicitNormalizedFisher
      (mixedPolynomialHallHeydeRowSize m) row.1)
    (mixedPolynomialTruthFrameDirectionalInformation theta h b) epsilon n
  have hEvent :
      {row : CommonRow A mixedPolynomialHallHeydeRowSize n |
          epsilon ≤
            |(A n).explicitNormalizedFisher
                (mixedPolynomialHallHeydeRowSize n) row.1 -
              mixedPolynomialTruthFrameDirectionalInformation theta h b|} =
        (fun row : CommonRow A mixedPolynomialHallHeydeRowSize n => row.1) ⁻¹'
          pilotEvent := by
    ext row
    change epsilon ≤
        |(A n).explicitNormalizedFisher
            (mixedPolynomialHallHeydeRowSize n) row.1 -
          mixedPolynomialTruthFrameDirectionalInformation theta h b| ↔
      epsilon ≤
        |mixedPolynomialNormalizedDirectionalInformation theta h b n row.1 -
          mixedPolynomialTruthFrameDirectionalInformation theta h b|
    rw [mixedPolynomialHallHeydeRowData_explicitFisher_eq
      b theta h hTruth hSeed n row.1]
  calc
    commonMeasure A mixedPolynomialHallHeydeRowSize
        {omega |
          epsilon ≤
            |(A n).explicitNormalizedFisher
                (mixedPolynomialHallHeydeRowSize n) (omega n).1 -
              mixedPolynomialTruthFrameDirectionalInformation theta h b|} =
      commonRowMeasure A mixedPolynomialHallHeydeRowSize n
        {row |
          epsilon ≤
            |(A n).explicitNormalizedFisher
                (mixedPolynomialHallHeydeRowSize n) row.1 -
              mixedPolynomialTruthFrameDirectionalInformation theta h b|} := by
        simpa [liftRowVariable] using hCommonRow
    _ = commonRowMeasure A mixedPolynomialHallHeydeRowSize n
        ((fun row : CommonRow A mixedPolynomialHallHeydeRowSize n => row.1) ⁻¹'
          pilotEvent) := by rw [hEvent]
    _ = pauliPilotBornProductMeasure theta pilotEvent := by
      unfold commonRowMeasure
      exact mixedPolynomialHallHeydeRowData_pilotMarginal
        b theta h hTruth hSeed n pilotEvent
    _ = pauliPilotBornProductMeasure theta
        {path |
          epsilon ≤
            |mixedPolynomialNormalizedDirectionalInformation theta h b n path -
              mixedPolynomialTruthFrameDirectionalInformation theta h b|} := rfl

/-- The final-cycle schedule tends to infinity. -/
theorem mixedPolynomialHallHeydeRowSize_tendsto_atTop :
    Tendsto mixedPolynomialHallHeydeRowSize atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro N
  refine ⟨N, ?_⟩
  intro n hn
  change N ≤ mixedPolynomialRFinal n
  rw [mixedPolynomialRFinal_eq]
  calc
    N ≤ n := hn
    _ ≤ n + 1 := Nat.le_succ n
    _ ≤ (n + 1) ^ 6 := le_self_pow (by omega) (by norm_num)

/-- The normalized one-shot score envelope vanishes along the exact
polynomial final-cycle schedule. -/
theorem mixedPolynomialHallHeyde_envelope_tendsto_zero
    (b theta h : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    VaryingMaximumJumpEnvelopeTendsToZero
      (mixedPolynomialHallHeydeRowData b theta h hTruth hSeed)
      mixedPolynomialHallHeydeRowSize := by
  let B0 := mixedPolynomialHallHeydeRowData b theta h hTruth hSeed 0
  have hLimit := B0.maximumJumpEnvelope_tendsto_zero.comp
    mixedPolynomialHallHeydeRowSize_tendsto_atTop
  unfold VaryingMaximumJumpEnvelopeTendsToZero
  have hEq :
      (fun n =>
        MixedExactCycleScalarTriangularArrayData.maximumJumpEnvelope
          (mixedPolynomialHallHeydeRowData b theta h hTruth hSeed n)
          (mixedPolynomialHallHeydeRowSize n)) =
        (B0.maximumJumpEnvelope ∘ mixedPolynomialHallHeydeRowSize) := by
    funext n
    rfl
  rw [hEq]
  exact hLimit

/-- The concrete polynomial protocol satisfies the common-space Fisher
convergence premise. -/
theorem mixedPolynomialHallHeyde_fisherConvergesInProbability
    (b theta h : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hHoeffding : MixedPolynomialFinitePilotHoeffdingContracts theta
      (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)) :
    VaryingCommonFisherConvergesInProbability
      (mixedPolynomialHallHeydeRowData b theta h hTruth hSeed)
      mixedPolynomialHallHeydeRowSize
      (mixedPolynomialTruthFrameDirectionalInformation theta h b) := by
  have hPolynomial :=
    mixedPolynomialNormalizedDirectionalInformation_convergesInProbability
      b theta h hTruth hSeed hHoeffding
  intro epsilon hepsilon
  have hTendsto := hPolynomial epsilon hepsilon
  refine hTendsto.congr' ?_
  exact Filter.Eventually.of_forall fun n =>
    (mixedPolynomialHallHeyde_commonDeviationProbability_eq
      b theta h hTruth hSeed epsilon n).symm

/-- Paper-faithful scalar final-score CLT. Its only non-foundational axiom is
Hall and Heyde (1980), Corollary 3.1. -/
theorem mixedPolynomial_exactCycle_targetScoreCLT
    (b theta h : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hHoeffding : MixedPolynomialFinitePilotHoeffdingContracts theta
      (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)) :
    VaryingExactCycleScalarScoreCLT
      (mixedPolynomialHallHeydeRowData b theta h hTruth hSeed)
      mixedPolynomialHallHeydeRowSize
      (mixedPolynomialTruthFrameDirectionalInformation theta h b) := by
  exact varyingExactCycleScalarScoreCLT_of_hallHeyde
    (mixedPolynomialHallHeydeRowData b theta h hTruth hSeed)
    mixedPolynomialHallHeydeRowSize
    (fun n => mixedPolynomialRFinal_pos n)
    (mixedPolynomialTruthFrameDirectionalInformation theta h b)
    (mixedPolynomialTruthFrameDirectionalInformation_nonnegative_closed
      theta h b hTruth hSeed)
    (mixedPolynomialHallHeyde_fisherConvergesInProbability
      b theta h hTruth hSeed hHoeffding)
    (mixedPolynomialHallHeyde_envelope_tendsto_zero
      b theta h hTruth hSeed)

end
end QubitOracle.Paper
