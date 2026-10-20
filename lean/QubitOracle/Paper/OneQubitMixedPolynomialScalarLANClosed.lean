import QubitOracle.Paper.OneQubitMixedPolynomialHallHeydeClosed
import QubitOracle.Paper.OneQubitMixedTotalScaleResidualCertificate
import QubitOracle.Paper.MathlibHoeffding1963Bridge
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Closed scalar LAN theorem for the concrete polynomial mixed-qubit protocol

This file combines the paper-faithful exact polynomial score CLT with the
total-observation residual certificate.  The pilot and final-row calculations,
the information convergence, and Hoeffding concentration are kernel-proved.
The sole external scientific theorem used by the endpoint is the
source-faithful Hall--Heyde martingale CLT atom.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace QubitOracle.Paper

noncomputable section


attribute [local instance] MixedExactCycleScalarTriangularArrayData.rowMeasurableSpace
  MixedExactCycleScalarTriangularArrayData.rowMeasurableSingletonClass
  mixedPolynomialTotalScaleRowMeasurableSpace
  mixedPolynomialTotalScaleRowMeasurableSingletonClass

private abbrev mixedPolynomialScalarLANArray
    (b theta h : Fin 3 → ℝ)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :=
  mixedPolynomialHallHeydeRowData b theta h hTruth hSeed

/-- Common product sample space carrying every concrete polynomial row. -/
abbrev MixedPolynomialScalarLANCommonOmega
    (b theta h : Fin 3 → ℝ)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :=
  MixedExactCycleScalarTriangularArrayData.CommonOmega
    (mixedPolynomialScalarLANArray b theta h hTruth hSeed)
    mixedPolynomialHallHeydeRowSize

/-- Exact common product law of the concrete polynomial rows. -/
noncomputable def mixedPolynomialScalarLANCommonMeasure
    (b theta h : Fin 3 → ℝ)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    Measure (MixedPolynomialScalarLANCommonOmega b theta h hTruth hSeed) :=
  MixedExactCycleScalarTriangularArrayData.commonMeasure
    (mixedPolynomialScalarLANArray b theta h hTruth hSeed)
    mixedPolynomialHallHeydeRowSize

local instance mixedPolynomialScalarLANCommonMeasure_isProbabilityMeasure
    (b theta h : Fin 3 → ℝ)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    IsProbabilityMeasure
      (mixedPolynomialScalarLANCommonMeasure b theta h hTruth hSeed) := by
  unfold mixedPolynomialScalarLANCommonMeasure
  infer_instance

/-- The concrete total-scale row, exposed through the common-space row type. -/
private def mixedPolynomialScalarLANRowResidual
    (b theta h : Fin 3 → ℝ)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (n : ℕ)
    (row : MixedExactCycleScalarTriangularArrayData.CommonRow
      (mixedPolynomialScalarLANArray b theta h hTruth hSeed)
      mixedPolynomialHallHeydeRowSize n) : ℝ :=
  mixedPolynomialTotalScaleResidual theta h b n row

/-- The concrete complete likelihood, exposed through the common-space row type. -/
private def mixedPolynomialScalarLANRowCompleteLogLikelihood
    (b theta h : Fin 3 → ℝ)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (n : ℕ)
    (row : MixedExactCycleScalarTriangularArrayData.CommonRow
      (mixedPolynomialScalarLANArray b theta h hTruth hSeed)
      mixedPolynomialHallHeydeRowSize n) : ℝ :=
  mixedPolynomialTotalScaleCompleteLogLikelihood theta h b n row

/-- The common row law is definitionally the paper's concrete two-stage law. -/
private theorem mixedPolynomialScalarLANCommonRowMeasure_eq
    (b theta h : Fin 3 → ℝ)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (n : ℕ) :
    MixedExactCycleScalarTriangularArrayData.commonRowMeasure
        (mixedPolynomialScalarLANArray b theta h hTruth hSeed)
        mixedPolynomialHallHeydeRowSize n =
      mixedPolynomialTotalScaleRowMeasure theta b n := by
  unfold MixedExactCycleScalarTriangularArrayData.commonRowMeasure
    mixedPolynomialScalarLANArray
  exact mixedPolynomialHallHeydeRowData_rowMeasure_eq
    b theta h hTruth hSeed n

set_option backward.isDefEq.respectTransparency.types false in
/-- Pushforward of the common product law by a finite-row observable is
exactly the pushforward of the concrete two-stage Born row law.  This is a
measure-theoretic transport identity, not an asymptotic assumption. -/
theorem mixedPolynomialScalarLANCommonMeasure_map_rowVariable
    (b theta h : Fin 3 → ℝ)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (n : ℕ) (g : MixedPolynomialTotalScaleRow n → ℝ)
    (hg : Measurable g) :
    (mixedPolynomialScalarLANCommonMeasure b theta h hTruth hSeed).map
        (fun omega => g (omega n)) =
      (mixedPolynomialTotalScaleRowMeasure theta b n).map g := by
  change
    (mixedPolynomialScalarLANCommonMeasure b theta h hTruth hSeed).map
        (g ∘ MixedExactCycleScalarTriangularArrayData.rowCoordinate
          (mixedPolynomialScalarLANArray b theta h hTruth hSeed)
          mixedPolynomialHallHeydeRowSize n) =
      (mixedPolynomialTotalScaleRowMeasure theta b n).map g
  rw [← Measure.map_map hg
    (MixedExactCycleScalarTriangularArrayData.rowCoordinate_measurable
      (mixedPolynomialScalarLANArray b theta h hTruth hSeed)
      mixedPolynomialHallHeydeRowSize n)]
  unfold mixedPolynomialScalarLANCommonMeasure
  exact congrArg (fun mu => mu.map g)
    ((MixedExactCycleScalarTriangularArrayData.commonMeasure_map_coordinate
        (mixedPolynomialScalarLANArray b theta h hTruth hSeed)
        mixedPolynomialHallHeydeRowSize n).trans
      (mixedPolynomialScalarLANCommonRowMeasure_eq
        b theta h hTruth hSeed n))

/-- The fixed-direction Hall--Heyde terminal row score. -/
def mixedPolynomialCommonFixedFinalScore
    (b theta h : Fin 3 → ℝ)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (n : ℕ)
    (omega : MixedPolynomialScalarLANCommonOmega b theta h hTruth hSeed) : ℝ :=
  hallHeydeDeterministicVarianceRowSum
    (MixedExactCycleScalarTriangularArrayData.varyingExactCycleRowLength
      mixedPolynomialHallHeydeRowSize)
    (MixedExactCycleScalarTriangularArrayData.varyingExactCycleScoreIncrement
      (mixedPolynomialScalarLANArray b theta h hTruth hSeed)
      mixedPolynomialHallHeydeRowSize)
    n omega

/-- The same final score after converting root-final normalization to the
actual root-total normalization. -/
def mixedPolynomialCommonTotalScaleFinalScore
    (b theta h : Fin 3 → ℝ)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (n : ℕ)
    (omega : MixedPolynomialScalarLANCommonOmega b theta h hTruth hSeed) : ℝ :=
  mixedPolynomialTotalScaleRootFinalRatio n *
    mixedPolynomialCommonFixedFinalScore b theta h hTruth hSeed n omega

/-- Complete pilot-plus-final likelihood lifted to the common product law. -/
def mixedPolynomialCommonCompleteLogLikelihood
    (b theta h : Fin 3 → ℝ)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (n : ℕ)
    (omega : MixedPolynomialScalarLANCommonOmega b theta h hTruth hSeed) : ℝ :=
  MixedExactCycleScalarTriangularArrayData.liftRowVariable
    (mixedPolynomialScalarLANArray b theta h hTruth hSeed)
    mixedPolynomialHallHeydeRowSize n
    (mixedPolynomialScalarLANRowCompleteLogLikelihood
      b theta h hTruth hSeed n) omega

/-- Total-scale likelihood residual lifted to the common product law. -/
def mixedPolynomialCommonResidual
    (b theta h : Fin 3 → ℝ)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (n : ℕ)
    (omega : MixedPolynomialScalarLANCommonOmega b theta h hTruth hSeed) : ℝ :=
  MixedExactCycleScalarTriangularArrayData.liftRowVariable
    (mixedPolynomialScalarLANArray b theta h hTruth hSeed)
    mixedPolynomialHallHeydeRowSize n
    (mixedPolynomialScalarLANRowResidual b theta h hTruth hSeed n) omega

/-- Exact linear homogeneity of the finite final score. -/
theorem mixedExactCycleLinearScoreTerm_scale_closed
    {q r : ℕ} (theta h : Fin 3 → ℝ) (c : ℝ)
    (selected : PilotSelectedFinalFrame q) (pilot : PauliPilotPath q)
    (finalPath : MixedTwoStageFinalPath (3 * r)) :
    mixedExactCycleLinearScoreTerm theta (fun i ↦ c * h i)
        selected pilot finalPath =
      c * mixedExactCycleLinearScoreTerm theta h selected pilot finalPath := by
  unfold mixedExactCycleLinearScoreTerm
    mixedExactCycleNormalizedDirectionalScore
    mixedTwoStageFinalPathDirectionalScore
    mixedTwoStageFinalShotDirectionalScore
    mixedTwoStageAxisDirectionalScore
  simp_rw [mixedPolynomialTotalScale_blochDot_scale c h]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

/-- The Hall--Heyde row sum is definitionally the fixed-direction exact-cycle
linear score of row `n`. -/
theorem mixedPolynomialCommonFixedFinalScore_eq_linearScore
    (b theta h : Fin 3 → ℝ)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (n : ℕ)
    (omega : MixedPolynomialScalarLANCommonOmega b theta h hTruth hSeed) :
    mixedPolynomialCommonFixedFinalScore b theta h hTruth hSeed n omega =
      mixedExactCycleLinearScoreTerm theta h
        (mixedPolynomialTotalScaleSelectedFrame b n)
        (omega n).1 (omega n).2 := by
  rfl

/-- The Slutsky-scaled common score is exactly the final linear score appearing
in the total-scale likelihood decomposition. -/
theorem mixedPolynomialCommonTotalScaleFinalScore_eq_rowScore
    (b theta h : Fin 3 → ℝ)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (n : ℕ)
    (omega : MixedPolynomialScalarLANCommonOmega b theta h hTruth hSeed) :
    mixedPolynomialCommonTotalScaleFinalScore b theta h hTruth hSeed n omega =
      mixedPolynomialTotalScaleFinalLinearScore theta h b n (omega n) := by
  rw [mixedPolynomialCommonTotalScaleFinalScore,
    mixedPolynomialCommonFixedFinalScore_eq_linearScore]
  unfold mixedPolynomialTotalScaleFinalLinearScore
    mixedPolynomialTotalScaleDirection
  exact (mixedExactCycleLinearScoreTerm_scale_closed theta h
    (mixedPolynomialTotalScaleRootFinalRatio n)
    (mixedPolynomialTotalScaleSelectedFrame b n) (omega n).1 (omega n).2).symm

/-- Fixed-direction scalar score CLT, inherited from the exact Hall--Heyde
reduction. -/
theorem mixedPolynomialCommonFixedFinalScore_CLT
    (b theta h : Fin 3 → ℝ)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hHoeffding : MixedPolynomialFinitePilotHoeffdingContracts theta
      (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)) :
    TendstoInDistribution
      (mixedPolynomialCommonFixedFinalScore b theta h hTruth hSeed)
      atTop id
      (fun _ ↦ mixedPolynomialScalarLANCommonMeasure
        b theta h hTruth hSeed)
      (gaussianReal 0
        (mixedPolynomialTruthFrameDirectionalInformation theta h b).toNNReal) := by
  change MixedExactCycleScalarTriangularArrayData.VaryingExactCycleScalarScoreCLT
    (mixedPolynomialHallHeydeRowData b theta h hTruth hSeed)
    mixedPolynomialHallHeydeRowSize
    (mixedPolynomialTruthFrameDirectionalInformation theta h b)
  exact mixedPolynomial_exactCycle_targetScoreCLT
    b theta h hTruth hSeed hHoeffding

/-- The deterministic root-final/root-total factor converges in measure to
one on the common probability space. -/
theorem mixedPolynomialRootFinalRatio_tendstoInMeasure_one
    (b theta h : Fin 3 → ℝ)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    TendstoInMeasure
      (mixedPolynomialScalarLANCommonMeasure b theta h hTruth hSeed)
      (fun n (_omega : MixedPolynomialScalarLANCommonOmega
        b theta h hTruth hSeed) ↦ mixedPolynomialTotalScaleRootFinalRatio n)
      atTop (fun _ ↦ (1 : ℝ)) := by
  rw [tendstoInMeasure_iff_norm]
  intro epsilon hepsilon
  have hnorm : Tendsto
      (fun n : ℕ => ‖mixedPolynomialTotalScaleRootFinalRatio n - (1 : ℝ)‖)
      atTop (nhds 0) := by
    simpa using
      (mixedPolynomialTotalScaleRootFinalRatio_tendsto_one.sub
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1))).norm
  have hsmall : ∀ᶠ n : ℕ in atTop,
      ‖mixedPolynomialTotalScaleRootFinalRatio n - (1 : ℝ)‖ < epsilon :=
    (tendsto_order.1 hnorm).2 epsilon hepsilon
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hsmall] with n hn
  have hempty :
      {omega : MixedPolynomialScalarLANCommonOmega b theta h hTruth hSeed |
        epsilon ≤
          ‖mixedPolynomialTotalScaleRootFinalRatio n - (1 : ℝ)‖} = ∅ := by
    ext omega
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact not_le_of_gt hn
  symm
  change mixedPolynomialScalarLANCommonMeasure b theta h hTruth hSeed
      {omega | epsilon ≤
        ‖mixedPolynomialTotalScaleRootFinalRatio n - (1 : ℝ)‖} = 0
  rw [hempty, measure_empty]

/-- Total-observation scalar score CLT.  This is Mathlib Slutsky applied to
the proved fixed-direction score CLT and the deterministic scale factor. -/
theorem mixedPolynomialCommonTotalScaleFinalScore_CLT
    (b theta h : Fin 3 → ℝ)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hHoeffding : MixedPolynomialFinitePilotHoeffdingContracts theta
      (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)) :
    TendstoInDistribution
      (mixedPolynomialCommonTotalScaleFinalScore b theta h hTruth hSeed)
      atTop id
      (fun _ ↦ mixedPolynomialScalarLANCommonMeasure
        b theta h hTruth hSeed)
      (gaussianReal 0
        (mixedPolynomialTruthFrameDirectionalInformation theta h b).toNNReal) := by
  have hfixed := mixedPolynomialCommonFixedFinalScore_CLT
    b theta h hTruth hSeed hHoeffding
  have hfactor := mixedPolynomialRootFinalRatio_tendstoInMeasure_one
    b theta h hTruth hSeed
  have hproduct :=
    hfixed.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := fun p : ℝ × ℝ ↦ p.2 * p.1) (by fun_prop) hfactor
      (fun _n ↦ measurable_const.aemeasurable)
  change TendstoInDistribution
    (fun n omega ↦ mixedPolynomialTotalScaleRootFinalRatio n *
      mixedPolynomialCommonFixedFinalScore b theta h hTruth hSeed n omega)
    atTop (fun x : ℝ ↦ x)
    (fun _ ↦ mixedPolynomialScalarLANCommonMeasure b theta h hTruth hSeed)
    (gaussianReal 0
      (mixedPolynomialTruthFrameDirectionalInformation theta h b).toNNReal)
  simpa only [Prod.snd, Prod.fst, id_eq, one_mul] using hproduct

/-- The row-specific residual certificate transported to the exact common
product law. -/
theorem mixedPolynomialCommonResidual_tendstoInMeasure_zero
    (b theta h : Fin 3 → ℝ)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hHoeffding : MixedPolynomialFinitePilotHoeffdingContracts theta
      (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)) :
    TendstoInMeasure
      (mixedPolynomialScalarLANCommonMeasure b theta h hTruth hSeed)
      (mixedPolynomialCommonResidual b theta h hTruth hSeed)
      atTop 0 := by
  rw [tendstoInMeasure_iff_norm]
  intro epsilon hepsilon
  have hrow := mixedPolynomialTotalScaleResidual_convergesInProbability
    theta h b hTruth hSeed hHoeffding epsilon hepsilon
  have hprob : ∀ n : ℕ,
      mixedPolynomialScalarLANCommonMeasure b theta h hTruth hSeed
          {omega | epsilon ≤
            ‖mixedPolynomialCommonResidual b theta h hTruth hSeed n omega‖} =
        mixedPolynomialTotalScaleRowMeasure theta b n
          {row | epsilon ≤
            |mixedPolynomialTotalScaleResidual theta h b n row|} := by
    intro n
    calc
      mixedPolynomialScalarLANCommonMeasure b theta h hTruth hSeed
          {omega | epsilon ≤
            ‖mixedPolynomialCommonResidual b theta h hTruth hSeed n omega‖} =
        MixedExactCycleScalarTriangularArrayData.commonRowMeasure
          (mixedPolynomialScalarLANArray b theta h hTruth hSeed)
          mixedPolynomialHallHeydeRowSize n
          {row | |mixedPolynomialScalarLANRowResidual
              b theta h hTruth hSeed n row - 0| ≥
            epsilon} := by
              simpa [mixedPolynomialScalarLANCommonMeasure,
                mixedPolynomialCommonResidual, Real.norm_eq_abs] using
                (MixedExactCycleScalarTriangularArrayData.commonDeviationProbability_eq_row
                  (mixedPolynomialScalarLANArray b theta h hTruth hSeed)
                  mixedPolynomialHallHeydeRowSize
                  (fun n row ↦
                    mixedPolynomialScalarLANRowResidual
                      b theta h hTruth hSeed n row)
                  0 epsilon n)
      _ = mixedPolynomialTotalScaleRowMeasure theta b n
          {row | epsilon ≤
            |mixedPolynomialTotalScaleResidual theta h b n row|} := by
              rw [mixedPolynomialScalarLANCommonRowMeasure_eq]
              simp [mixedPolynomialScalarLANRowResidual]
              rfl
  have hfun :
      (fun n : ℕ ↦
        mixedPolynomialScalarLANCommonMeasure b theta h hTruth hSeed
          {omega | epsilon ≤
            ‖mixedPolynomialCommonResidual b theta h hTruth hSeed n omega‖}) =
      (fun n : ℕ ↦
        mixedPolynomialTotalScaleRowMeasure theta b n
          {row | epsilon ≤
            |mixedPolynomialTotalScaleResidual theta h b n row|}) := by
    funext n
    exact hprob n
  simpa only [Pi.zero_apply, sub_zero] using (show
    Tendsto
      (fun n : ℕ ↦
        mixedPolynomialScalarLANCommonMeasure b theta h hTruth hSeed
          {omega | epsilon ≤
            ‖mixedPolynomialCommonResidual b theta h hTruth hSeed n omega‖})
      atTop (nhds 0) by
        rw [hfun]
        exact hrow)

/-- Exact common-space likelihood decomposition. -/
theorem mixedPolynomialCommonCompleteLogLikelihood_exact
    (b theta h : Fin 3 → ℝ)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (n : ℕ)
    (omega : MixedPolynomialScalarLANCommonOmega b theta h hTruth hSeed) :
    mixedPolynomialCommonCompleteLogLikelihood b theta h hTruth hSeed n omega =
      mixedPolynomialCommonTotalScaleFinalScore b theta h hTruth hSeed n omega -
        mixedPolynomialTruthFrameDirectionalInformation theta h b / 2 +
      mixedPolynomialCommonResidual b theta h hTruth hSeed n omega := by
  calc
    mixedPolynomialCommonCompleteLogLikelihood b theta h hTruth hSeed n omega =
        mixedPolynomialTotalScaleFinalLinearScore theta h b n (omega n) -
          mixedPolynomialTruthFrameDirectionalInformation theta h b / 2 +
        mixedPolynomialCommonResidual b theta h hTruth hSeed n omega := by
      exact mixedPolynomialTotalScaleCompleteLogLikelihood_exact
        theta h b n (omega n)
    _ = mixedPolynomialCommonTotalScaleFinalScore b theta h hTruth hSeed n omega -
          mixedPolynomialTruthFrameDirectionalInformation theta h b / 2 +
        mixedPolynomialCommonResidual b theta h hTruth hSeed n omega := by
      rw [mixedPolynomialCommonTotalScaleFinalScore_eq_rowScore]

/-- Shifted common score used in the LAN expansion. -/
def mixedPolynomialCommonShiftedFinalScore
    (b theta h : Fin 3 → ℝ)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (n : ℕ)
    (omega : MixedPolynomialScalarLANCommonOmega b theta h hTruth hSeed) : ℝ :=
  mixedPolynomialCommonTotalScaleFinalScore b theta h hTruth hSeed n omega -
    mixedPolynomialTruthFrameDirectionalInformation theta h b / 2

/-- Scalar LAN for the complete concrete two-stage likelihood. -/
def MixedPolynomialConcreteScalarLAN
    (b theta h : Fin 3 → ℝ)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) : Prop :=
  TendstoInDistribution
    (mixedPolynomialCommonCompleteLogLikelihood b theta h hTruth hSeed)
    atTop
    (fun z : ℝ ↦
      z - mixedPolynomialTruthFrameDirectionalInformation theta h b / 2)
    (fun _ ↦ mixedPolynomialScalarLANCommonMeasure
      b theta h hTruth hSeed)
    (gaussianReal 0
      (mixedPolynomialTruthFrameDirectionalInformation theta h b).toNNReal)

/-- Complete scalar LAN, conditional only on the finite-pilot Hoeffding
contract. -/
theorem mixedPolynomialConcreteScalarLAN_of_hoeffding
    (b theta h : Fin 3 → ℝ)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hHoeffding : MixedPolynomialFinitePilotHoeffdingContracts theta
      (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)) :
    MixedPolynomialConcreteScalarLAN b theta h hTruth hSeed := by
  have hscore := mixedPolynomialCommonTotalScaleFinalScore_CLT
    b theta h hTruth hSeed hHoeffding
  have hshift : TendstoInDistribution
      (mixedPolynomialCommonShiftedFinalScore b theta h hTruth hSeed)
      atTop
      (fun z : ℝ ↦
        z - mixedPolynomialTruthFrameDirectionalInformation theta h b / 2)
      (fun _ ↦ mixedPolynomialScalarLANCommonMeasure
        b theta h hTruth hSeed)
      (gaussianReal 0
        (mixedPolynomialTruthFrameDirectionalInformation theta h b).toNNReal) := by
    change TendstoInDistribution
      (fun n x ↦
        mixedPolynomialCommonTotalScaleFinalScore b theta h hTruth hSeed n x -
          mixedPolynomialTruthFrameDirectionalInformation theta h b / 2)
      atTop
      (fun z : ℝ ↦
        z - mixedPolynomialTruthFrameDirectionalInformation theta h b / 2)
      (fun _ ↦ mixedPolynomialScalarLANCommonMeasure b theta h hTruth hSeed)
      (gaussianReal 0
        (mixedPolynomialTruthFrameDirectionalInformation theta h b).toNNReal)
    simpa [Function.comp_def] using
      (hscore.continuous_comp
        (g := fun z : ℝ ↦
          z - mixedPolynomialTruthFrameDirectionalInformation theta h b / 2)
        (by fun_prop))
  have hresidual := mixedPolynomialCommonResidual_tendstoInMeasure_zero
    b theta h hTruth hSeed hHoeffding
  have hdiff : TendstoInMeasure
      (mixedPolynomialScalarLANCommonMeasure b theta h hTruth hSeed)
      ((fun n ↦
          mixedPolynomialCommonCompleteLogLikelihood
            b theta h hTruth hSeed n) -
        (fun n ↦
          mixedPolynomialCommonShiftedFinalScore
            b theta h hTruth hSeed n))
      atTop 0 := by
    have hfun :
        ((fun n ↦
            mixedPolynomialCommonCompleteLogLikelihood
              b theta h hTruth hSeed n) -
          (fun n ↦
            mixedPolynomialCommonShiftedFinalScore
              b theta h hTruth hSeed n)) =
      mixedPolynomialCommonResidual b theta h hTruth hSeed := by
      funext n omega
      change mixedPolynomialCommonCompleteLogLikelihood
          b theta h hTruth hSeed n omega -
        mixedPolynomialCommonShiftedFinalScore
          b theta h hTruth hSeed n omega =
        mixedPolynomialCommonResidual b theta h hTruth hSeed n omega
      rw [mixedPolynomialCommonCompleteLogLikelihood_exact]
      unfold mixedPolynomialCommonShiftedFinalScore
      ring
    rw [hfun]
    exact hresidual
  unfold MixedPolynomialConcreteScalarLAN
  exact tendstoInDistribution_of_tendstoInMeasure_sub
    (mixedPolynomialCommonCompleteLogLikelihood b theta h hTruth hSeed)
    (fun z : ℝ ↦
      z - mixedPolynomialTruthFrameDirectionalInformation theta h b / 2)
    hshift hdiff
    (fun n ↦ by
      exact ((measurable_of_finite
        (mixedPolynomialScalarLANRowCompleteLogLikelihood
          b theta h hTruth hSeed n)).comp
          (MixedExactCycleScalarTriangularArrayData.rowCoordinate_measurable
            (mixedPolynomialScalarLANArray b theta h hTruth hSeed)
            mixedPolynomialHallHeydeRowSize n)).aemeasurable)

/-- Fully concrete scalar LAN endpoint: Mathlib discharges Hoeffding, so the
only external scientific atom remaining transitively is Hall--Heyde. -/
theorem mixedPolynomialConcreteScalarLAN_mathlib
    (b theta h : Fin 3 → ℝ)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    MixedPolynomialConcreteScalarLAN b theta h hTruth hSeed :=
  mixedPolynomialConcreteScalarLAN_of_hoeffding b theta h hTruth hSeed
    (mixedPolynomialFinitePilotHoeffdingContracts_mathlib theta
      (mixedNonzeroInterior_pauliPilotPhysical theta hTruth))

/-- The LAN limit law is the ordinary real Gaussian `N(-I/2, I)`. -/
theorem mixedPolynomialConcreteScalarLAN_limitLaw_eq_gaussian
    (theta h b : Fin 3 → ℝ) :
    (gaussianReal 0
      (mixedPolynomialTruthFrameDirectionalInformation theta h b).toNNReal).map
        (fun z : ℝ ↦
          z - mixedPolynomialTruthFrameDirectionalInformation theta h b / 2) =
      gaussianReal
        (-mixedPolynomialTruthFrameDirectionalInformation theta h b / 2)
        (mixedPolynomialTruthFrameDirectionalInformation theta h b).toNNReal := by
  simpa [neg_div] using
    (gaussianReal_map_sub_const
      (μ := (0 : ℝ))
      (v := (mixedPolynomialTruthFrameDirectionalInformation
        theta h b).toNNReal)
      (mixedPolynomialTruthFrameDirectionalInformation theta h b / 2))

end

end QubitOracle.Paper
