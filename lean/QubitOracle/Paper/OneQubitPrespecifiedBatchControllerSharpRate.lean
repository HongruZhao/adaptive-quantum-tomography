import QubitOracle.Paper.OneQubitPrespecifiedBatchCumulativeInformationClosure
import QubitOracle.Paper.OneQubitMixedGoodBranchUniformFrame
import QubitOracle.Paper.OneQubitPrespecifiedBatchFinalEstimatorBridge

/-!
# Sharp controller-information rate for exact prespecified qubit batches

This file strengthens qualitative controller-information convergence to a
quantitative rate.  The proof has no protocol or scientific premise:

* the concrete Gram--Schmidt frame-information map is differentiable at every
  nonzero interior truth with a nonparallel seed, hence locally Lipschitz;
* the literal Pauli pilot has exact mean-square error of order `q_k^{-1}`;
* the safeguarded branch has probability at most `12 / (q_k * delta^2)` by
  the already-kernel-proved finite Born Hoeffding theorem;
* polynomial schedule arithmetic then converts the row bounds into the
  cumulative rate required by the Newton defect.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory Set Matrix
open scoped BigOperators ENNReal Topology Matrix
open OneQubitPredeterminedBatchHeadline
open PureMultilevelSequentialBatchAdaptive

noncomputable section

attribute [local instance]
  pauliPilotBornPathMeasurableSpace
  mixedTwoStageFiniteRowMeasurableSpace
  mixedTwoStageFiniteRowMeasurableSingletonClass

/-! ## Concrete differentiability and local Lipschitz control -/

@[fun_prop] theorem localNormalizedBlochDirection_differentiableAt
    (theta : RLSVector 3) (hTheta : 0 < QubitOracle.blochNormSq theta) :
    DifferentiableAt Real localNormalizedBlochDirection theta := by
  rw [differentiableAt_pi]
  intro i
  unfold localNormalizedBlochDirection QubitOracle.blochNormSq
  fun_prop (disch := positivity)

@[fun_prop] theorem localFrameFirstResidual_differentiableAt
    (theta b : RLSVector 3) (hTheta : 0 < QubitOracle.blochNormSq theta) :
    DifferentiableAt Real (localFrameFirstResidual b) theta := by
  have hnormalized :=
    localNormalizedBlochDirection_differentiableAt theta hTheta
  have hdot : DifferentiableAt Real
      (fun x => QubitOracle.blochDot b (localNormalizedBlochDirection x))
      theta := by
    unfold QubitOracle.blochDot
    fun_prop
      (disch := exact differentiableAt_pi.mp hnormalized _)
  rw [differentiableAt_pi]
  intro i
  unfold localFrameFirstResidual
  fun_prop
    (disch := first
      | exact hdot
      | exact differentiableAt_pi.mp hnormalized _)

@[fun_prop] theorem localFrameFirstTangent_differentiableAt
    (theta b : RLSVector 3)
    (hTheta : 0 < QubitOracle.blochNormSq theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    DifferentiableAt Real (localFrameFirstTangent b) theta := by
  have hresidual := localFrameFirstResidual_differentiableAt theta b hTheta
  have hnormalized := localNormalizedBlochDirection_differentiableAt
    (localFrameFirstResidual b theta) hSeed
  simpa [localFrameFirstTangent, Function.comp_def] using
    hnormalized.comp theta hresidual

@[fun_prop] theorem localFrameSecondTangent_differentiableAt
    (theta b : RLSVector 3)
    (hTheta : 0 < QubitOracle.blochNormSq theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    DifferentiableAt Real (localFrameSecondTangent b) theta := by
  have hnormalized :=
    localNormalizedBlochDirection_differentiableAt theta hTheta
  have htangent := localFrameFirstTangent_differentiableAt
    theta b hTheta hSeed
  rw [differentiableAt_pi]
  intro i
  fin_cases i <;>
    simp [localFrameSecondTangent, qubitCrossProduct] <;>
    fun_prop
      (disch := first
        | exact differentiableAt_pi.mp hnormalized _
        | exact differentiableAt_pi.mp htangent _)

@[fun_prop] theorem localContinuousQubitFrame_entry_differentiableAt
    (theta b : RLSVector 3)
    (hTheta : 0 < QubitOracle.blochNormSq theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) (i k : Fin 3) :
    DifferentiableAt Real
      (fun x => localContinuousQubitFrame b x i k) theta := by
  have hnormalized :=
    localNormalizedBlochDirection_differentiableAt theta hTheta
  have hfirst := localFrameFirstTangent_differentiableAt
    theta b hTheta hSeed
  have hsecond := localFrameSecondTangent_differentiableAt
    theta b hTheta hSeed
  fin_cases k
  · simpa [localContinuousQubitFrame] using
      differentiableAt_pi.mp hfirst i
  · simpa [localContinuousQubitFrame] using
      differentiableAt_pi.mp hsecond i
  · simpa [localContinuousQubitFrame] using
      differentiableAt_pi.mp hnormalized i

/-- The exact fixed-truth directional Fisher information is differentiable
as a function of the concrete Gram--Schmidt controller. -/
theorem mixedFrameDirectionalInformation_differentiableAt_truth
    (theta h b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    DifferentiableAt Real
      (fun x => mixedPolynomialFrameDirectionalInformation theta h
        (localContinuousQubitFrame b x)) theta := by
  have hden (k : Fin 3) :
      1 - (QubitOracle.blochDot theta
          (mixedTwoStageFrameAxis
          (localContinuousQubitFrame b theta) k)) ^ 2 ≠ 0 := by
    apply ne_of_gt
    apply mixedTwoStageAxisFisherDenominator_pos theta _ hTruth.2
    change QubitOracle.blochNormSq
      (qubitFrameAxis (localContinuousQubitFrame b theta) k) = 1
    exact localContinuousQubitFrame_axis_unit
      ⟨hTruth.1, hSeed⟩ k
  unfold mixedPolynomialFrameDirectionalInformation
    mixedTwoStageFrameAxis QubitOracle.blochDot
  fun_prop
    (disch := first
      | exact hTruth.1
      | exact hSeed
      | exact hden _
      | exact localContinuousQubitFrame_entry_differentiableAt
          theta b hTruth.1 hSeed _ _)

/-- Local quantitative controller certificate.  Both the safeguarded-domain
membership and the Lipschitz constant are derived from the concrete formulas. -/
theorem exactControllerInformation_exists_localLipschitz
    (theta h b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    ∃ C : Real, 0 < C ∧ ∃ delta : Real, 0 < delta ∧
      ∀ x : RLSVector 3, ‖x - theta‖ < delta →
        LocalContinuousFrameDomain b x ∧
        |mixedPolynomialFrameDirectionalInformation theta h
              (mixedPilotSelectedLocalFrame b x) -
            mixedPolynomialTruthFrameDirectionalInformation theta h b| <=
          C * ‖x - theta‖ := by
  let F : RLSVector 3 -> Real := fun x =>
    mixedPolynomialFrameDirectionalInformation theta h
      (localContinuousQubitFrame b x)
  have hdiff : DifferentiableAt Real F theta :=
    mixedFrameDirectionalInformation_differentiableAt_truth
      theta h b hTruth hSeed
  obtain ⟨C, hC, hbig⟩ := hdiff.isBigO_sub.exists_pos
  have hlip : ∀ᶠ x in nhds theta,
      ‖F x - F theta‖ <= C * ‖x - theta‖ := hbig.bound
  have hradial : ∀ᶠ x in nhds theta,
      0 < QubitOracle.blochNormSq x := by
    have hc : Continuous
        (fun x : RLSVector 3 => QubitOracle.blochNormSq x) := by
      unfold QubitOracle.blochNormSq
      apply continuous_finsetSum
      intro i hi
      fun_prop
    exact hc.continuousAt (Ioi_mem_nhds hTruth.1)
  have hresidual : ∀ᶠ x in nhds theta,
      0 < QubitOracle.blochNormSq (localFrameFirstResidual b x) := by
    have hr :=
      (localFrameFirstResidual_differentiableAt theta b hTruth.1).continuousAt
    have hnorm : Continuous
        (fun x : RLSVector 3 => QubitOracle.blochNormSq x) := by
      unfold QubitOracle.blochNormSq
      apply continuous_finsetSum
      intro i hi
      fun_prop
    have hc : ContinuousAt
        (fun x : RLSVector 3 =>
          QubitOracle.blochNormSq (localFrameFirstResidual b x)) theta := by
      simpa [Function.comp_def] using hnorm.continuousAt.comp hr
    exact hc (Ioi_mem_nhds hSeed)
  have hall : ∀ᶠ x in nhds theta,
      LocalContinuousFrameDomain b x ∧
        ‖F x - F theta‖ <= C * ‖x - theta‖ := by
    filter_upwards [hradial, hresidual, hlip] with x hx hrx hlx
    exact ⟨⟨hx, hrx⟩, hlx⟩
  rw [Metric.eventually_nhds_iff] at hall
  obtain ⟨delta, hdelta, hall⟩ := hall
  refine ⟨C, hC, delta, hdelta, ?_⟩
  intro x hx
  obtain ⟨hDomain, hbound⟩ := hall hx
  refine ⟨hDomain, ?_⟩
  simpa [F, mixedPilotSelectedLocalFrame, hDomain,
    mixedPolynomialTruthFrameDirectionalInformation,
    Real.norm_eq_abs] using hbound

/-! ## Finite-dimensional norm and information envelopes -/

theorem rlsVector_norm_lt_of_coordinate_abs_lt
    (x y : RLSVector 3) (delta : Real) (hdelta : 0 < delta)
    (h : forall j, |x j - y j| < delta) :
    ‖x - y‖ < delta := by
  rw [Pi.norm_def]
  change (↑(Finset.univ.sup fun j => ‖(x - y) j‖₊) : Real) <
    (↑(⟨delta, hdelta.le⟩ : NNReal) : Real)
  apply NNReal.coe_lt_coe.mpr
  rw [Finset.sup_lt_iff
    (show (⊥ : NNReal) < ⟨delta, hdelta.le⟩ by exact_mod_cast hdelta)]
  intro j hj
  apply NNReal.coe_lt_coe.mp
  change |x j - y j| < (↑(⟨delta, hdelta.le⟩ : NNReal) : Real)
  convert h j using 1

theorem rlsVector_norm_sq_le_blochNormSq (x : RLSVector 3) :
    ‖x‖ ^ 2 <= QubitOracle.blochNormSq x := by
  have hB : 0 <= QubitOracle.blochNormSq x := by
    unfold QubitOracle.blochNormSq
    positivity
  have hcoordinate (j : Fin 3) :
      ‖x j‖ <= Real.sqrt (QubitOracle.blochNormSq x) := by
    rw [← sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)]
    rw [Real.sq_sqrt hB]
    unfold QubitOracle.blochNormSq
    rw [Real.norm_eq_abs, sq_abs]
    exact Finset.single_le_sum
      (fun k _ => sq_nonneg (x k)) (Finset.mem_univ j)
  let S : NNReal :=
    ⟨Real.sqrt (QubitOracle.blochNormSq x), Real.sqrt_nonneg _⟩
  have hnorm : ‖x‖ <= Real.sqrt (QubitOracle.blochNormSq x) := by
    rw [Pi.norm_def]
    change (↑(Finset.univ.sup fun j => ‖x j‖₊) : Real) <= (↑S : Real)
    apply NNReal.coe_le_coe.mpr
    rw [Finset.sup_le_iff]
    intro j hj
    apply NNReal.coe_le_coe.mp
    change ‖x j‖ <= (↑S : Real)
    convert hcoordinate j using 1
    rfl
  nlinarith [Real.sq_sqrt hB, norm_nonneg x,
    Real.sqrt_nonneg (QubitOracle.blochNormSq x)]

private theorem directionalFisherTerm_nonnegative_and_le_sharp
    (theta h axis : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (haxis : QubitOracle.blochNormSq axis = 1) :
    0 <= QubitOracle.blochDot h axis ^ 2 /
        (1 - QubitOracle.blochDot theta axis ^ 2) ∧
      QubitOracle.blochDot h axis ^ 2 /
          (1 - QubitOracle.blochDot theta axis ^ 2) <=
        QubitOracle.blochNormSq h /
          exactConcreteMixedInformationGap theta := by
  let gamma := exactConcreteMixedInformationGap theta
  have hgamma : 0 < gamma := exactConcreteMixedInformationGap_pos theta hTruth
  have htheta : QubitOracle.blochNormSq theta <= 1 - gamma := by
    simp [gamma, exactConcreteMixedInformationGap]
  have hden := mixedAxis_denominator_ge_of_normSq_le
    theta axis gamma htheta haxis
  have hdenpos : 0 < 1 - QubitOracle.blochDot theta axis ^ 2 :=
    hgamma.trans_le hden
  have hnum := blochDot_sq_le_normSq_mul_normSq h axis
  rw [haxis, mul_one] at hnum
  have hnorm : 0 <= QubitOracle.blochNormSq h := by
    unfold QubitOracle.blochNormSq
    positivity
  have hC : 0 <= QubitOracle.blochNormSq h / gamma :=
    div_nonneg hnorm hgamma.le
  constructor
  · exact div_nonneg (sq_nonneg _) hdenpos.le
  · rw [div_le_iff₀ hdenpos]
    calc
      QubitOracle.blochDot h axis ^ 2 <= QubitOracle.blochNormSq h := hnum
      _ = (QubitOracle.blochNormSq h / gamma) * gamma := by
        field_simp [hgamma.ne']
      _ <= (QubitOracle.blochNormSq h / gamma) *
          (1 - QubitOracle.blochDot theta axis ^ 2) :=
        mul_le_mul_of_nonneg_left hden hC

theorem mixedPolynomialFrameDirectionalInformation_nonnegative_and_le_sharp
    (theta h : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (R : Matrix (Fin 3) (Fin 3) Real)
    (haxis : forall k, QubitOracle.blochNormSq
      (mixedTwoStageFrameAxis R k) = 1) :
    0 <= mixedPolynomialFrameDirectionalInformation theta h R ∧
      mixedPolynomialFrameDirectionalInformation theta h R <=
        QubitOracle.blochNormSq h /
          exactConcreteMixedInformationGap theta := by
  let U := QubitOracle.blochNormSq h /
    exactConcreteMixedInformationGap theta
  have hterm : forall k : Fin 3,
      0 <= QubitOracle.blochDot h (mixedTwoStageFrameAxis R k) ^ 2 /
          (1 - QubitOracle.blochDot theta
            (mixedTwoStageFrameAxis R k) ^ 2) ∧
      QubitOracle.blochDot h (mixedTwoStageFrameAxis R k) ^ 2 /
          (1 - QubitOracle.blochDot theta
            (mixedTwoStageFrameAxis R k) ^ 2) <= U := by
    intro k
    exact directionalFisherTerm_nonnegative_and_le_sharp
      theta h _ hTruth (haxis k)
  constructor
  · unfold mixedPolynomialFrameDirectionalInformation
    exact mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun k _ => (hterm k).1)
  · unfold mixedPolynomialFrameDirectionalInformation
    calc
      (1 / 3 : Real) * ∑ k : Fin 3,
          QubitOracle.blochDot h (mixedTwoStageFrameAxis R k) ^ 2 /
            (1 - QubitOracle.blochDot theta
              (mixedTwoStageFrameAxis R k) ^ 2) <=
        (1 / 3 : Real) * ∑ _k : Fin 3, U :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun k _ => (hterm k).2) (by norm_num)
      _ = U := by simp [Fin.sum_univ_succ]

theorem mixedPolynomialTruthFrameDirectionalInformation_nonnegative_and_le_sharp
    (theta h b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    0 <= mixedPolynomialTruthFrameDirectionalInformation theta h b ∧
      mixedPolynomialTruthFrameDirectionalInformation theta h b <=
        QubitOracle.blochNormSq h /
          exactConcreteMixedInformationGap theta := by
  unfold mixedPolynomialTruthFrameDirectionalInformation
  apply mixedPolynomialFrameDirectionalInformation_nonnegative_and_le_sharp
    theta h hTruth
  intro k
  change QubitOracle.blochNormSq
    (qubitFrameAxis (localContinuousQubitFrame b theta) k) = 1
  exact localContinuousQubitFrame_axis_unit ⟨hTruth.1, hSeed⟩ k

/-! ## Exact finite-row second-moment certificate -/

def exactConcreteControllerDirectionalRowError
    (theta h b : RLSVector 3) (k : Nat)
    (pilot : PauliPilotPath (exactConcreteBatchPilotBlocks k)) : Real :=
  exactCumulativeBatchFrameDirectionalInformation theta h b k pilot -
    mixedPolynomialTruthFrameDirectionalInformation theta h b

def exactConcreteControllerPilotCubeBadEvent
    (theta : RLSVector 3) (k : Nat) (delta : Real) :
    Set (PauliPilotPath (exactConcreteBatchPilotBlocks k)) :=
  {pilot | exists j : Fin 3,
    delta <= |pauliPilotEstimate pilot j - theta j|}

private theorem pauliPilotFiniteExpectation_mono_sharp
    {q : Nat} (theta : RLSVector 3)
    (hphysical : PauliPilotPhysicalBloch theta)
    {f g : PauliPilotPath q -> Real}
    (hfg : forall path, f path <= g path) :
    pauliPilotFiniteExpectation theta f <=
      pauliPilotFiniteExpectation theta g := by
  unfold pauliPilotFiniteExpectation
  exact Finset.sum_le_sum fun path _ =>
    mul_le_mul_of_nonneg_left (hfg path)
      (pauliPilotPathMass_nonnegative theta hphysical path)

theorem pauliPilotFiniteExpectation_indicator_eq_measureReal
    {q : Nat} (theta : RLSVector 3)
    (hphysical : PauliPilotPhysicalBloch theta)
    (event : Set (PauliPilotPath q)) :
    pauliPilotFiniteExpectation theta (event.indicator (fun _ => 1)) =
      (pauliPilotBornProductMeasure theta event).toReal := by
  classical
  rw [pauliPilotBornProductMeasure_apply theta hphysical]
  rw [ENNReal.toReal_ofReal]
  · unfold pauliPilotFiniteExpectation
    apply Finset.sum_congr rfl
    intro pilot hpilot
    by_cases hmem : pilot ∈ event <;> simp [Set.indicator, hmem]
  · apply Finset.sum_nonneg
    intro pilot hpilot
    by_cases hmem : pilot ∈ event
    · simp [hmem, pauliPilotPathMass_nonnegative theta hphysical pilot]
    · simp [hmem]

theorem exactConcreteControllerPilotCubeBadEvent_measure_le
    (theta : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (k : Nat) (delta : Real) (hdelta : 0 < delta) :
    pauliPilotBornProductMeasure theta
        (exactConcreteControllerPilotCubeBadEvent theta k delta) <=
      pauliPilotFiniteHoeffdingEnvelope
        (exactConcreteBatchPilotIndex k) delta := by
  let q := exactConcreteBatchPilotBlocks k
  let X : Nat -> PauliPilotPath q -> RLSVector 3 :=
    fun _ pilot => pauliPilotEstimate pilot
  have hcoordinate (j : Fin 3) :
      pauliPilotBornProductMeasure theta
          {pilot : PauliPilotPath q |
            delta <= |pauliPilotEstimate pilot j - theta j|} <=
        pauliPilotCoordinateHoeffdingEnvelope
          (exactConcreteBatchPilotIndex k) delta := by
    have hHoeffding :
        PauliPilotBornTwoSidedHoeffdingTheorem2Contract
          (exactConcreteBatchPilotBlocks_pos k) theta hphysical j :=
      ⟨hoeffding1963UniversalTheorem2_of_mathlib _ _ _ _,
        hoeffding1963UniversalTheorem2_of_mathlib _ _ _ _⟩
    have hfinite := pauliPilotBorn_twoSidedTail_of_hoeffding2
      (exactConcreteBatchPilotBlocks_pos k) theta hphysical j
      hHoeffding delta hdelta
    unfold pauliPilotCoordinateHoeffdingEnvelope
    have hcast :
        ((Nat.succ (exactConcreteBatchPilotIndex k) : Nat) : Real) =
          (exactConcreteBatchPilotBlocks k : Real) := by
      exact_mod_cast exactConcreteBatchPilotIndex_succ k
    rw [hcast]
    convert hfinite using 1 <;> simp <;> ring
  calc
    pauliPilotBornProductMeasure theta
        (exactConcreteControllerPilotCubeBadEvent theta k delta) <=
      ∑ j : Fin 3, pauliPilotBornProductMeasure theta
        {pilot : PauliPilotPath q |
          delta <= |pauliPilotEstimate pilot j - theta j|} := by
      change pauliPilotBornProductMeasure theta
        (QubitOracle.coordinateDeltaBadEvent X theta 0 delta) <= _
      exact QubitOracle.measure_coordinateDeltaBadEvent_le_finset_sum
        (pauliPilotBornProductMeasure theta) X theta 0 delta
    _ <= ∑ _j : Fin 3,
        pauliPilotCoordinateHoeffdingEnvelope
          (exactConcreteBatchPilotIndex k) delta :=
      Finset.sum_le_sum fun j _ => hcoordinate j
    _ = pauliPilotFiniteHoeffdingEnvelope
        (exactConcreteBatchPilotIndex k) delta := by
      simp [pauliPilotFiniteHoeffdingEnvelope]

theorem exactConcreteControllerPilotCubeBadEvent_measureReal_le
    (theta : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (k : Nat) (delta : Real) (hdelta : 0 < delta) :
    (pauliPilotBornProductMeasure theta
      (exactConcreteControllerPilotCubeBadEvent theta k delta)).toReal <=
      12 / ((exactConcreteBatchPilotBlocks k : Real) * delta ^ 2) := by
  have htail := exactConcreteControllerPilotCubeBadEvent_measure_le
    theta hphysical k delta hdelta
  have hmeasureTop :
      pauliPilotBornProductMeasure theta
          (exactConcreteControllerPilotCubeBadEvent theta k delta) ≠ ∞ :=
    ne_top_of_le_ne_top (by
      rw [pauliPilotBornProductMeasure_univ theta hphysical]
      norm_num)
      (measure_mono (Set.subset_univ
        (exactConcreteControllerPilotCubeBadEvent theta k delta)))
  have henvelopeTop :
      pauliPilotFiniteHoeffdingEnvelope
        (exactConcreteBatchPilotIndex k) delta ≠ ∞ := by
    unfold pauliPilotFiniteHoeffdingEnvelope
      pauliPilotCoordinateHoeffdingEnvelope
    exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.mul_ne_top (by norm_num) (by simp))
  have hreal :=
    (ENNReal.toReal_le_toReal hmeasureTop henvelopeTop).2 htail
  have hqpos : (0 : Real) < exactConcreteBatchPilotBlocks k := by
    exact_mod_cast exactConcreteBatchPilotBlocks_pos k
  let y : Real :=
    (exactConcreteBatchPilotBlocks k : Real) * delta ^ 2 / 2
  have hy : 0 < y := by
    dsimp [y]
    positivity
  have hexp : Real.exp (-y) <= 1 / y := by
    rw [le_div_iff₀ hy]
    simpa [mul_comm] using
      (Real.mul_exp_neg_le_exp_neg_one y).trans
        (Real.exp_le_one_iff.mpr (by norm_num))
  have hcast :
      ((Nat.succ (exactConcreteBatchPilotIndex k) : Nat) : Real) =
        (exactConcreteBatchPilotBlocks k : Real) := by
    exact_mod_cast exactConcreteBatchPilotIndex_succ k
  simp only [pauliPilotFiniteHoeffdingEnvelope,
    pauliPilotCoordinateHoeffdingEnvelope, ENNReal.toReal_mul,
    ENNReal.toReal_ofNat, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    hcast] at hreal
  calc
    (pauliPilotBornProductMeasure theta
      (exactConcreteControllerPilotCubeBadEvent theta k delta)).toReal <=
        6 * Real.exp (-y) := by
      dsimp [y]
      nlinarith [hreal]
    _ <= 6 * (1 / y) :=
      mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ = 12 / ((exactConcreteBatchPilotBlocks k : Real) * delta ^ 2) := by
      dsimp [y]
      field_simp
      ring

/-- A concrete row-level `L2` certificate.  The constant is independent of
the row and the bound uses the literal cubic pilot size. -/
theorem exactConcreteControllerDirectionalRowError_exists_l2_constant
    (theta h b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    ∃ A : Real, 0 < A ∧ ∀ k : Nat,
      pauliPilotFiniteExpectation theta
        (fun pilot : PauliPilotPath (exactConcreteBatchPilotBlocks k) =>
          exactConcreteControllerDirectionalRowError
            theta h b k pilot ^ 2) <=
        A / (exactConcreteBatchPilotBlocks k : Real) := by
  obtain ⟨C, hC, delta, hdelta, hlocal⟩ :=
    exactControllerInformation_exists_localLipschitz
      theta h b hTruth hSeed
  let U := QubitOracle.blochNormSq h /
    exactConcreteMixedInformationGap theta
  let A := 3 * C ^ 2 + 48 * U ^ 2 / delta ^ 2
  have hU : 0 <= U := by
    exact div_nonneg (by
      unfold QubitOracle.blochNormSq
      positivity) (exactConcreteMixedInformationGap_pos theta hTruth).le
  have hA : 0 < A := by
    dsimp [A]
    have : 0 < 3 * C ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos hC)
    positivity
  refine ⟨A, hA, ?_⟩
  intro k
  let bad := exactConcreteControllerPilotCubeBadEvent theta k delta
  have hphysical := mixedNonzeroInterior_pauliPilotPhysical theta hTruth
  have htruth :=
    mixedPolynomialTruthFrameDirectionalInformation_nonnegative_and_le_sharp
      theta h b hTruth hSeed
  have hpointwise (pilot : PauliPilotPath
      (exactConcreteBatchPilotBlocks k)) :
      exactConcreteControllerDirectionalRowError theta h b k pilot ^ 2 <=
        C ^ 2 * QubitOracle.blochNormSq
          (mixedPauliCoordinateError theta pilot) +
        4 * U ^ 2 * bad.indicator (fun _ => 1) pilot := by
    by_cases hbad : pilot ∈ bad
    · have hrow :=
        exactCumulativeBatchFrameDirectionalInformation_nonnegative_and_le
          theta h b hTruth k pilot
      have habs :
          |exactConcreteControllerDirectionalRowError theta h b k pilot| <=
            2 * U := by
        unfold exactConcreteControllerDirectionalRowError
        calc
          |exactCumulativeBatchFrameDirectionalInformation theta h b k pilot -
              mixedPolynomialTruthFrameDirectionalInformation theta h b| ≤
            |exactCumulativeBatchFrameDirectionalInformation theta h b k pilot| +
              |mixedPolynomialTruthFrameDirectionalInformation theta h b| :=
                abs_sub _ _
          _ =
            exactCumulativeBatchFrameDirectionalInformation theta h b k pilot +
              mixedPolynomialTruthFrameDirectionalInformation theta h b := by
                rw [abs_of_nonneg hrow.1, abs_of_nonneg htruth.1]
          _ <= 2 * U := by
            dsimp [U]
            linarith [hrow.2, htruth.2]
      have hsquare :
          exactConcreteControllerDirectionalRowError theta h b k pilot ^ 2 <=
            (2 * U) ^ 2 := by
        rw [← sq_abs]
        exact (sq_le_sq₀ (abs_nonneg _)
          (mul_nonneg (by norm_num) hU)).2 habs
      rw [Set.indicator_of_mem hbad]
      simp only [mul_one]
      have hnonnegative :
          0 <= C ^ 2 * QubitOracle.blochNormSq
            (mixedPauliCoordinateError theta pilot) := by
        apply mul_nonneg (sq_nonneg C)
        unfold QubitOracle.blochNormSq
        positivity
      nlinarith [hsquare]
    · have hcoordinate : forall j : Fin 3,
          |pauliPilotEstimate pilot j - theta j| < delta := by
        intro j
        by_contra hj
        apply hbad
        exact ⟨j, le_of_not_gt hj⟩
      have hnorm :
          ‖pauliPilotEstimate pilot - theta‖ < delta :=
        rlsVector_norm_lt_of_coordinate_abs_lt
          (pauliPilotEstimate pilot) theta delta hdelta hcoordinate
      have hlip := (hlocal (pauliPilotEstimate pilot) hnorm).2
      have herror :
          |exactConcreteControllerDirectionalRowError theta h b k pilot| <=
            C * ‖mixedPauliCoordinateError theta pilot‖ := by
        have herrEq : mixedPauliCoordinateError theta pilot =
            pauliPilotEstimate pilot - theta := by
          rfl
        rw [herrEq]
        simpa [exactConcreteControllerDirectionalRowError,
          exactCumulativeBatchFrameDirectionalInformation] using hlip
      have hsquare :
          exactConcreteControllerDirectionalRowError theta h b k pilot ^ 2 <=
            C ^ 2 * ‖mixedPauliCoordinateError theta pilot‖ ^ 2 := by
        rw [← sq_abs]
        have hsquareBase := (sq_le_sq₀ (abs_nonneg _)
          (mul_nonneg hC.le (norm_nonneg _))).2 herror
        nlinarith
      simp only [Set.indicator, hbad, if_false, mul_zero, add_zero]
      exact hsquare.trans (mul_le_mul_of_nonneg_left
        (rlsVector_norm_sq_le_blochNormSq
          (mixedPauliCoordinateError theta pilot)) (sq_nonneg C))
  calc
    pauliPilotFiniteExpectation theta
        (fun pilot : PauliPilotPath (exactConcreteBatchPilotBlocks k) =>
          exactConcreteControllerDirectionalRowError
            theta h b k pilot ^ 2) <=
      pauliPilotFiniteExpectation theta
        (fun pilot => C ^ 2 * QubitOracle.blochNormSq
            (mixedPauliCoordinateError theta pilot) +
          4 * U ^ 2 * bad.indicator (fun _ => 1) pilot) :=
      pauliPilotFiniteExpectation_mono_sharp theta hphysical hpointwise
    _ = C ^ 2 * pauliPilotFiniteExpectation theta
          (fun pilot => QubitOracle.blochNormSq
            (mixedPauliCoordinateError theta pilot)) +
        4 * U ^ 2 * pauliPilotFiniteExpectation theta
          (bad.indicator (fun _ => 1)) := by
      rw [pauliPilotFiniteExpectation_add,
        pauliPilotFiniteExpectation_const_mul,
        pauliPilotFiniteExpectation_const_mul]
    _ <= C ^ 2 * (3 / (exactConcreteBatchPilotBlocks k : Real)) +
        4 * U ^ 2 *
          (12 / ((exactConcreteBatchPilotBlocks k : Real) * delta ^ 2)) := by
      gcongr
      · rw [pauliPilotCoordinateError_normSq_mean
          (exactConcreteBatchPilotBlocks_pos k) theta]
        have hcoord := pauliPilotPhysicalBloch_coordinate_bounds theta hphysical
        have hqpos : (0 : Real) < exactConcreteBatchPilotBlocks k := by
          exact_mod_cast exactConcreteBatchPilotBlocks_pos k
        have hsum : ∑ j : Fin 3, (1 - theta j ^ 2) <= 3 := by
          calc
            ∑ j : Fin 3, (1 - theta j ^ 2) <= ∑ _j : Fin 3, 1 := by
              apply Finset.sum_le_sum
              intro j hj
              nlinarith [sq_nonneg (theta j)]
            _ = 3 := by norm_num
        rw [← Finset.sum_div]
        exact div_le_div_of_nonneg_right hsum hqpos.le
      · rw [pauliPilotFiniteExpectation_indicator_eq_measureReal
          theta hphysical bad]
        exact exactConcreteControllerPilotCubeBadEvent_measureReal_le
          theta hphysical k delta hdelta
    _ = A / (exactConcreteBatchPilotBlocks k : Real) := by
      dsimp [A]
      have hqne : (exactConcreteBatchPilotBlocks k : Real) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (exactConcreteBatchPilotBlocks_pos k))
      have hdne : delta ≠ 0 := ne_of_gt hdelta
      field_simp [hqne, hdne]
      ring

/-! ## Weighted finite-prefix controller rate -/

/-- The exact selected-frame directional-information defect, weighted by the
number of final observations in each of the first `K` batches and normalized
by the total prespecified sample size. -/
def prespecifiedBatchFinitePrefixWeightedControllerDirectionalDefect
    (theta h b : RLSVector 3) (K : Nat)
    (omega : ExactConcretePredeterminedBatchPrefix K) : Real :=
  (prespecifiedBatchTotalObservations K : Real)⁻¹ *
    ∑ k : Fin K, (exactConcreteBatchExploitationSize k : Real) *
      exactConcreteControllerDirectionalRowError theta h b k
        (prespecifiedBatchPrefixPilot K k omega)

/-- The row `L2` certificate transports exactly from the finite Pauli law to
the native `K`-batch prefix law through the proved pilot marginal. -/
theorem prespecifiedBatchControllerDirectionalRowError_integral_sq_le
    (theta h b : RLSVector 3)
    (hphysical : PauliPilotPhysicalBloch theta)
    (A : Real)
    (hrow : ∀ k : Nat,
      pauliPilotFiniteExpectation theta
        (fun pilot : PauliPilotPath (exactConcreteBatchPilotBlocks k) =>
          exactConcreteControllerDirectionalRowError theta h b k pilot ^ 2) <=
        A / (exactConcreteBatchPilotBlocks k : Real))
    (K : Nat) (k : Fin K) :
    (∫ omega,
      exactConcreteControllerDirectionalRowError theta h b k
        (prespecifiedBatchPrefixPilot K k omega) ^ 2
      ∂prespecifiedBatchEstimatorPrefixMeasure theta b K) <=
      A / (exactConcreteBatchPilotBlocks k : Real) := by
  have hmap := prespecifiedBatchPrefixMeasure_map_pilot
    theta b hphysical K k
  have hIntegralMap := integral_map_of_stronglyMeasurable
    (μ := prespecifiedBatchEstimatorPrefixMeasure theta b K)
    (φ := prespecifiedBatchPrefixPilot K k)
    (f := fun pilot : PauliPilotPath (exactConcreteBatchPilotBlocks k) =>
      exactConcreteControllerDirectionalRowError theta h b k pilot ^ 2)
    Measurable.of_discrete StronglyMeasurable.of_discrete
  rw [hmap] at hIntegralMap
  rw [← hIntegralMap,
    integral_pauliPilotBornProductMeasure theta hphysical]
  simpa [pauliPilotFiniteExpectation] using hrow k

/-- A deliberately simple degree-five envelope for one exact exploitation
batch.  Its loose numerical constant keeps the later rate arithmetic
transparent. -/
theorem exactConcreteBatchExploitationSize_real_le_power_five (k : Nat) :
    (exactConcreteBatchExploitationSize k : Real) <=
      45927 * ((k : Real) + 1) ^ 5 := by
  have hnat : exactConcreteBatchExploitationSize k <=
      exactConcreteBatchSize k := by
    rw [exactConcreteBatchSize_eq_exploration_add_exploitation]
    omega
  have hcast : (exactConcreteBatchExploitationSize k : Real) <=
      (exactConcreteBatchSize k : Real) := by exact_mod_cast hnat
  apply hcast.trans
  unfold exactConcreteBatchSize
  push_cast
  ring_nf
  have hk0 : 0 <= (k : Real) := by positivity
  have hk2 : 0 <= (k : Real) ^ 2 := sq_nonneg _
  have hk3 : 0 <= (k : Real) ^ 3 := by positivity
  have hk4 : 0 <= (k : Real) ^ 4 := by positivity
  have hk5 : 0 <= (k : Real) ^ 5 := by positivity
  linarith

/-- Combining the degree-five final allocation with the exact cubic pilot
lower bound gives the deterministic degree-seven weighted row variance. -/
theorem exactConcreteBatchExploitation_sq_div_pilot_le_power_seven (k : Nat) :
    (exactConcreteBatchExploitationSize k : Real) ^ 2 /
        (exactConcreteBatchPilotBlocks k : Real) <=
      ((45927 : Real) ^ 2 / 27) * ((k : Real) + 1) ^ 7 := by
  let x : Real := (k : Real) + 1
  have hx : 0 < x := by dsimp [x]; positivity
  have he := exactConcreteBatchExploitationSize_real_le_power_five k
  have hq := exactConcreteBatchPilotBlocks_ge_twentySeven_cube k
  have hqpos : (0 : Real) < exactConcreteBatchPilotBlocks k := by
    exact_mod_cast exactConcreteBatchPilotBlocks_pos k
  have he0 : 0 <= (exactConcreteBatchExploitationSize k : Real) := by positivity
  have heUpper0 : 0 <= (45927 : Real) * x ^ 5 := by positivity
  have heSq : (exactConcreteBatchExploitationSize k : Real) ^ 2 <=
      ((45927 : Real) * x ^ 5) ^ 2 :=
    (sq_le_sq₀ he0 heUpper0).2 (by simpa [x] using he)
  apply (div_le_iff₀ hqpos).2
  calc
    (exactConcreteBatchExploitationSize k : Real) ^ 2 <=
        ((45927 : Real) * x ^ 5) ^ 2 := heSq
    _ = (((45927 : Real) ^ 2 / 27) * x ^ 7) *
        (27 * x ^ 3) := by ring
    _ <= (((45927 : Real) ^ 2 / 27) * x ^ 7) *
        (exactConcreteBatchPilotBlocks k : Real) := by
      apply mul_le_mul_of_nonneg_left (by simpa [x] using hq)
      positivity

/-- Pointwise Cauchy bound for the exact weighted controller defect. -/
theorem prespecifiedBatchFinitePrefixWeightedControllerDirectionalDefect_sq_le
    (theta h b : RLSVector 3) (K : Nat)
    (omega : ExactConcretePredeterminedBatchPrefix K) :
    prespecifiedBatchFinitePrefixWeightedControllerDirectionalDefect
        theta h b K omega ^ 2 <=
      (prespecifiedBatchTotalObservations K : Real)⁻¹ ^ 2 * (K : Real) *
        ∑ k : Fin K,
          ((exactConcreteBatchExploitationSize k : Real) *
            exactConcreteControllerDirectionalRowError theta h b k
              (prespecifiedBatchPrefixPilot K k omega)) ^ 2 := by
  have hCauchy := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (Fin K))
    (fun _k => (1 : Real))
    (fun k => (exactConcreteBatchExploitationSize k : Real) *
      exactConcreteControllerDirectionalRowError theta h b k
        (prespecifiedBatchPrefixPilot K k omega))
  unfold prespecifiedBatchFinitePrefixWeightedControllerDirectionalDefect
  calc
    ((prespecifiedBatchTotalObservations K : Real)⁻¹ *
        ∑ k : Fin K, (exactConcreteBatchExploitationSize k : Real) *
          exactConcreteControllerDirectionalRowError theta h b k
            (prespecifiedBatchPrefixPilot K k omega)) ^ 2 =
      (prespecifiedBatchTotalObservations K : Real)⁻¹ ^ 2 *
        (∑ k : Fin K, (1 : Real) *
          ((exactConcreteBatchExploitationSize k : Real) *
            exactConcreteControllerDirectionalRowError theta h b k
              (prespecifiedBatchPrefixPilot K k omega))) ^ 2 := by
        simp only [one_mul]
        ring
    _ <= (prespecifiedBatchTotalObservations K : Real)⁻¹ ^ 2 *
        ((∑ k : Fin K, (1 : Real) ^ 2) *
          ∑ k : Fin K,
            ((exactConcreteBatchExploitationSize k : Real) *
              exactConcreteControllerDirectionalRowError theta h b k
                (prespecifiedBatchPrefixPilot K k omega)) ^ 2) :=
      mul_le_mul_of_nonneg_left hCauchy (sq_nonneg _)
    _ = (prespecifiedBatchTotalObservations K : Real)⁻¹ ^ 2 * (K : Real) *
        ∑ k : Fin K,
          ((exactConcreteBatchExploitationSize k : Real) *
            exactConcreteControllerDirectionalRowError theta h b k
              (prespecifiedBatchPrefixPilot K k omega)) ^ 2 := by
      rw [show (∑ _k : Fin K, (1 : Real) ^ 2) = (K : Real) by simp]
      ring

/-- The concrete weighted selected-frame defect has mean square
`O(K^{-3})`.  Consequently its root-mean-square size is `O(K^{-3/2})`, which
is strictly smaller than the `K^{-5/4}` Newton-defect requirement. -/
theorem prespecifiedBatchFinitePrefixWeightedControllerDirectionalDefect_exists_l2_rate
    (theta h b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    ∃ B : Real, 0 < B ∧ ∀ K : Nat, 0 < K →
      (∫ omega,
        prespecifiedBatchFinitePrefixWeightedControllerDirectionalDefect
          theta h b K omega ^ 2
        ∂prespecifiedBatchEstimatorPrefixMeasure theta b K) <=
        B / (K : Real) ^ 3 := by
  obtain ⟨A, hA, hrow⟩ :=
    exactConcreteControllerDirectionalRowError_exists_l2_constant
      theta h b hTruth hSeed
  let D : Real := (45927 : Real) ^ 2 / 27
  let B : Real := A * D / (729 : Real) ^ 2
  have hD : 0 < D := by dsimp [D]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro K hK
  let μ := prespecifiedBatchEstimatorPrefixMeasure theta b K
  have hphysical := mixedNonzeroInterior_pauliPilotPhysical theta hTruth
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact prespecifiedBatchEstimatorPrefixMeasure_isProbability
      theta b hphysical K
  have hrowIntegral (k : Fin K) :
      (∫ omega,
        exactConcreteControllerDirectionalRowError theta h b k
          (prespecifiedBatchPrefixPilot K k omega) ^ 2 ∂μ) <=
        A / (exactConcreteBatchPilotBlocks k : Real) := by
    exact prespecifiedBatchControllerDirectionalRowError_integral_sq_le
      theta h b hphysical A hrow K k
  have htermIntegral (k : Fin K) :
      (∫ omega,
        ((exactConcreteBatchExploitationSize k : Real) *
          exactConcreteControllerDirectionalRowError theta h b k
            (prespecifiedBatchPrefixPilot K k omega)) ^ 2 ∂μ) <=
        A * D * ((k : Real) + 1) ^ 7 := by
    simp_rw [mul_pow]
    rw [integral_const_mul]
    calc
      (exactConcreteBatchExploitationSize k : Real) ^ 2 *
          (∫ omega,
            exactConcreteControllerDirectionalRowError theta h b k
              (prespecifiedBatchPrefixPilot K k omega) ^ 2 ∂μ) <=
        (exactConcreteBatchExploitationSize k : Real) ^ 2 *
          (A / (exactConcreteBatchPilotBlocks k : Real)) :=
        mul_le_mul_of_nonneg_left (hrowIntegral k) (sq_nonneg _)
      _ = A * ((exactConcreteBatchExploitationSize k : Real) ^ 2 /
          (exactConcreteBatchPilotBlocks k : Real)) := by ring
      _ <= A * (D * ((k : Real) + 1) ^ 7) :=
        mul_le_mul_of_nonneg_left
          (by simpa [D] using
            exactConcreteBatchExploitation_sq_div_pilot_le_power_seven k)
          hA.le
      _ = A * D * ((k : Real) + 1) ^ 7 := by ring
  have hsumPower :
      (∑ k : Fin K, A * D * ((k : Real) + 1) ^ 7) <=
        A * D * (K : Real) ^ 8 := by
    calc
      (∑ k : Fin K, A * D * ((k : Real) + 1) ^ 7) <=
          ∑ _k : Fin K, A * D * (K : Real) ^ 7 := by
        apply Finset.sum_le_sum
        intro k hk
        have hkK : (k : Real) + 1 <= (K : Real) := by
          exact_mod_cast (Nat.succ_le_iff.mpr k.isLt)
        have hp : ((k : Real) + 1) ^ 7 <= (K : Real) ^ 7 := by
          gcongr
        exact mul_le_mul_of_nonneg_left hp
          (mul_nonneg hA.le hD.le)
      _ = A * D * (K : Real) ^ 8 := by simp; ring
  have hsumIntegral :
      (∫ omega,
        ∑ k : Fin K,
          ((exactConcreteBatchExploitationSize k : Real) *
            exactConcreteControllerDirectionalRowError theta h b k
              (prespecifiedBatchPrefixPilot K k omega)) ^ 2 ∂μ) <=
        A * D * (K : Real) ^ 8 := by
    rw [integral_finsetSum]
    · exact (Finset.sum_le_sum fun k _hk => htermIntegral k).trans hsumPower
    · intro k hk
      exact Integrable.of_finite
  have hintegral :
      (∫ omega,
        prespecifiedBatchFinitePrefixWeightedControllerDirectionalDefect
          theta h b K omega ^ 2 ∂μ) <=
      (prespecifiedBatchTotalObservations K : Real)⁻¹ ^ 2 * (K : Real) *
        (A * D * (K : Real) ^ 8) := by
    calc
      (∫ omega,
        prespecifiedBatchFinitePrefixWeightedControllerDirectionalDefect
          theta h b K omega ^ 2 ∂μ) <=
        ∫ omega,
          (prespecifiedBatchTotalObservations K : Real)⁻¹ ^ 2 * (K : Real) *
            ∑ k : Fin K,
              ((exactConcreteBatchExploitationSize k : Real) *
                exactConcreteControllerDirectionalRowError theta h b k
                  (prespecifiedBatchPrefixPilot K k omega)) ^ 2 ∂μ := by
        apply integral_mono Integrable.of_finite Integrable.of_finite
        intro omega
        exact prespecifiedBatchFinitePrefixWeightedControllerDirectionalDefect_sq_le
          theta h b K omega
      _ = (prespecifiedBatchTotalObservations K : Real)⁻¹ ^ 2 * (K : Real) *
          (∫ omega,
            ∑ k : Fin K,
              ((exactConcreteBatchExploitationSize k : Real) *
                exactConcreteControllerDirectionalRowError theta h b k
                  (prespecifiedBatchPrefixPilot K k omega)) ^ 2 ∂μ) := by
        rw [integral_const_mul]
      _ <= (prespecifiedBatchTotalObservations K : Real)⁻¹ ^ 2 * (K : Real) *
          (A * D * (K : Real) ^ 8) :=
        mul_le_mul_of_nonneg_left hsumIntegral
          (mul_nonneg (sq_nonneg _) (by positivity))
  have hKreal : (0 : Real) < K := by exact_mod_cast hK
  have hN : (prespecifiedBatchTotalObservations K : Real) =
      729 * (K : Real) ^ 6 := by
    rw [prespecifiedBatchTotalObservations_eq]
    push_cast
    ring
  calc
    (∫ omega,
      prespecifiedBatchFinitePrefixWeightedControllerDirectionalDefect
        theta h b K omega ^ 2 ∂μ) <=
      (prespecifiedBatchTotalObservations K : Real)⁻¹ ^ 2 * (K : Real) *
        (A * D * (K : Real) ^ 8) := hintegral
    _ = B / (K : Real) ^ 3 := by
      rw [hN]
      dsimp [B]
      field_simp [ne_of_gt hKreal]

/-- Exact real-valued representation of the pooled-pilot Newton scale
`K^(5/4)`. -/
def prespecifiedBatchControllerNewtonScale (K : Nat) : Real :=
  (K : Real) * Real.sqrt (Real.sqrt (K : Real))

/-- The weighted controller defect remains negligible after multiplication
by the exact `K^(5/4)` Newton scale: its scaled mean square is at most
`B / sqrt K`. -/
theorem prespecifiedBatchFinitePrefixWeightedControllerDirectionalDefect_exists_newtonScaled_l2_rate
    (theta h b : RLSVector 3)
    (hTruth : QubitOracle.MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    ∃ B : Real, 0 < B ∧ ∀ K : Nat, 0 < K →
      (∫ omega,
        (prespecifiedBatchControllerNewtonScale K *
          prespecifiedBatchFinitePrefixWeightedControllerDirectionalDefect
            theta h b K omega) ^ 2
        ∂prespecifiedBatchEstimatorPrefixMeasure theta b K) <=
        B / Real.sqrt (K : Real) := by
  obtain ⟨B, hB, hrate⟩ :=
    prespecifiedBatchFinitePrefixWeightedControllerDirectionalDefect_exists_l2_rate
      theta h b hTruth hSeed
  refine ⟨B, hB, ?_⟩
  intro K hK
  have hKreal : (0 : Real) < K := by exact_mod_cast hK
  have hsqrt : 0 < Real.sqrt (K : Real) := Real.sqrt_pos.2 hKreal
  simp_rw [mul_pow]
  rw [integral_const_mul]
  calc
    prespecifiedBatchControllerNewtonScale K ^ 2 *
        (∫ omega,
          prespecifiedBatchFinitePrefixWeightedControllerDirectionalDefect
            theta h b K omega ^ 2
          ∂prespecifiedBatchEstimatorPrefixMeasure theta b K) <=
      prespecifiedBatchControllerNewtonScale K ^ 2 *
        (B / (K : Real) ^ 3) :=
      mul_le_mul_of_nonneg_left (hrate K hK) (sq_nonneg _)
    _ = B / Real.sqrt (K : Real) := by
      unfold prespecifiedBatchControllerNewtonScale
      rw [mul_pow, Real.sq_sqrt (Real.sqrt_nonneg _)]
      field_simp [ne_of_gt hKreal, ne_of_gt hsqrt]
      nlinarith [Real.sq_sqrt hKreal.le]

/-- The explicit Newton-scaled mean-square envelope tends to zero. -/
theorem prespecifiedBatchControllerNewtonScaled_l2Envelope_tendsto_zero
    (B : Real) :
    Tendsto (fun K : Nat => B / Real.sqrt (K : Real))
      atTop (nhds 0) := by
  have hsqrt : Tendsto (fun K : Nat => Real.sqrt (K : Real))
      atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  simpa [div_eq_mul_inv] using
    (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hsqrt))

end

end QubitOracle.Paper
