import QubitOracle.Paper.OneQubitMixedPolynomialHajekLANReduction
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Finite Radon--Nikodym closure for the polynomial mixed-qubit protocol

This file discharges the last model-specific finite computation in the
concrete Hajek LAN reduction.  It proves pointwise Radon--Nikodym ratios on a
finite full-support space, strict positivity of every interior Born atom, and
the exact equality between the complete likelihood exponential and the joint
row-mass ratio.

No external statistical theorem is introduced here.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace QubitOracle.Paper

noncomputable section

attribute [local instance]
  mixedTwoStageFiniteRowMeasurableSpace
  mixedTwoStageFiniteRowMeasurableSingletonClass
  mixedPolynomialTotalScaleRowMeasurableSpace
  mixedPolynomialTotalScaleRowMeasurableSingletonClass

/-! ## Generic finite full-support Radon--Nikodym calculation -/

theorem finiteFullSupport_absolutelyContinuous
    {alpha : Type*} [MeasurableSpace alpha] [Fintype alpha]
    [MeasurableSingletonClass alpha]
    (mu nu : Measure alpha)
    (hnu : forall x : alpha, 0 < nu {x}) :
    mu ≪ nu := by
  intro s hs
  have hsempty : s = ∅ := by
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    have hmono : nu {x} ≤ nu s :=
      measure_mono (Set.singleton_subset_iff.2 hx)
    rw [hs] at hmono
    exact (not_lt_of_ge hmono) (hnu x)
  rw [hsempty, measure_empty]

theorem finiteFullSupport_rnDeriv_eq_singletonRatio
    {alpha : Type*} [MeasurableSpace alpha] [Fintype alpha]
    [MeasurableSingletonClass alpha]
    (mu nu : Measure alpha) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hnu : forall x : alpha, 0 < nu {x}) (x : alpha) :
    mu.rnDeriv nu x = mu {x} / nu {x} := by
  have hac : mu ≪ nu :=
    finiteFullSupport_absolutelyContinuous mu nu hnu
  have hdensity :=
    Measure.withDensity_rnDeriv_eq mu nu hac
  have hmass :=
    congrArg (fun xi : Measure alpha => xi {x}) hdensity
  rw [withDensity_apply _ (measurableSet_singleton x),
    lintegral_singleton] at hmass
  apply (ENNReal.eq_div_iff (ne_of_gt (hnu x))
    (measure_ne_top nu {x})).2
  rw [mul_comm]
  exact hmass

theorem finiteFullSupport_rnDeriv_toReal_eq_singletonRatio
    {alpha : Type*} [MeasurableSpace alpha] [Fintype alpha]
    [MeasurableSingletonClass alpha]
    (mu nu : Measure alpha) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hnu : forall x : alpha, 0 < nu {x}) (x : alpha) :
    (mu.rnDeriv nu x).toReal =
      (mu {x}).toReal / (nu {x}).toReal := by
  rw [finiteFullSupport_rnDeriv_eq_singletonRatio mu nu hnu x,
    ENNReal.toReal_div]

/-! ## Strict positivity of every interior two-stage Born atom -/

theorem pauliBornProbability_pos_of_strictInterior
    (theta : RLSVector 3) (hInterior : MixedPilotStrictInterior theta)
    (j : Fin 3) (outcome : Bool) :
    0 < pauliBornProbability theta j outcome := by
  have hj :=
    abs_lt.1
      (mixedPilotStrictInterior_coordinate_abs_lt_one
        theta hInterior j)
  cases outcome <;>
    simp [pauliBornProbability] <;> linarith

theorem pauliPilotBlockMass_pos_of_strictInterior
    (theta : RLSVector 3) (hInterior : MixedPilotStrictInterior theta)
    (block : PauliPilotBlock) :
    0 < pauliPilotBlockMass theta block := by
  unfold pauliPilotBlockMass
  exact Finset.prod_pos fun j _ =>
    pauliBornProbability_pos_of_strictInterior
      theta hInterior j (block j)

theorem pauliPilotPathMass_pos_of_strictInterior
    {q : Nat} (theta : RLSVector 3)
    (hInterior : MixedPilotStrictInterior theta)
    (path : PauliPilotPath q) :
    0 < pauliPilotPathMass theta path := by
  unfold pauliPilotPathMass
  exact Finset.prod_pos fun k _ =>
    pauliPilotBlockMass_pos_of_strictInterior
      theta hInterior (path k)

theorem mixedTwoStageFinalBornProbability_pos_of_strictInterior
    {q T : Nat} (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q)
    (hInterior : MixedPilotStrictInterior theta)
    (pilot : PauliPilotPath q) (t : Fin T) (outcome : Bool) :
    0 < mixedTwoStageFinalBornProbability
      theta selected pilot t outcome := by
  let axis := mixedTwoStageFinalAxis selected pilot t
  have hgap : 0 < mixedInteriorGap theta :=
    mixedInteriorGap_pos theta hInterior
  have hfloor :=
    mixedExactCycleScoreDenominator_floor
      theta axis outcome
      (mixedTwoStageFinalAxis_unit selected pilot t)
  have hden :
      0 < 1 + pauliOutcomeSign outcome *
        QubitOracle.blochDot theta axis :=
    hgap.trans_le hfloor
  have hcomm :
      QubitOracle.blochDot axis theta =
        QubitOracle.blochDot theta axis :=
    mixedTwoStageScore_blochDot_comm axis theta
  cases outcome <;>
    simp [mixedTwoStageFinalBornProbability, pauliOutcomeSign,
      axis, hcomm] at hden ⊢ <;> linarith

theorem mixedTwoStageConditionalFinalPathMass_pos_of_strictInterior
    {q T : Nat} (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q)
    (hInterior : MixedPilotStrictInterior theta)
    (pilot : PauliPilotPath q)
    (finalPath : MixedTwoStageFinalPath T) :
    0 < mixedTwoStageConditionalFinalPathMass
      theta selected pilot finalPath := by
  unfold mixedTwoStageConditionalFinalPathMass
  exact Finset.prod_pos fun t _ =>
    mixedTwoStageFinalBornProbability_pos_of_strictInterior
      theta selected hInterior pilot t (finalPath t)

theorem mixedTwoStageFiniteRowMass_pos_of_strictInterior
    {q T : Nat} (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q)
    (hInterior : MixedPilotStrictInterior theta)
    (row : MixedTwoStageFiniteRow q T) :
    0 < mixedTwoStageFiniteRowMass theta selected row := by
  unfold mixedTwoStageFiniteRowMass
  exact mul_pos
    (pauliPilotPathMass_pos_of_strictInterior
      theta hInterior row.1)
    (mixedTwoStageConditionalFinalPathMass_pos_of_strictInterior
      theta selected hInterior row.1 row.2)

theorem mixedTwoStageFiniteBornMeasure_singleton
    {q T : Nat} (theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q)
    (hphysical : PauliPilotPhysicalBloch theta)
    (row : MixedTwoStageFiniteRow q T) :
    mixedTwoStageFiniteBornMeasure theta selected {row} =
      ENNReal.ofReal (mixedTwoStageFiniteRowMass theta selected row) := by
  classical
  rw [mixedTwoStageFiniteBornMeasure_apply
    theta selected hphysical {row}]
  simp

theorem mixedTwoStageFiniteBornMeasure_rnDeriv_toReal_eq_rowMassRatio
    {q T : Nat} (eta theta : RLSVector 3)
    (selected : PilotSelectedFinalFrame q)
    (hEta : MixedPilotStrictInterior eta)
    (hTheta : MixedPilotStrictInterior theta)
    (row : MixedTwoStageFiniteRow q T) :
    ((mixedTwoStageFiniteBornMeasure eta selected).rnDeriv
      (mixedTwoStageFiniteBornMeasure theta selected) row).toReal =
      mixedTwoStageFiniteRowMass eta selected row /
        mixedTwoStageFiniteRowMass theta selected row := by
  letI : IsProbabilityMeasure
      (mixedTwoStageFiniteBornMeasure (T := T) eta selected) :=
    ⟨mixedTwoStageFiniteBornMeasure_univ (T := T) eta selected
      (mixedPilotStrictInterior_physical eta hEta)⟩
  letI : IsProbabilityMeasure
      (mixedTwoStageFiniteBornMeasure (T := T) theta selected) :=
    ⟨mixedTwoStageFiniteBornMeasure_univ (T := T) theta selected
      (mixedPilotStrictInterior_physical theta hTheta)⟩
  have hsupport :
      forall x : MixedTwoStageFiniteRow q T,
        0 < mixedTwoStageFiniteBornMeasure theta selected {x} := by
    intro x
    rw [mixedTwoStageFiniteBornMeasure_singleton (T := T) theta selected
      (mixedPilotStrictInterior_physical theta hTheta) x]
    exact ENNReal.ofReal_pos.2
      (mixedTwoStageFiniteRowMass_pos_of_strictInterior
        theta selected hTheta x)
  rw [finiteFullSupport_rnDeriv_toReal_eq_singletonRatio
    (mixedTwoStageFiniteBornMeasure (T := T) eta selected)
    (mixedTwoStageFiniteBornMeasure (T := T) theta selected) hsupport row]
  rw [mixedTwoStageFiniteBornMeasure_singleton (T := T) eta selected
      (mixedPilotStrictInterior_physical eta hEta) row,
    mixedTwoStageFiniteBornMeasure_singleton (T := T) theta selected
      (mixedPilotStrictInterior_physical theta hTheta) row,
    ENNReal.toReal_ofReal
      (mixedTwoStageFiniteRowMass_nonnegative eta selected
        (mixedPilotStrictInterior_physical eta hEta) row),
    ENNReal.toReal_ofReal
      (mixedTwoStageFiniteRowMass_nonnegative theta selected
        (mixedPilotStrictInterior_physical theta hTheta) row)]

/-! ## Exact finite likelihood-to-mass algebra -/

theorem real_exp_fintype_sum_log_div_eq_prod_div
    {alpha : Type*} [Fintype alpha]
    (a c : alpha -> Real)
    (ha : forall i, 0 < a i) (hc : forall i, 0 < c i) :
    Real.exp (∑ i, Real.log (a i / c i)) =
      (∏ i, a i) / (∏ i, c i) := by
  rw [Real.exp_sum]
  simp_rw [Real.exp_log (div_pos (ha _) (hc _))]
  exact Finset.prod_div_distrib a c

theorem mixedPolynomialPilotLANScale_eq_totalFinalObservations
    (n : Nat) :
    mixedPolynomialPilotLANScale n =
      mixedPolynomialTotalScaleFinalObservations n := by
  simp [mixedPolynomialPilotLANScale, mixedPolynomialScheduleM,
    mixedPolynomialTotalScaleFinalObservations,
    mixedPolynomialTotalScaleFinalCycles]

theorem mixedPolynomialTotalScaleExactCycleLocalParameter_eq_totalAlternative
    (theta h : Fin 3 -> Real) (n : Nat) :
    mixedExactCycleLocalParameter theta
        (mixedPolynomialTotalScaleDirection n h)
        (mixedPolynomialTotalScaleFinalCycles n) =
      mixedLocalAlternative theta
        mixedPolynomialTotalScaleObservations n h := by
  calc
    mixedExactCycleLocalParameter theta
        (mixedPolynomialTotalScaleDirection n h)
        (mixedPolynomialTotalScaleFinalCycles n) =
      (fun i => theta i + h i /
        Real.sqrt (mixedPolynomialTotalScaleObservations n : Real)) :=
      mixedPolynomialTotalScaleLocalParameter_eq theta h n
    _ = mixedLocalAlternative theta
        mixedPolynomialTotalScaleObservations n h := by
      funext i
      unfold mixedLocalAlternative mixedLocalScale
      ring

theorem mixedPolynomialPilotLocalAlternative_eq_totalAlternative
    (theta h : Fin 3 -> Real) (n : Nat) :
    (fun i => theta i +
      mixedPolynomialTotalScaleDirection n h i /
        Real.sqrt (mixedPolynomialPilotLANScale n : Real)) =
      mixedLocalAlternative theta
        mixedPolynomialTotalScaleObservations n h := by
  calc
    (fun i => theta i +
      mixedPolynomialTotalScaleDirection n h i /
        Real.sqrt (mixedPolynomialPilotLANScale n : Real)) =
        mixedExactCycleLocalParameter theta
          (mixedPolynomialTotalScaleDirection n h)
          (mixedPolynomialTotalScaleFinalCycles n) := by
            funext i
            unfold mixedExactCycleLocalParameter
            rw [mixedPolynomialPilotLANScale_eq_totalFinalObservations]
            rfl
    _ = mixedLocalAlternative theta
        mixedPolynomialTotalScaleObservations n h :=
      mixedPolynomialTotalScaleExactCycleLocalParameter_eq_totalAlternative
        theta h n

theorem pauliBornProbability_eq_signed
    (theta : Fin 3 -> Real) (j : Fin 3) (outcome : Bool) :
    pauliBornProbability theta j outcome =
      (1 + pauliOutcomeSign outcome * theta j) / 2 := by
  cases outcome <;>
    simp [pauliBornProbability, pauliOutcomeSign, sub_eq_add_neg]

theorem mixedPolynomialTotalScalePilotBornRatio_eq_one_add
    (theta h : Fin 3 -> Real)
    (hInterior : MixedPilotStrictInterior theta)
    (n : Nat) (j : Fin 3) (outcome : Bool) :
    pauliBornProbability
        (mixedLocalAlternative theta
          mixedPolynomialTotalScaleObservations n h)
        j outcome /
      pauliBornProbability theta j outcome =
        1 + mixedPolynomialPilotLocalRatio theta
          (mixedPolynomialTotalScaleDirection n h) n j outcome := by
  rw [← mixedPolynomialPilotLocalAlternative_eq_totalAlternative
    theta h n]
  have hden :
      0 < 1 + pauliOutcomeSign outcome * theta j :=
    (mixedPilotInteriorMargin_pos theta hInterior).trans_le
      (mixedPilot_scoreDenominator_ge_margin
        theta hInterior j outcome)
  have hsqrt :
      0 < Real.sqrt (mixedPolynomialPilotLANScale n : Real) :=
    Real.sqrt_pos.2 (by
      exact_mod_cast mixedPolynomialPilotLANScale_pos n)
  unfold mixedPolynomialPilotLocalRatio
    mixedPilotOneShotDirectionalScore
  rw [pauliBornProbability_eq_signed,
    pauliBornProbability_eq_signed]
  field_simp [ne_of_gt hden, ne_of_gt hsqrt]
  ring

theorem mixedPolynomialTotalScalePilotLogLikelihood_exp_eq_massRatio
    (theta h : Fin 3 -> Real)
    (n : Nat)
    (hTheta : MixedPilotStrictInterior theta)
    (hEta : MixedPilotStrictInterior
      (mixedLocalAlternative theta
        mixedPolynomialTotalScaleObservations n h))
    (path : PauliPilotPath (mixedPolynomialTotalScalePilotBlocks n)) :
    Real.exp
        (mixedPolynomialTotalScalePilotLogLikelihood theta h n path) =
      pauliPilotPathMass
          (mixedLocalAlternative theta
            mixedPolynomialTotalScaleObservations n h) path /
        pauliPilotPathMass theta path := by
  unfold mixedPolynomialTotalScalePilotLogLikelihood
    mixedPolynomialPilotLogLikelihood
  simp_rw [← mixedPolynomialTotalScalePilotBornRatio_eq_one_add
    theta h hTheta n]
  have hblock
      (k : Fin (mixedPolynomialPilotBlocks n)) :
      Real.exp
          (∑ j : Fin 3, Real.log
            (pauliBornProbability
                (mixedLocalAlternative theta
                  mixedPolynomialTotalScaleObservations n h)
                j (path k j) /
              pauliBornProbability theta j (path k j))) =
        (∏ j : Fin 3, pauliBornProbability
            (mixedLocalAlternative theta
              mixedPolynomialTotalScaleObservations n h)
            j (path k j)) /
          ∏ j : Fin 3, pauliBornProbability theta j (path k j) :=
    real_exp_fintype_sum_log_div_eq_prod_div
      (fun j => pauliBornProbability
        (mixedLocalAlternative theta
          mixedPolynomialTotalScaleObservations n h) j (path k j))
      (fun j => pauliBornProbability theta j (path k j))
      (fun j => pauliBornProbability_pos_of_strictInterior
        _ hEta j (path k j))
      (fun j => pauliBornProbability_pos_of_strictInterior
        theta hTheta j (path k j))
  rw [Real.exp_sum]
  simp_rw [hblock]
  rw [Finset.prod_div_distrib]
  rfl

theorem mixedPolynomialTotalScaleFinalLogLikelihood_exp_eq_massRatio
    (theta h b : Fin 3 -> Real)
    (n : Nat)
    (hTheta : MixedPilotStrictInterior theta)
    (hEta : MixedPilotStrictInterior
      (mixedLocalAlternative theta
        mixedPolynomialTotalScaleObservations n h))
    (row : MixedPolynomialTotalScaleRow n) :
    Real.exp
        (mixedPolynomialTotalScaleFinalLogLikelihood theta h b n row) =
      mixedTwoStageConditionalFinalPathMass
          (mixedLocalAlternative theta
            mixedPolynomialTotalScaleObservations n h)
          (mixedPolynomialTotalScaleSelectedFrame b n) row.1 row.2 /
        mixedTwoStageConditionalFinalPathMass theta
          (mixedPolynomialTotalScaleSelectedFrame b n) row.1 row.2 := by
  unfold mixedPolynomialTotalScaleFinalLogLikelihood
  rw [mixedExactCycleConditionalLogLikelihoodRatio_eq_sum_log_bornRatios
    theta (mixedPolynomialTotalScaleDirection n h)
    (mixedPolynomialTotalScaleSelectedFrame b n) row.1 row.2
    hTheta (mixedPolynomialTotalScaleFinalCycles_pos n)]
  rw [mixedPolynomialTotalScaleExactCycleLocalParameter_eq_totalAlternative
    theta h n]
  change Real.exp
      (∑ t : Fin (mixedPolynomialTotalScaleFinalObservations n),
        Real.log
          (mixedTwoStageFinalBornProbability
              (mixedLocalAlternative theta
                mixedPolynomialTotalScaleObservations n h)
              (mixedPolynomialTotalScaleSelectedFrame b n)
              row.1 t (row.2 t) /
            mixedTwoStageFinalBornProbability theta
              (mixedPolynomialTotalScaleSelectedFrame b n)
              row.1 t (row.2 t))) = _
  rw [real_exp_fintype_sum_log_div_eq_prod_div
    (fun t => mixedTwoStageFinalBornProbability
      (mixedLocalAlternative theta
        mixedPolynomialTotalScaleObservations n h)
      (mixedPolynomialTotalScaleSelectedFrame b n)
      row.1 t (row.2 t))
    (fun t => mixedTwoStageFinalBornProbability theta
      (mixedPolynomialTotalScaleSelectedFrame b n)
      row.1 t (row.2 t))
    (fun t => mixedTwoStageFinalBornProbability_pos_of_strictInterior
      _ _ hEta row.1 t (row.2 t))
    (fun t => mixedTwoStageFinalBornProbability_pos_of_strictInterior
      theta _ hTheta row.1 t (row.2 t))]
  rfl

theorem mixedPolynomialTotalScaleCompleteLogLikelihood_exp_eq_rowMassRatio
    (theta h b : Fin 3 -> Real)
    (n : Nat)
    (hTheta : MixedPilotStrictInterior theta)
    (hEta : MixedPilotStrictInterior
      (mixedLocalAlternative theta
        mixedPolynomialTotalScaleObservations n h))
    (row : MixedPolynomialTotalScaleRow n) :
    Real.exp
        (mixedPolynomialTotalScaleCompleteLogLikelihood theta h b n row) =
      mixedTwoStageFiniteRowMass
          (mixedLocalAlternative theta
            mixedPolynomialTotalScaleObservations n h)
          (mixedPolynomialTotalScaleSelectedFrame b n) row /
        mixedTwoStageFiniteRowMass theta
          (mixedPolynomialTotalScaleSelectedFrame b n) row := by
  unfold mixedPolynomialTotalScaleCompleteLogLikelihood
  rw [Real.exp_add,
    mixedPolynomialTotalScalePilotLogLikelihood_exp_eq_massRatio
      theta h n hTheta hEta row.1,
    mixedPolynomialTotalScaleFinalLogLikelihood_exp_eq_massRatio
      theta h b n hTheta hEta row]
  unfold mixedTwoStageFiniteRowMass
  field_simp [
    ne_of_gt (pauliPilotPathMass_pos_of_strictInterior
      theta hTheta row.1),
    ne_of_gt
      (mixedTwoStageConditionalFinalPathMass_pos_of_strictInterior
        theta (mixedPolynomialTotalScaleSelectedFrame b n)
        hTheta row.1 row.2)]

theorem mixedPolynomialTotalScaleRowMeasure_rnDeriv_toReal_eq_rowMassRatio
    (eta theta b : Fin 3 -> Real)
    (hEta : MixedPilotStrictInterior eta)
    (hTheta : MixedPilotStrictInterior theta)
    (n : Nat) (row : MixedPolynomialTotalScaleRow n) :
    ((mixedPolynomialTotalScaleRowMeasure eta b n).rnDeriv
      (mixedPolynomialTotalScaleRowMeasure theta b n) row).toReal =
      mixedTwoStageFiniteRowMass eta
          (mixedPolynomialTotalScaleSelectedFrame b n) row /
        mixedTwoStageFiniteRowMass theta
          (mixedPolynomialTotalScaleSelectedFrame b n) row := by
  unfold mixedPolynomialTotalScaleRowMeasure
  exact
    mixedTwoStageFiniteBornMeasure_rnDeriv_toReal_eq_rowMassRatio
      eta theta (mixedPolynomialTotalScaleSelectedFrame b n)
      hEta hTheta row

/-! ## Unconditional concrete LAN closure -/

theorem mixedPolynomialHajekLocalAlternative_eventually_strictInterior
    (theta b h : Fin 3 -> Real)
    (hTruth : MixedNonzeroInteriorTruth theta) :
    ∀ᶠ n : Nat in atTop,
      MixedPilotStrictInterior
        (mixedLocalAlternative theta
          mixedPolynomialTotalScaleObservations n
          (mixedPolynomialTruthFrameWhiteningDirection theta b h)) := by
  let ah :=
    mixedPolynomialTruthFrameWhiteningDirection theta b h
  let H : Real := blochNormSq ah + 1
  have hnorm : 0 ≤ blochNormSq ah := by
    unfold blochNormSq
    positivity
  have hball : MixedLocalDirectionBall H ah := by
    unfold MixedLocalDirectionBall H
    nlinarith [sq_nonneg (blochNormSq ah)]
  have hscale :
      Tendsto (mixedLocalScale mixedPolynomialTotalScaleObservations)
        atTop (nhds 0) := by
    change Tendsto
      (fun n : Nat =>
        (Real.sqrt (mixedPolynomialTotalScaleObservations n : Real))⁻¹)
      atTop (nhds 0)
    apply Tendsto.squeeze tendsto_const_nhds
      mixedPolynomial_invSqrtLANScale_tendsto_zero
    · intro n
      positivity
    · intro n
      have hcountNat :
          mixedPolynomialPilotLANScale n ≤
            mixedPolynomialTotalScaleObservations n := by
        simp [mixedPolynomialPilotLANScale,
          mixedPolynomialScheduleM,
          mixedPolynomialTotalScaleObservations,
          mixedPolynomialTotalScalePilotObservations,
          mixedPolynomialTotalScalePilotBlocks,
          mixedPolynomialTotalScaleFinalObservations,
          mixedPolynomialTotalScaleFinalCycles]
      exact inv_anti₀
        (Real.sqrt_pos.2 (by
          exact_mod_cast mixedPolynomialPilotLANScale_pos n))
        (Real.sqrt_le_sqrt (by exact_mod_cast hcountNat))
  have hinterior :=
    mixedLocalAlternative_eventually_uniform_interior
      theta mixedPolynomialTotalScaleObservations H hTruth.2 hscale
  filter_upwards [hinterior] with n hn
  exact hn ah hball

theorem mixedPolynomialFiniteRadonNikodymIdentity_proved
    (theta b : Fin 3 -> Real)
    (hTruth : MixedNonzeroInteriorTruth theta) :
    MixedPolynomialFiniteRadonNikodymIdentity theta b hTruth := by
  intro h
  have hlaw :=
    mixedPolynomialHajekExperiment_eventually_localLaw
      theta b h hTruth
  have hinterior :=
    mixedPolynomialHajekLocalAlternative_eventually_strictInterior
      theta b h hTruth
  rw [eventually_atTop] at hlaw hinterior
  obtain ⟨Nlaw, hNlaw⟩ := hlaw
  obtain ⟨Nint, hNint⟩ := hinterior
  refine ⟨max Nlaw Nint, ?_⟩
  intro n hn row
  have hnLaw := hNlaw n (le_trans (Nat.le_max_left _ _) hn)
  have hnInterior := hNint n (le_trans (Nat.le_max_right _ _) hn)
  unfold hajekLikelihoodRatio
  rw [hnLaw, mixedPolynomialHajekExperiment_baseLaw]
  exact
    (mixedPolynomialTotalScaleRowMeasure_rnDeriv_toReal_eq_rowMassRatio
      (mixedLocalAlternative theta
        mixedPolynomialTotalScaleObservations n
        (mixedPolynomialTruthFrameWhiteningDirection theta b h))
      theta b hnInterior hTruth.2 n row).trans
      (mixedPolynomialTotalScaleCompleteLogLikelihood_exp_eq_rowMassRatio
        theta
        (mixedPolynomialTruthFrameWhiteningDirection theta b h)
        b n hTruth.2 hnInterior row).symm

noncomputable def mixedPolynomialConcreteFrozenHajekLAN
    (theta b : Fin 3 -> Real)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hHoeffding : MixedPolynomialFinitePilotHoeffdingContracts theta
      (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)) :
    Hajek1972Assumption31LAN
      (mixedPolynomialHajekExperiment theta b hTruth) 0 :=
  mixedPolynomialConcreteFrozenHajekLAN_of_finiteRN
    theta b hTruth hSeed hHoeffding
    (mixedPolynomialFiniteRadonNikodymIdentity_proved theta b hTruth)

noncomputable def constructConcreteFrozenMixedQubitLANConclusion
    (theta b : Fin 3 -> Real)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hHoeffding : MixedPolynomialFinitePilotHoeffdingContracts theta
      (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)) :
    FrozenMixedQubitLANConclusion
      (mixedPolynomialHajekExperiment theta b hTruth) 0 :=
  constructConcreteFrozenMixedQubitLANConclusion_of_finiteRN
    theta b hTruth hSeed hHoeffding
    (mixedPolynomialFiniteRadonNikodymIdentity_proved theta b hTruth)

end

end QubitOracle.Paper
