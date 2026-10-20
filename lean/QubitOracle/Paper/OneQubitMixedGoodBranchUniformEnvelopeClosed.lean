import QubitOracle.Paper.OneQubitMixedGoodBranchUniformFrame

/-!
# Closed uniform envelope on the mixed-qubit polynomial good branch

This file closes the deterministic good-branch uniformization step.  If a
uniform real bound failed, classical choice selects one offending pilot outcome
at an index beyond every prescribed cutoff.  Those indices tend to infinity,
and the explicit good-event coordinate bound forces the selected pilot vectors
to the truth.  The existing sequential frame-risk theorem then contradicts the
fixed positive deviation.

No pilot/final joint law and no uniform-integrability statement is used.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace QubitOracle.Paper

noncomputable section

/-- Concrete sequential-contradiction theorem.  Uniformly over every pilot
outcome satisfying the polynomial good-event coordinate inequalities, the
conditional scaled quadratic risk converges to `9 / 4`. -/
theorem mixedPolynomialPilot_goodBranch_uniform_real
    (b theta : RLSVector 3) (qFinal : ℕ → ℕ)
    (hqFinal : ∀ n, 0 < qFinal n)
    (hPositive : 0 < QubitOracle.blochNormSq theta)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ n in atTop, ∀ omega : PauliPilotConsistencySampleSpace,
      omega ∉ polynomialPilotBadEvent theta n →
        |mixedFrameConditionalScaledQuadraticRisk (q := qFinal n) theta
              (mixedPilotSelectedLocalFrame b
                (polynomialPilotEstimator n omega)) - 9 / 4| < epsilon := by
  by_contra hUniform
  have hfar : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∃ omega : PauliPilotConsistencySampleSpace,
        omega ∉ polynomialPilotBadEvent theta n ∧
          epsilon ≤
            |mixedFrameConditionalScaledQuadraticRisk (q := qFinal n) theta
                (mixedPilotSelectedLocalFrame b
                  (polynomialPilotEstimator n omega)) - 9 / 4| := by
    intro N
    by_contra hN
    push_neg at hN
    apply hUniform
    filter_upwards [eventually_ge_atTop N] with n hn
    intro omega hgood
    exact hN n hn omega hgood
  choose index hindex_ge hbadIndex using hfar
  choose omega hgood hdeviationFar using hbadIndex
  have hindexTendsto : Tendsto index atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro N
    filter_upwards [eventually_ge_atTop N] with k hk
    exact hk.trans (hindex_ge k)
  have hthreshold :
      Tendsto (fun k => polynomialPilotThreshold (index k))
        atTop (nhds 0) :=
    polynomialPilotThreshold_tendsto_zero.comp hindexTendsto
  have hcoordinate (k : ℕ) (j : Fin 3) :
      |polynomialPilotEstimator (index k) (omega k) j - theta j| <
        polynomialPilotThreshold (index k) := by
    by_contra hnot
    have hle : polynomialPilotThreshold (index k) ≤
        |polynomialPilotEstimator (index k) (omega k) j - theta j| :=
      le_of_not_gt hnot
    apply hgood k
    change ∃ i : Fin 3,
      polynomialPilotThreshold (index k) ≤
        |polynomialPilotEstimator (index k) (omega k) i - theta i|
    exact ⟨j, hle⟩
  have hx (j : Fin 3) :
      Tendsto
        (fun k => polynomialPilotEstimator (index k) (omega k) j)
        atTop (nhds (theta j)) := by
    have hlower :
        Tendsto (fun k => -polynomialPilotThreshold (index k))
          atTop (nhds 0) := by
      simpa using hthreshold.neg
    have hdiff :
        Tendsto
          (fun k =>
            polynomialPilotEstimator (index k) (omega k) j - theta j)
          atTop (nhds 0) := by
      exact Tendsto.squeeze hlower hthreshold
        (fun k => neg_le_of_abs_le (le_of_lt (hcoordinate k j)))
        (fun k => le_of_abs_le (le_of_lt (hcoordinate k j)))
    have hconst : Tendsto (fun _ : ℕ => theta j) atTop (nhds (theta j)) :=
      tendsto_const_nhds
    simpa only [sub_add_cancel, zero_add] using hdiff.add hconst
  have hrisk :
      Tendsto
        (fun k => mixedFrameConditionalScaledQuadraticRisk
          (q := qFinal (index k)) theta
          (mixedPilotSelectedLocalFrame b
            (polynomialPilotEstimator (index k) (omega k))))
        atTop (nhds (9 / 4)) :=
    mixedFrameConditionalScaledRisk_tendsto_of_coordinatewise
      b theta
      (fun k => polynomialPilotEstimator (index k) (omega k))
      (fun k => qFinal (index k))
      (fun k => hqFinal (index k)) hx
      hPositive hInterior hSeed
  have hcentered :
      Tendsto
        (fun k => mixedFrameConditionalScaledQuadraticRisk
          (q := qFinal (index k)) theta
          (mixedPilotSelectedLocalFrame b
            (polynomialPilotEstimator (index k) (omega k))) - 9 / 4)
        atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℕ => (9 / 4 : ℝ)) atTop
        (nhds (9 / 4 : ℝ)) := tendsto_const_nhds
    simpa only [sub_self] using hrisk.sub hconst
  have habs :
      Tendsto
        (fun k =>
          |mixedFrameConditionalScaledQuadraticRisk
              (q := qFinal (index k)) theta
              (mixedPilotSelectedLocalFrame b
                (polynomialPilotEstimator (index k) (omega k))) - 9 / 4|)
        atTop (nhds 0) := by
    simpa using hcentered.abs
  have heventuallySmall :
      ∀ᶠ k in atTop,
        |mixedFrameConditionalScaledQuadraticRisk
            (q := qFinal (index k)) theta
            (mixedPilotSelectedLocalFrame b
              (polynomialPilotEstimator (index k) (omega k))) - 9 / 4| <
          epsilon :=
    (tendsto_order.1 habs).2 epsilon hepsilon
  rcases (eventually_atTop.1 heventuallySmall) with ⟨K, hK⟩
  exact (not_lt_of_ge (hdeviationFar K)) (hK K le_rfl)

/-- Pointwise supremum of all conditional scaled-risk deviations on the
polynomial pilot good event. -/
noncomputable def mixedPolynomialPilotGoodBranchEnvelope
    (theta b : RLSVector 3) (qFinal : ℕ → ℕ) (n : ℕ) : ℝ≥0∞ :=
  by
    classical
    exact ⨆ omega : PauliPilotConsistencySampleSpace,
      if omega ∉ polynomialPilotBadEvent theta n then
        ENNReal.ofReal
          |mixedFrameConditionalScaledQuadraticRisk (q := qFinal n) theta
              (mixedPilotSelectedLocalFrame b
                (polynomialPilotEstimator n omega)) - 9 / 4|
      else 0

/-- A uniform real good-branch bound controls the explicit `ENNReal` supremum
envelope. -/
theorem mixedPolynomialPilotGoodBranchEnvelope_le_of_uniform_real
    (theta b : RLSVector 3) (qFinal : ℕ → ℕ) (n : ℕ)
    (epsilon : ℝ)
    (hbound : ∀ omega : PauliPilotConsistencySampleSpace,
      omega ∉ polynomialPilotBadEvent theta n →
        |mixedFrameConditionalScaledQuadraticRisk (q := qFinal n) theta
              (mixedPilotSelectedLocalFrame b
                (polynomialPilotEstimator n omega)) - 9 / 4| < epsilon) :
    mixedPolynomialPilotGoodBranchEnvelope theta b qFinal n ≤
      ENNReal.ofReal epsilon := by
  classical
  unfold mixedPolynomialPilotGoodBranchEnvelope
  refine iSup_le ?_
  intro omega
  by_cases hgood : omega ∉ polynomialPilotBadEvent theta n
  · simp only [if_pos hgood]
    exact ENNReal.ofReal_le_ofReal (le_of_lt (hbound omega hgood))
  · simp [hgood]

/-- The concrete polynomial good branch admits a common vanishing envelope.
This is exactly `MixedPilotGoodBranchUniformFrameContinuityPremise`, with no
joint-law or uniform-integrability hypothesis. -/
theorem mixedPilotGoodBranchUniformFrameContinuityPremise_closed
    (b theta : RLSVector 3) (qFinal : ℕ → ℕ)
    (hqFinal : ∀ n, 0 < qFinal n)
    (hPositive : 0 < QubitOracle.blochNormSq theta)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    MixedPilotGoodBranchUniformFrameContinuityPremise theta b qFinal := by
  classical
  have huniform (epsilon : ℝ) (hepsilon : 0 < epsilon) :
      ∀ᶠ n in atTop, ∀ omega : PauliPilotConsistencySampleSpace,
        omega ∉ polynomialPilotBadEvent theta n →
          |mixedFrameConditionalScaledQuadraticRisk (q := qFinal n) theta
                (mixedPilotSelectedLocalFrame b
                  (polynomialPilotEstimator n omega)) - 9 / 4| < epsilon :=
    mixedPolynomialPilot_goodBranch_uniform_real
      b theta qFinal hqFinal hPositive hInterior hSeed epsilon hepsilon
  have hEnvelopeTendsto :
      Tendsto
        (mixedPolynomialPilotGoodBranchEnvelope theta b qFinal)
        atTop (nhds 0) := by
    apply tendsto_order.2
    constructor
    · intro a ha
      exact False.elim
        ((not_lt_of_ge (bot_le : (0 : ℝ≥0∞) ≤ a)) ha)
    · intro a ha
      by_cases haTop : a = ⊤
      · subst a
        filter_upwards [huniform 1 zero_lt_one] with n hn
        calc
          mixedPolynomialPilotGoodBranchEnvelope theta b qFinal n ≤
              ENNReal.ofReal 1 :=
            mixedPolynomialPilotGoodBranchEnvelope_le_of_uniform_real
              theta b qFinal n 1 hn
          _ < ⊤ := ENNReal.ofReal_lt_top
      · have htoReal : 0 < a.toReal :=
          ENNReal.toReal_pos (ne_of_gt ha) haTop
        have hhalf : 0 < a.toReal / 2 := half_pos htoReal
        filter_upwards [huniform (a.toReal / 2) hhalf] with n hn
        calc
          mixedPolynomialPilotGoodBranchEnvelope theta b qFinal n ≤
              ENNReal.ofReal (a.toReal / 2) :=
            mixedPolynomialPilotGoodBranchEnvelope_le_of_uniform_real
              theta b qFinal n (a.toReal / 2) hn
          _ < ENNReal.ofReal a.toReal := by
            rw [ENNReal.ofReal_lt_ofReal_iff htoReal]
            exact half_lt_self htoReal
          _ = a := ENNReal.ofReal_toReal haTop
  refine ⟨mixedPolynomialPilotGoodBranchEnvelope theta b qFinal,
    hEnvelopeTendsto, ?_⟩
  refine Filter.Eventually.of_forall ?_
  intro n omega hgood
  unfold mixedPolynomialPilotGoodBranchEnvelope
  calc
    ENNReal.ofReal
        |mixedFrameConditionalScaledQuadraticRisk (q := qFinal n) theta
            (mixedPilotSelectedLocalFrame b
              (polynomialPilotEstimator n omega)) - 9 / 4| =
      (if omega ∉ polynomialPilotBadEvent theta n then
        ENNReal.ofReal
          |mixedFrameConditionalScaledQuadraticRisk (q := qFinal n) theta
              (mixedPilotSelectedLocalFrame b
                (polynomialPilotEstimator n omega)) - 9 / 4|
       else 0) := by simp [hgood]
    _ ≤ ⨆ w : PauliPilotConsistencySampleSpace,
        if w ∉ polynomialPilotBadEvent theta n then
          ENNReal.ofReal
            |mixedFrameConditionalScaledQuadraticRisk (q := qFinal n) theta
                (mixedPilotSelectedLocalFrame b
                  (polynomialPilotEstimator n w)) - 9 / 4|
        else 0 := le_iSup (fun w : PauliPilotConsistencySampleSpace =>
          if w ∉ polynomialPilotBadEvent theta n then
            ENNReal.ofReal
              |mixedFrameConditionalScaledQuadraticRisk (q := qFinal n) theta
                  (mixedPilotSelectedLocalFrame b
                    (polynomialPilotEstimator n w)) - 9 / 4|
          else 0) omega

/-- Closed instance of the formerly residual sequential-envelope extraction
contract for the concrete polynomial mixed-qubit protocol. -/
theorem mixedPilotGoodBranchSequentialEnvelopeExtraction_closed
    (b theta : RLSVector 3) (qFinal : ℕ → ℕ)
    (hqFinal : ∀ n, 0 < qFinal n)
    (hPositive : 0 < QubitOracle.blochNormSq theta)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    MixedPilotGoodBranchSequentialEnvelopeExtraction b theta qFinal := by
  intro _hSequential
  exact mixedPilotGoodBranchUniformFrameContinuityPremise_closed
    b theta qFinal hqFinal hPositive hInterior hSeed

namespace Label

/-- Paper-facing closed deterministic good-branch envelope reduction for the
concrete one-qubit polynomial pilot protocol. -/
theorem lem_SI_mixed_good_branch_uniform_envelope_closed_qubit
    (b theta : RLSVector 3) (qFinal : ℕ → ℕ)
    (hqFinal : ∀ n, 0 < qFinal n)
    (hPositive : 0 < QubitOracle.blochNormSq theta)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    MixedPilotGoodBranchUniformFrameContinuityPremise theta b qFinal :=
  mixedPilotGoodBranchUniformFrameContinuityPremise_closed
    b theta qFinal hqFinal hPositive hInterior hSeed

end Label

end

end QubitOracle.Paper
