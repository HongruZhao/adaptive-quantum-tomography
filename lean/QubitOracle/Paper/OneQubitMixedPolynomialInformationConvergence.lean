import QubitOracle.Paper.OneQubitMixedExactCycleInformation
import QubitOracle.Paper.OneQubitPolynomialTwoStageSchedule
import QubitOracle.Paper.OneQubitMixedPilotFrameRiskTransfer
import QubitOracle.Paper.OneQubitMixedGoodBranchUniformFrame

open scoped BigOperators ENNReal
open Filter MeasureTheory Set

namespace QubitOracle.Paper

noncomputable section

/-!
# Information convergence for the concrete polynomial two-stage mixed-qubit row

The sample space is allowed to vary with the row.  Row `n` has `(n+1)^5`
complete Pauli pilot blocks and `3 * (n+1)^6` final observations.  The latter
are split into `(n+1)^6` complete cycles through the three columns of the
pilot-selected orthonormal frame.
-/

local instance mixedPolynomialPilotPathMeasurableSpace (q : ℕ) :
    MeasurableSpace (PauliPilotPath q) := ⊤

/-- Number of complete three-Pauli pilot blocks in polynomial row `n`. -/
def mixedPolynomialQPilot (n : ℕ) : ℕ := polynomialPilotBlocks n

/-- Number of complete three-axis final cycles in polynomial row `n`. -/
def mixedPolynomialRFinal (n : ℕ) : ℕ := polynomialFinalShots n

/-- Number of final binary observations in polynomial row `n`. -/
def mixedPolynomialTFinal (n : ℕ) : ℕ := 3 * mixedPolynomialRFinal n

@[simp] theorem mixedPolynomialQPilot_eq (n : ℕ) :
    mixedPolynomialQPilot n = (n + 1) ^ 5 := by
  simp [mixedPolynomialQPilot, polynomialPilotBlocks, polynomialScheduleM]

@[simp] theorem mixedPolynomialRFinal_eq (n : ℕ) :
    mixedPolynomialRFinal n = (n + 1) ^ 6 := by
  simp [mixedPolynomialRFinal, polynomialFinalShots, polynomialScheduleM]

@[simp] theorem mixedPolynomialTFinal_eq (n : ℕ) :
    mixedPolynomialTFinal n = 3 * (n + 1) ^ 6 := by
  simp [mixedPolynomialTFinal]

theorem mixedPolynomialQPilot_pos (n : ℕ) : 0 < mixedPolynomialQPilot n := by
  rw [mixedPolynomialQPilot_eq]
  positivity

theorem mixedPolynomialRFinal_pos (n : ℕ) : 0 < mixedPolynomialRFinal n := by
  rw [mixedPolynomialRFinal_eq]
  positivity

/-- The finite empirical three-coordinate Pauli estimator in row `n`. -/
def mixedPolynomialFinitePilotEstimator (n : ℕ)
    (path : PauliPilotPath (mixedPolynomialQPilot n)) : Fin 3 → ℝ :=
  pauliPilotEstimate path

/-- The bad pilot event is the union of the three coordinate deviations at
threshold `(n+1)⁻²`. -/
def mixedPolynomialFinitePilotBadEvent (theta : Fin 3 → ℝ) (n : ℕ) :
    Set (PauliPilotPath (mixedPolynomialQPilot n)) :=
  {path | ∃ j : Fin 3,
    polynomialPilotThreshold n ≤
      |mixedPolynomialFinitePilotEstimator n path j - theta j|}

/-- One coordinate of the row-`n` bad pilot event. -/
def mixedPolynomialFinitePilotCoordinateBadEvent
    (theta : Fin 3 → ℝ) (n : ℕ) (j : Fin 3) :
    Set (PauliPilotPath (mixedPolynomialQPilot n)) :=
  {path | polynomialPilotThreshold n ≤
    |mixedPolynomialFinitePilotEstimator n path j - theta j|}

theorem mixedPolynomialPilotThreshold_pos (n : ℕ) :
    0 < polynomialPilotThreshold n := by
  unfold polynomialPilotThreshold polynomialScheduleM
  positivity

theorem mixedPolynomialFinitePilotEstimator_coordinate_lt_of_good
    (theta : Fin 3 → ℝ) (n : ℕ)
    (path : PauliPilotPath (mixedPolynomialQPilot n))
    (hgood : path ∉ mixedPolynomialFinitePilotBadEvent theta n)
    (j : Fin 3) :
    |mixedPolynomialFinitePilotEstimator n path j - theta j| <
      polynomialPilotThreshold n := by
  by_contra hnot
  apply hgood
  exact ⟨j, le_of_not_gt hnot⟩

/-- The pilot-dependent final frame.  The bounded fallback in
`mixedPilotSelectedLocalFrame` makes this a physical orthonormal frame for
*every* pilot path, not only on the good event. -/
noncomputable def mixedPolynomialPilotSelectedFinalFrame
    (b : Fin 3 → ℝ) (n : ℕ) :
    PilotSelectedFinalFrame (mixedPolynomialQPilot n) where
  frame path :=
    mixedPilotSelectedLocalFrame b
      (mixedPolynomialFinitePilotEstimator n path)
  axis_unit path k := by
    change blochNormSq
      (qubitFrameAxis
        (mixedPilotSelectedLocalFrame b
          (mixedPolynomialFinitePilotEstimator n path)) k) = 1
    exact mixedPilotSelectedLocalFrame_axis_unit b
      (mixedPolynomialFinitePilotEstimator n path) k
  axes_orthogonal path k l := by
    change blochDot
      (qubitFrameAxis
        (mixedPilotSelectedLocalFrame b
          (mixedPolynomialFinitePilotEstimator n path)) k)
      (qubitFrameAxis
        (mixedPilotSelectedLocalFrame b
          (mixedPolynomialFinitePilotEstimator n path)) l) =
        if k = l then 1 else 0
    exact mixedPilotSelectedLocalFrame_axes_orthogonal b
      (mixedPolynomialFinitePilotEstimator n path) k l

/-- Directional Fisher information averaged over one complete three-axis
frame cycle. -/
def mixedPolynomialFrameDirectionalInformation
    (theta h : Fin 3 → ℝ) (R : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  (1 / 3 : ℝ) * ∑ k : Fin 3,
    (blochDot h (mixedTwoStageFrameAxis R k)) ^ 2 /
      (1 - (blochDot theta (mixedTwoStageFrameAxis R k)) ^ 2)

/-- The limiting directional information evaluated in the continuous local
frame at the true Bloch vector. -/
def mixedPolynomialTruthFrameDirectionalInformation
    (theta h b : Fin 3 → ℝ) : ℝ :=
  mixedPolynomialFrameDirectionalInformation theta h
    (localContinuousQubitFrame b theta)

/-- The normalized exact finite-row information, defined from all final
observations rather than directly from the three-column formula. -/
def mixedPolynomialNormalizedDirectionalInformation
    (theta h b : Fin 3 → ℝ) (n : ℕ)
    (path : PauliPilotPath (mixedPolynomialQPilot n)) : ℝ :=
  (∑ t : Fin (mixedPolynomialTFinal n),
      mixedTwoStageFinalDirectionalFisherTerm theta h
        (mixedPolynomialPilotSelectedFinalFrame b n) path t) /
    (mixedPolynomialTFinal n : ℝ)

/-- Exact-cycle reduction of the row information to the average over the
three pilot-selected frame columns. -/
theorem mixedPolynomialNormalizedDirectionalInformation_eq_frameInformation
    (theta h b : Fin 3 → ℝ) (n : ℕ)
    (path : PauliPilotPath (mixedPolynomialQPilot n)) :
    mixedPolynomialNormalizedDirectionalInformation theta h b n path =
      mixedPolynomialFrameDirectionalInformation theta h
        (mixedPilotSelectedLocalFrame b
          (mixedPolynomialFinitePilotEstimator n path)) := by
  calc
    mixedPolynomialNormalizedDirectionalInformation theta h b n path =
        (1 / 3 : ℝ) * ∑ k : Fin 3,
          mixedTwoStageFrameColumnDirectionalFisherTerm theta h
            (mixedPolynomialPilotSelectedFinalFrame b n) path k := by
      unfold mixedPolynomialNormalizedDirectionalInformation
        mixedPolynomialTFinal
      exact mixedTwoStageExactCycleInformation_normalized
        (r := mixedPolynomialRFinal n)
        (mixedPolynomialRFinal_pos n) theta h
        (mixedPolynomialPilotSelectedFinalFrame b n) path
    _ = mixedPolynomialFrameDirectionalInformation theta h
        (mixedPilotSelectedLocalFrame b
          (mixedPolynomialFinitePilotEstimator n path)) := by
      rfl

private theorem mixedPolynomial_selectedFrameAxis_dot_tendsto
    (b theta v : Fin 3 → ℝ) (xHat : ℕ → Fin 3 → ℝ)
    (hx : ∀ j : Fin 3,
      Tendsto (fun n => xHat n j) atTop (nhds (theta j)))
    (hTruthPositive : 0 < blochNormSq theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (k : Fin 3) :
    Tendsto
      (fun n => blochDot v
        (mixedTwoStageFrameAxis
          (mixedPilotSelectedLocalFrame b (xHat n)) k))
      atTop
      (nhds (blochDot v
        (mixedTwoStageFrameAxis
          (localContinuousQubitFrame b theta) k))) := by
  unfold blochDot mixedTwoStageFrameAxis
  apply tendsto_finset_sum
  intro i hi
  exact tendsto_const_nhds.mul
    (mixedPilotSelectedLocalFrame_entry_tendsto_of_coordinatewise
      b xHat theta hx hTruthPositive hSeed i k)

/-- Coordinatewise consistency of a pilot estimate implies convergence of the
complete-cycle directional information.  Interior physicality is used only to
keep the three limiting Bernoulli Fisher denominators strictly positive. -/
theorem mixedPolynomialFrameDirectionalInformation_tendsto_of_coordinatewise
    (b theta h : Fin 3 → ℝ) (xHat : ℕ → Fin 3 → ℝ)
    (hx : ∀ j : Fin 3,
      Tendsto (fun n => xHat n j) atTop (nhds (theta j)))
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    Tendsto
      (fun n => mixedPolynomialFrameDirectionalInformation theta h
        (mixedPilotSelectedLocalFrame b (xHat n)))
      atTop
      (nhds (mixedPolynomialTruthFrameDirectionalInformation theta h b)) := by
  have hDomain : LocalContinuousFrameDomain b theta := ⟨hTruth.1, hSeed⟩
  have hterm : ∀ k : Fin 3,
      Tendsto
        (fun n =>
          (blochDot h
              (mixedTwoStageFrameAxis
                (mixedPilotSelectedLocalFrame b (xHat n)) k)) ^ 2 /
            (1 - (blochDot theta
              (mixedTwoStageFrameAxis
                (mixedPilotSelectedLocalFrame b (xHat n)) k)) ^ 2))
        atTop
        (nhds
          ((blochDot h
              (mixedTwoStageFrameAxis
                (localContinuousQubitFrame b theta) k)) ^ 2 /
            (1 - (blochDot theta
              (mixedTwoStageFrameAxis
                (localContinuousQubitFrame b theta) k)) ^ 2))) := by
    intro k
    have hh := mixedPolynomial_selectedFrameAxis_dot_tendsto
      b theta h xHat hx hTruth.1 hSeed k
    have htheta := mixedPolynomial_selectedFrameAxis_dot_tendsto
      b theta theta xHat hx hTruth.1 hSeed k
    have hunit :
        blochNormSq
          (mixedTwoStageFrameAxis
            (localContinuousQubitFrame b theta) k) = 1 := by
      change blochNormSq
        (qubitFrameAxis (localContinuousQubitFrame b theta) k) = 1
      exact localContinuousQubitFrame_axis_unit hDomain k
    have hden_pos :
        0 < 1 - (blochDot theta
          (mixedTwoStageFrameAxis
            (localContinuousQubitFrame b theta) k)) ^ 2 :=
      mixedTwoStageAxisFisherDenominator_pos theta
        (mixedTwoStageFrameAxis
          (localContinuousQubitFrame b theta) k) hTruth.2 hunit
    exact (hh.pow 2).div
      (tendsto_const_nhds.sub (htheta.pow 2)) (ne_of_gt hden_pos)
  unfold mixedPolynomialFrameDirectionalInformation
    mixedPolynomialTruthFrameDirectionalInformation
  apply tendsto_const_nhds.mul
  apply tendsto_finset_sum
  intro k hk
  exact hterm k

/-- A dependent triangular subsequence of good finite pilot paths has a
coordinatewise consistent pilot estimate. -/
theorem mixedPolynomialFinitePilotEstimator_coordinatewise_tendsto_on_goodSubsequence
    (theta : Fin 3 → ℝ) (index : ℕ → ℕ)
    (hindex : Tendsto index atTop atTop)
    (path : ∀ k : ℕ, PauliPilotPath (mixedPolynomialQPilot (index k)))
    (hgood : ∀ k : ℕ,
      path k ∉ mixedPolynomialFinitePilotBadEvent theta (index k))
    (j : Fin 3) :
    Tendsto
      (fun k => mixedPolynomialFinitePilotEstimator (index k) (path k) j)
      atTop (nhds (theta j)) := by
  have hthreshold :
      Tendsto (fun k => polynomialPilotThreshold (index k))
        atTop (nhds 0) :=
    polynomialPilotThreshold_tendsto_zero.comp hindex
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  have heventually : ∀ᶠ k in atTop,
      polynomialPilotThreshold (index k) < epsilon :=
    (tendsto_order.1 hthreshold).2 epsilon hepsilon
  rcases (eventually_atTop.1 heventually) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro k hk
  rw [Real.dist_eq]
  exact lt_trans
    (mixedPolynomialFinitePilotEstimator_coordinate_lt_of_good
      theta (index k) (path k) (hgood k) j) (hN k hk)

/-- Deterministic convergence of exact-cycle information along every good
triangular subsequence. -/
theorem mixedPolynomialNormalizedDirectionalInformation_tendsto_on_goodSubsequence
    (b theta h : Fin 3 → ℝ) (index : ℕ → ℕ)
    (hindex : Tendsto index atTop atTop)
    (path : ∀ k : ℕ, PauliPilotPath (mixedPolynomialQPilot (index k)))
    (hgood : ∀ k : ℕ,
      path k ∉ mixedPolynomialFinitePilotBadEvent theta (index k))
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    Tendsto
      (fun k => mixedPolynomialNormalizedDirectionalInformation
        theta h b (index k) (path k))
      atTop
      (nhds (mixedPolynomialTruthFrameDirectionalInformation theta h b)) := by
  have hx : ∀ j : Fin 3,
      Tendsto
        (fun k => mixedPolynomialFinitePilotEstimator (index k) (path k) j)
        atTop (nhds (theta j)) := by
    intro j
    exact mixedPolynomialFinitePilotEstimator_coordinatewise_tendsto_on_goodSubsequence
      theta index hindex path hgood j
  have hframe :=
    mixedPolynomialFrameDirectionalInformation_tendsto_of_coordinatewise
      b theta h
      (fun k => mixedPolynomialFinitePilotEstimator (index k) (path k))
      hx hTruth hSeed
  simpa only
    [mixedPolynomialNormalizedDirectionalInformation_eq_frameInformation]
    using hframe

/-- Uniform deterministic convergence over the whole row-specific pilot good
event.  This follows by a sequential contradiction and therefore remains valid
although the finite sample space changes with `n`. -/
theorem mixedPolynomialNormalizedDirectionalInformation_uniform_on_goodEvent
    (b theta h : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ n in atTop, ∀ path : PauliPilotPath (mixedPolynomialQPilot n),
      path ∉ mixedPolynomialFinitePilotBadEvent theta n →
      |mixedPolynomialNormalizedDirectionalInformation theta h b n path -
        mixedPolynomialTruthFrameDirectionalInformation theta h b| < epsilon := by
  by_contra hUniform
  have hfar : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∃ path : PauliPilotPath (mixedPolynomialQPilot n),
        path ∉ mixedPolynomialFinitePilotBadEvent theta n ∧
        epsilon ≤
          |mixedPolynomialNormalizedDirectionalInformation theta h b n path -
            mixedPolynomialTruthFrameDirectionalInformation theta h b| := by
    intro N
    by_contra hN
    push_neg at hN
    apply hUniform
    filter_upwards [eventually_ge_atTop N] with n hn
    intro path hgood
    exact hN n hn path hgood
  choose index hindex_ge hbadIndex using hfar
  choose path hpath_good hpath_far using hbadIndex
  have hindex : Tendsto index atTop atTop := by
    apply tendsto_atTop.2
    intro N
    filter_upwards [eventually_ge_atTop N] with k hk
    exact le_trans hk (hindex_ge k)
  have hinfo :=
    mixedPolynomialNormalizedDirectionalInformation_tendsto_on_goodSubsequence
      b theta h index hindex path hpath_good hTruth hSeed
  have habs :
      Tendsto
        (fun k =>
          |mixedPolynomialNormalizedDirectionalInformation
              theta h b (index k) (path k) -
            mixedPolynomialTruthFrameDirectionalInformation theta h b|)
        atTop (nhds 0) := by
    have hconst : Tendsto
        (fun _ : ℕ =>
          mixedPolynomialTruthFrameDirectionalInformation theta h b)
        atTop
        (nhds (mixedPolynomialTruthFrameDirectionalInformation theta h b)) :=
      tendsto_const_nhds
    simpa using (hinfo.sub hconst).abs
  have hnear : ∀ᶠ k in atTop,
      |mixedPolynomialNormalizedDirectionalInformation
          theta h b (index k) (path k) -
        mixedPolynomialTruthFrameDirectionalInformation theta h b| < epsilon :=
    (tendsto_order.1 habs).2 epsilon hepsilon
  rcases (eventually_atTop.1 hnear) with ⟨K, hK⟩
  exact (not_le_of_gt (hK K le_rfl)) (hpath_far K)

/-- Exact row-wise Hoeffding hypotheses.  This is a contract parameter, not an
axiom: each field is precisely the already isolated positive and negated
Hoeffding-Theorem-2 conclusion for one finite Born product row. -/
def MixedPolynomialFinitePilotHoeffdingContracts
    (theta : Fin 3 → ℝ) (hphysical : blochNormSq theta ≤ 1) : Prop :=
  ∀ n : ℕ, ∀ j : Fin 3,
    PauliPilotBornTwoSidedHoeffdingTheorem2Contract
      (q := mixedPolynomialQPilot n) (mixedPolynomialQPilot_pos n)
      theta hphysical j

/-- Common coordinate tail envelope before simplifying the polynomial
schedule. -/
def mixedPolynomialFinitePilotCoordinateEnvelope (n : ℕ) : ENNReal :=
  2 * ENNReal.ofReal
    (Real.exp
      (-((mixedPolynomialQPilot n : ℝ) *
        (polynomialPilotThreshold n) ^ 2) / 2))

/-- Three-coordinate union-bound envelope in row `n`. -/
def mixedPolynomialFinitePilotBadEventEnvelope (n : ℕ) : ENNReal :=
  3 * mixedPolynomialFinitePilotCoordinateEnvelope n

/-- One finite-row coordinate tail is bounded directly by the paired
Hoeffding contract for that row and coordinate. -/
theorem mixedPolynomialFinitePilotCoordinateBadEvent_measure_le
    (theta : Fin 3 → ℝ) (hphysical : blochNormSq theta ≤ 1)
    (hHoeffding : MixedPolynomialFinitePilotHoeffdingContracts theta hphysical)
    (n : ℕ) (j : Fin 3) :
    pauliPilotBornProductMeasure (q := mixedPolynomialQPilot n) theta
        (mixedPolynomialFinitePilotCoordinateBadEvent theta n j) ≤
      mixedPolynomialFinitePilotCoordinateEnvelope n := by
  simpa [mixedPolynomialFinitePilotCoordinateBadEvent,
    mixedPolynomialFinitePilotEstimator,
    mixedPolynomialFinitePilotCoordinateEnvelope] using
    (pauliPilotBorn_twoSidedTail_of_hoeffding2
      (q := mixedPolynomialQPilot n) (mixedPolynomialQPilot_pos n)
      theta hphysical j (hHoeffding n j)
      (polynomialPilotThreshold n)
      (mixedPolynomialPilotThreshold_pos n))

/-- Explicit union bound for the three-coordinate finite pilot bad event. -/
theorem mixedPolynomialFinitePilotBadEvent_measure_le
    (theta : Fin 3 → ℝ) (hphysical : blochNormSq theta ≤ 1)
    (hHoeffding : MixedPolynomialFinitePilotHoeffdingContracts theta hphysical)
    (n : ℕ) :
    pauliPilotBornProductMeasure (q := mixedPolynomialQPilot n) theta
        (mixedPolynomialFinitePilotBadEvent theta n) ≤
      mixedPolynomialFinitePilotBadEventEnvelope n := by
  let E0 := mixedPolynomialFinitePilotCoordinateBadEvent theta n (0 : Fin 3)
  let E1 := mixedPolynomialFinitePilotCoordinateBadEvent theta n (1 : Fin 3)
  let E2 := mixedPolynomialFinitePilotCoordinateBadEvent theta n (2 : Fin 3)
  have hsubset :
      mixedPolynomialFinitePilotBadEvent theta n ⊆ E0 ∪ (E1 ∪ E2) := by
    intro path hpath
    change ∃ j : Fin 3,
      polynomialPilotThreshold n ≤
        |mixedPolynomialFinitePilotEstimator n path j - theta j| at hpath
    rcases hpath with ⟨j, hj⟩
    change path ∈ E0 ∪ (E1 ∪ E2)
    simp only [Set.mem_union]
    fin_cases j
    · left
      simpa [E0, mixedPolynomialFinitePilotCoordinateBadEvent] using hj
    · right
      left
      simpa [E1, mixedPolynomialFinitePilotCoordinateBadEvent] using hj
    · right
      right
      simpa [E2, mixedPolynomialFinitePilotCoordinateBadEvent] using hj
  have h0 := mixedPolynomialFinitePilotCoordinateBadEvent_measure_le
    theta hphysical hHoeffding n (0 : Fin 3)
  have h1 := mixedPolynomialFinitePilotCoordinateBadEvent_measure_le
    theta hphysical hHoeffding n (1 : Fin 3)
  have h2 := mixedPolynomialFinitePilotCoordinateBadEvent_measure_le
    theta hphysical hHoeffding n (2 : Fin 3)
  calc
    pauliPilotBornProductMeasure (q := mixedPolynomialQPilot n) theta
        (mixedPolynomialFinitePilotBadEvent theta n) ≤
      pauliPilotBornProductMeasure (q := mixedPolynomialQPilot n) theta
        (E0 ∪ (E1 ∪ E2)) := measure_mono hsubset
    _ ≤ pauliPilotBornProductMeasure (q := mixedPolynomialQPilot n) theta E0 +
        (pauliPilotBornProductMeasure (q := mixedPolynomialQPilot n) theta E1 +
          pauliPilotBornProductMeasure (q := mixedPolynomialQPilot n) theta E2) := by
      calc
        _ ≤ pauliPilotBornProductMeasure (q := mixedPolynomialQPilot n) theta E0 +
            pauliPilotBornProductMeasure (q := mixedPolynomialQPilot n) theta
              (E1 ∪ E2) := measure_union_le _ _
        _ ≤ pauliPilotBornProductMeasure (q := mixedPolynomialQPilot n) theta E0 +
            (pauliPilotBornProductMeasure (q := mixedPolynomialQPilot n) theta E1 +
              pauliPilotBornProductMeasure (q := mixedPolynomialQPilot n) theta E2) :=
          add_le_add le_rfl
            (measure_union_le
              (μ := pauliPilotBornProductMeasure
                (q := mixedPolynomialQPilot n) theta) E1 E2)
    _ ≤ mixedPolynomialFinitePilotCoordinateEnvelope n +
        (mixedPolynomialFinitePilotCoordinateEnvelope n +
          mixedPolynomialFinitePilotCoordinateEnvelope n) := by
      exact add_le_add h0 (add_le_add h1 h2)
    _ = mixedPolynomialFinitePilotBadEventEnvelope n := by
      unfold mixedPolynomialFinitePilotBadEventEnvelope
      ring

/-- For the chosen fifth/squared-threshold schedule, the finite-row union
bound is exactly `6 exp(-(n+1)/2)`. -/
theorem mixedPolynomialFinitePilotBadEventEnvelope_eq
    (n : ℕ) :
    mixedPolynomialFinitePilotBadEventEnvelope n =
      polynomialPilotBadEventEnvelope n := by
  have hmne : (polynomialScheduleM n : ℝ) ≠ 0 := by
    apply ne_of_gt
    rw [polynomialScheduleM]
    positivity
  have hcollapse :
      -((mixedPolynomialQPilot n : ℝ) *
          (polynomialPilotThreshold n) ^ 2) / 2 =
        -((polynomialScheduleM n : ℝ) / 2) := by
    simp only [mixedPolynomialQPilot, polynomialPilotBlocks,
      polynomialPilotThreshold]
    push_cast
    field_simp [hmne]
    <;> ring
  unfold mixedPolynomialFinitePilotBadEventEnvelope
    mixedPolynomialFinitePilotCoordinateEnvelope
    polynomialPilotBadEventEnvelope
  rw [hcollapse]
  ring

theorem mixedPolynomialFinitePilotBadEventEnvelope_tendsto_zero :
    Tendsto mixedPolynomialFinitePilotBadEventEnvelope atTop (nhds 0) := by
  refine polynomialPilotBadEventEnvelope_tendsto_zero.congr' ?_
  exact Filter.Eventually.of_forall
    (fun n => (mixedPolynomialFinitePilotBadEventEnvelope_eq n).symm)

/-- Triangular-row convergence in probability.  The probability measure and
finite pilot sample space are both allowed to depend on the row. -/
def MixedPolynomialDirectionalInformationConvergesInProbability
    (theta h b : Fin 3 → ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    Tendsto
      (fun n =>
        pauliPilotBornProductMeasure (q := mixedPolynomialQPilot n) theta
          {path |
            epsilon ≤
              |mixedPolynomialNormalizedDirectionalInformation
                  theta h b n path -
                mixedPolynomialTruthFrameDirectionalInformation theta h b|})
      atTop (nhds 0)

/-- Closed concrete information-convergence endpoint for the polynomial
mixed-qubit two-stage protocol.  Its only probabilistic premise is the exact
paired finite-row Hoeffding contract already isolated from the literature;
there is no common-space or infinite-pilot bridge premise. -/
theorem mixedPolynomialNormalizedDirectionalInformation_convergesInProbability
    (b theta h : Fin 3 → ℝ)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hHoeffding : MixedPolynomialFinitePilotHoeffdingContracts theta
      (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)) :
    MixedPolynomialDirectionalInformationConvergesInProbability theta h b := by
  intro epsilon hepsilon
  have huniform :=
    mixedPolynomialNormalizedDirectionalInformation_uniform_on_goodEvent
      b theta h hTruth hSeed epsilon hepsilon
  have hEnvelope :=
    mixedPolynomialFinitePilotBadEventEnvelope_tendsto_zero
  apply tendsto_order.2
  constructor
  · intro a ha
    exact (not_lt_of_ge bot_le ha).elim
  · intro a ha
    have hEnvelope_lt : ∀ᶠ n in atTop,
        mixedPolynomialFinitePilotBadEventEnvelope n < a :=
      (tendsto_order.1 hEnvelope).2 a ha
    filter_upwards [huniform, hEnvelope_lt] with n hgoodRow hEnvelopeRow
    calc
      pauliPilotBornProductMeasure (q := mixedPolynomialQPilot n) theta
          {path |
            epsilon ≤
              |mixedPolynomialNormalizedDirectionalInformation
                  theta h b n path -
                mixedPolynomialTruthFrameDirectionalInformation theta h b|} ≤
        pauliPilotBornProductMeasure (q := mixedPolynomialQPilot n) theta
          (mixedPolynomialFinitePilotBadEvent theta n) := by
            apply measure_mono
            intro path hpath
            by_contra hnotBad
            exact (not_lt_of_ge hpath) (hgoodRow path hnotBad)
      _ ≤ mixedPolynomialFinitePilotBadEventEnvelope n :=
        mixedPolynomialFinitePilotBadEvent_measure_le theta
          (mixedNonzeroInterior_pauliPilotPhysical theta hTruth)
          hHoeffding n
      _ < a := hEnvelopeRow

end

end QubitOracle.Paper
