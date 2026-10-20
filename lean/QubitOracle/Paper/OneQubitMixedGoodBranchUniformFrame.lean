import QubitOracle.Paper.OneQubitMixedPilotFrameRiskTransfer

/-!
# Uniform good-branch reduction for the mixed pilot frame

Only the deterministic good branch is considered.  The final signed sample
means have already been integrated out by `pauliPilotFiniteExpectation`.
No pilot/final joint law and no uniform-integrability premise is used here.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace QubitOracle.Paper

noncomputable section

/-- Coordinate error of the three equal-allocation signed sample means. -/
def mixedPauliCoordinateError
    {q : ℕ} (z : RLSVector 3) (path : PauliPilotPath q) : RLSVector 3 :=
  fun j => pauliPilotEstimate path j - z j

/-- Expected squared Euclidean coordinate error. -/
theorem pauliPilotCoordinateError_normSq_mean
    {q : ℕ} (hq : 0 < q) (z : RLSVector 3) :
    pauliPilotFiniteExpectation (q := q) z
        (fun path : PauliPilotPath q => QubitOracle.blochNormSq
          (mixedPauliCoordinateError z path)) =
      ∑ j : Fin 3, (1 - z j ^ 2) / (q : ℝ) := by
  unfold QubitOracle.blochNormSq
  rw [pauliPilotFiniteExpectation_fintype_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact pauliPilotEstimate_coordinateVariance hq z j

/-- Expected square of any fixed scalar projection of the coordinate error.
The off-diagonal terms vanish by the exact covariance theorem. -/
theorem pauliPilotCoordinateError_projected_sq_mean
    {q : ℕ} (hq : 0 < q) (z a : RLSVector 3) :
    pauliPilotFiniteExpectation (q := q) z
        (fun path : PauliPilotPath q => QubitOracle.blochDot a
          (mixedPauliCoordinateError z path) ^ 2) =
      ∑ j : Fin 3, a j ^ 2 * (1 - z j ^ 2) / (q : ℝ) := by
  have hexpand :
      (fun path : PauliPilotPath q =>
        QubitOracle.blochDot a (mixedPauliCoordinateError z path) ^ 2) =
      (fun path : PauliPilotPath q =>
        ∑ j : Fin 3, ∑ k : Fin 3,
          (a j * a k) *
            ((pauliPilotEstimate path j - z j) *
              (pauliPilotEstimate path k - z k))) := by
    funext path
    simp [QubitOracle.blochDot, mixedPauliCoordinateError,
      Fin.sum_univ_succ]
    ring
  rw [hexpand, pauliPilotFiniteExpectation_fintype_sum]
  simp_rw [pauliPilotFiniteExpectation_fintype_sum,
    pauliPilotFiniteExpectation_const_mul,
    pauliPilotEstimate_covariance hq z]
  simp [Fin.sum_univ_succ]
  ring

/-- Closed form of the equal-allocation scaled conditional quadratic risk.
It contains no final block count. -/
def mixedFrameScaledQuadraticRiskClosedForm
    (theta : RLSVector 3)
    (R : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  let z := qubitFrameCoordinates R theta
  (3 / 4 : ℝ) *
    ((∑ j : Fin 3, (1 - z j ^ 2)) +
      (∑ j : Fin 3, z j ^ 2 * (1 - z j ^ 2)) /
        (1 - QubitOracle.blochNormSq theta))

/-- Rotational covariance rewrites the reconstructed local quadratic loss as
its coordinate-frame quadratic form. -/
theorem mixedInteriorBuresQuadraticLoss_linearEstimate_eq
    {q : ℕ} (theta : RLSVector 3)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : MixedFrameOrthonormal R) (path : PauliPilotPath q) :
    mixedInteriorBuresQuadraticLoss theta
        (fun i => mixedFrameLinearEstimate R path i - theta i) =
      (4 : ℝ)⁻¹ * QubitOracle.blochNormSq
          (mixedPauliCoordinateError (qubitFrameCoordinates R theta) path) +
        (4 * (1 - QubitOracle.blochNormSq theta))⁻¹ *
          QubitOracle.blochDot (qubitFrameCoordinates R theta)
            (mixedPauliCoordinateError
              (qubitFrameCoordinates R theta) path) ^ 2 := by
  rw [mixedFrameLinearEstimate_sub_truth R hR theta path]
  unfold mixedInteriorBuresQuadraticLoss
  rw [mixedFrameReconstruct_normSq R hR]
  rw [mixedFrame_blochDot_reconstruct R]
  rfl

/-- Exact cancellation of the positive equal-allocation count `q`.  This is
the deterministic conditional-risk calculation needed before any pilot-law
averaging. -/
theorem mixedFrameConditionalScaledQuadraticRisk_eq_closedForm
    {q : ℕ} (hq : 0 < q) (theta : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : MixedFrameOrthonormal R) :
    mixedFrameConditionalScaledQuadraticRisk (q := q) theta R =
      mixedFrameScaledQuadraticRiskClosedForm theta R := by
  let z : RLSVector 3 := qubitFrameCoordinates R theta
  have hloss :
      (fun path : PauliPilotPath q =>
        mixedInteriorBuresQuadraticLoss theta
          (fun i => mixedFrameLinearEstimate R path i - theta i)) =
      (fun path : PauliPilotPath q =>
        (4 : ℝ)⁻¹ * QubitOracle.blochNormSq
            (mixedPauliCoordinateError z path) +
          (4 * (1 - QubitOracle.blochNormSq theta))⁻¹ *
            QubitOracle.blochDot z
              (mixedPauliCoordinateError z path) ^ 2) := by
    funext path
    simpa [z] using
      mixedInteriorBuresQuadraticLoss_linearEstimate_eq theta R hR path
  unfold mixedFrameConditionalScaledQuadraticRisk
    mixedFrameConditionalQuadraticRisk
  rw [hloss, pauliPilotFiniteExpectation_add,
    pauliPilotFiniteExpectation_const_mul,
    pauliPilotFiniteExpectation_const_mul,
    pauliPilotCoordinateError_normSq_mean hq z,
    pauliPilotCoordinateError_projected_sq_mean hq z z]
  unfold mixedFrameScaledQuadraticRiskClosedForm
  dsimp only [z]
  have hqReal : (q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hq)
  have hden : 1 - QubitOracle.blochNormSq theta ≠ 0 := by
    linarith
  rw [← Finset.sum_div, ← Finset.sum_div]
  field_simp [hqReal, hden]

/-- The closed conditional risk is continuous in all nine frame entries. -/
theorem mixedFrameScaledQuadraticRiskClosedForm_continuous
    (theta : RLSVector 3) :
    Continuous
      (fun R : Matrix (Fin 3) (Fin 3) ℝ =>
        mixedFrameScaledQuadraticRiskClosedForm theta R) := by
  unfold mixedFrameScaledQuadraticRiskClosedForm
  unfold qubitFrameCoordinates QubitOracle.blochDot qubitFrameAxis
  fun_prop

/-- A nonzero Bloch vector is its radius times its normalized direction. -/
theorem mixedTruth_eq_radius_mul_normalized
    (theta : RLSVector 3)
    (hPositive : 0 < QubitOracle.blochNormSq theta) :
    theta = fun i =>
      Real.sqrt (QubitOracle.blochNormSq theta) *
        localNormalizedBlochDirection theta i := by
  funext i
  have hsqrt : Real.sqrt (QubitOracle.blochNormSq theta) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hPositive)
  unfold localNormalizedBlochDirection
  field_simp [hsqrt]

/-- At the truth-level local frame, the first two coordinates are tangent and
the third coordinate is the Bloch radius. -/
theorem localContinuousFrame_truth_coordinates
    (b theta : RLSVector 3)
    (hDomain : LocalContinuousFrameDomain b theta) (k : Fin 3) :
    qubitFrameCoordinates (localContinuousQubitFrame b theta) theta k =
      if k = (2 : Fin 3) then
        Real.sqrt (QubitOracle.blochNormSq theta) else 0 := by
  have htheta := mixedTruth_eq_radius_mul_normalized theta
    hDomain.radial_denominator_pos
  have horth := localContinuousQubitFrame_axes_orthogonal hDomain k (2 : Fin 3)
  rw [localContinuousQubitFrame_axis_two] at horth
  unfold qubitFrameCoordinates
  calc
    QubitOracle.blochDot
        (qubitFrameAxis (localContinuousQubitFrame b theta) k) theta =
      QubitOracle.blochDot
        (qubitFrameAxis (localContinuousQubitFrame b theta) k)
        (fun i => Real.sqrt (QubitOracle.blochNormSq theta) *
          localNormalizedBlochDirection theta i) :=
      congrArg
        (fun v : RLSVector 3 => QubitOracle.blochDot
          (qubitFrameAxis (localContinuousQubitFrame b theta) k) v)
        htheta
    _ = Real.sqrt (QubitOracle.blochNormSq theta) *
        QubitOracle.blochDot
          (qubitFrameAxis (localContinuousQubitFrame b theta) k)
          (localNormalizedBlochDirection theta) := by
            simp [QubitOracle.blochDot, Fin.sum_univ_succ]
            ring
    _ = Real.sqrt (QubitOracle.blochNormSq theta) *
        (if k = (2 : Fin 3) then 1 else 0) := by rw [horth]
    _ = if k = (2 : Fin 3) then
        Real.sqrt (QubitOracle.blochNormSq theta) else 0 := by
      by_cases hk : k = (2 : Fin 3) <;> simp [hk]

/-- The truth-level local frame has the canonical `9/4` scaled quadratic risk. -/
theorem mixedFrameScaledQuadraticRiskClosedForm_localTruth
    (b theta : RLSVector 3)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hDomain : LocalContinuousFrameDomain b theta) :
    mixedFrameScaledQuadraticRiskClosedForm theta
        (localContinuousQubitFrame b theta) = 9 / 4 := by
  have hsqrtSq :
      Real.sqrt (QubitOracle.blochNormSq theta) ^ 2 =
        QubitOracle.blochNormSq theta :=
    Real.sq_sqrt (le_of_lt hDomain.radial_denominator_pos)
  have hden : 1 - QubitOracle.blochNormSq theta ≠ 0 := by
    linarith
  unfold mixedFrameScaledQuadraticRiskClosedForm
  simp_rw [localContinuousFrame_truth_coordinates b theta hDomain]
  simp [Fin.sum_univ_succ, hsqrtSq]
  field_simp [hden]
  ring

/-- Entrywise convergence of frames implies convergence of the closed risk. -/
theorem mixedFrameScaledQuadraticRiskClosedForm_tendsto
    (theta : RLSVector 3)
    (R : ℕ → Matrix (Fin 3) (Fin 3) ℝ)
    (Rlim : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : ∀ i k, Tendsto (fun n => R n i k) atTop (nhds (Rlim i k))) :
    Tendsto
      (fun n => mixedFrameScaledQuadraticRiskClosedForm theta (R n))
      atTop (nhds (mixedFrameScaledQuadraticRiskClosedForm theta Rlim)) := by
  have hMatrix : Tendsto R atTop (nhds Rlim) := by
    change Tendsto (fun n i k => R n i k) atTop
      (nhds (fun i k => Rlim i k))
    rw [tendsto_pi_nhds]
    intro i
    rw [tendsto_pi_nhds]
    intro k
    exact hR i k
  exact
    (mixedFrameScaledQuadraticRiskClosedForm_continuous theta).continuousAt.tendsto.comp
      hMatrix

/-- Sequential good-frame continuity, with exact independence from the
positive sequence of final equal-allocation block counts. -/
theorem mixedFrameConditionalScaledRisk_tendsto_of_coordinatewise
    (b theta : RLSVector 3) (xHat : ℕ → RLSVector 3)
    (qFinal : ℕ → ℕ) (hqFinal : ∀ n, 0 < qFinal n)
    (hx : ∀ j, Tendsto (fun n => xHat n j) atTop (nhds (theta j)))
    (hPositive : 0 < QubitOracle.blochNormSq theta)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    Tendsto
      (fun n => mixedFrameConditionalScaledQuadraticRisk
        (q := qFinal n) theta (mixedPilotSelectedLocalFrame b (xHat n)))
      atTop (nhds (9 / 4)) := by
  have hFrame (i k : Fin 3) :
      Tendsto
        (fun n => mixedPilotSelectedLocalFrame b (xHat n) i k)
        atTop (nhds (localContinuousQubitFrame b theta i k)) :=
    mixedPilotSelectedLocalFrame_entry_tendsto_of_coordinatewise
      b xHat theta hx hPositive hSeed i k
  have hClosed := mixedFrameScaledQuadraticRiskClosedForm_tendsto
    theta (fun n => mixedPilotSelectedLocalFrame b (xHat n))
      (localContinuousQubitFrame b theta) hFrame
  have hDomain : LocalContinuousFrameDomain b theta := ⟨hPositive, hSeed⟩
  rw [mixedFrameScaledQuadraticRiskClosedForm_localTruth
    b theta hInterior hDomain] at hClosed
  apply hClosed.congr'
  filter_upwards with n
  exact (mixedFrameConditionalScaledQuadraticRisk_eq_closedForm
    (hqFinal n) theta hInterior
    (mixedPilotSelectedLocalFrame b (xHat n))
    (mixedPilotSelectedLocalFrame_orthonormal b (xHat n))).symm

/-! ## Explicit polynomial good-event sequences -/

theorem polynomialPilotThreshold_tendsto_zero :
    Tendsto polynomialPilotThreshold atTop (nhds 0) := by
  have hM : Tendsto
      (fun n : ℕ => (polynomialScheduleM n : ℝ)) atTop atTop := by
    rw [tendsto_atTop]
    intro A
    filter_upwards
      [(tendsto_atTop.1 tendsto_natCast_atTop_atTop) A] with n hn
    calc
      A ≤ (n : ℝ) := hn
      _ ≤ (polynomialScheduleM n : ℝ) := by
        simp [polynomialScheduleM]
  have hinv : Tendsto
      (fun n : ℕ => (polynomialScheduleM n : ℝ)⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hM
  have hThreshold :
      polynomialPilotThreshold =
        fun n : ℕ => (polynomialScheduleM n : ℝ)⁻¹ *
          (polynomialScheduleM n : ℝ)⁻¹ := by
    funext n
    have hmPos : 0 < (polynomialScheduleM n : ℝ) := by
      dsimp [polynomialScheduleM]
      positivity
    have hm : (polynomialScheduleM n : ℝ) ≠ 0 := ne_of_gt hmPos
    unfold polynomialPilotThreshold
    field_simp [hm]
  rw [hThreshold]
  simpa using hinv.mul hinv

/-- Any sequence selecting one outcome from every scheduled good event has a
coordinatewise consistent pilot vector. -/
theorem polynomialPilotEstimator_coordinatewise_tendsto_on_good
    (theta : RLSVector 3)
    (omega : ℕ → PauliPilotConsistencySampleSpace)
    (hgood : ∀ n, omega n ∉ polynomialPilotBadEvent theta n)
    (j : Fin 3) :
    Tendsto
      (fun n => polynomialPilotEstimator n (omega n) j)
      atTop (nhds (theta j)) := by
  have hcoordinate (n : ℕ) :
      |polynomialPilotEstimator n (omega n) j - theta j| <
        polynomialPilotThreshold n := by
    by_contra hnot
    have hle : polynomialPilotThreshold n ≤
        |polynomialPilotEstimator n (omega n) j - theta j| :=
      le_of_not_gt hnot
    apply hgood n
    change ∃ k : Fin 3,
      polynomialPilotThreshold n ≤
        |polynomialPilotEstimator n (omega n) k - theta k|
    exact ⟨j, hle⟩
  have hlower : Tendsto (fun n => -polynomialPilotThreshold n)
      atTop (nhds 0) := by
    simpa using polynomialPilotThreshold_tendsto_zero.neg
  have hdiff : Tendsto
      (fun n => polynomialPilotEstimator n (omega n) j - theta j)
      atTop (nhds 0) := by
    exact Tendsto.squeeze hlower polynomialPilotThreshold_tendsto_zero
      (fun n => neg_le_of_abs_le (le_of_lt (hcoordinate n)))
      (fun n => le_of_abs_le (le_of_lt (hcoordinate n)))
  have hconst : Tendsto (fun _ : ℕ => theta j) atTop (nhds (theta j)) :=
    tendsto_const_nhds
  simpa only [sub_add_cancel, zero_add] using hdiff.add hconst

/-- Every sequence of good pilot outcomes has conditional scaled quadratic
risk tending to `9/4`.  This is the sequential contradiction input. -/
theorem mixedPolynomialPilot_goodSequence_scaledRisk_tendsto
    (b theta : RLSVector 3) (qFinal : ℕ → ℕ)
    (hqFinal : ∀ n, 0 < qFinal n)
    (hPositive : 0 < QubitOracle.blochNormSq theta)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (omega : ℕ → PauliPilotConsistencySampleSpace)
    (hgood : ∀ n, omega n ∉ polynomialPilotBadEvent theta n) :
    Tendsto
      (fun n => mixedFrameConditionalScaledQuadraticRisk
        (q := qFinal n) theta
        (mixedPilotSelectedLocalFrame b
          (polynomialPilotEstimator n (omega n))))
      atTop (nhds (9 / 4)) := by
  exact mixedFrameConditionalScaledRisk_tendsto_of_coordinatewise
    b theta (fun n => polynomialPilotEstimator n (omega n))
    qFinal hqFinal
    (fun j => polynomialPilotEstimator_coordinatewise_tendsto_on_good
      theta omega hgood j)
    hPositive hInterior hSeed

/-- Exact remaining deterministic selection lemma.  It is the classical
finite-dimensional sequential-contradiction step converting convergence along
every good selection into one common vanishing envelope over all good outcomes.
It is exposed as a `Prop`, not declared as an axiom and not silently assumed. -/
def MixedPilotGoodBranchSequentialEnvelopeExtraction
    (b theta : RLSVector 3) (qFinal : ℕ → ℕ) : Prop :=
  (∀ (omega : ℕ → PauliPilotConsistencySampleSpace),
      (∀ n, omega n ∉ polynomialPilotBadEvent theta n) →
      Tendsto
        (fun n => mixedFrameConditionalScaledQuadraticRisk
          (q := qFinal n) theta
          (mixedPilotSelectedLocalFrame b
            (polynomialPilotEstimator n (omega n))))
        atTop (nhds (9 / 4))) →
    MixedPilotGoodBranchUniformFrameContinuityPremise theta b qFinal

/-- Reduction of the requested good-branch premise to precisely the remaining
sequential-envelope extraction lemma. -/
theorem mixedPilotGoodBranchUniformFrameContinuity_of_sequentialExtraction
    (b theta : RLSVector 3) (qFinal : ℕ → ℕ)
    (hqFinal : ∀ n, 0 < qFinal n)
    (hPositive : 0 < QubitOracle.blochNormSq theta)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hExtraction : MixedPilotGoodBranchSequentialEnvelopeExtraction
      b theta qFinal) :
    MixedPilotGoodBranchUniformFrameContinuityPremise theta b qFinal := by
  apply hExtraction
  intro omega hgood
  exact mixedPolynomialPilot_goodSequence_scaledRisk_tendsto
    b theta qFinal hqFinal hPositive hInterior hSeed omega hgood

namespace Label

/-- Honest good-branch reduction.  The only premise not proved in this file is
the explicitly named sequential-envelope extraction lemma. -/
theorem lem_SI_mixed_good_branch_uniform_frame_qubit_reduction
    (b theta : RLSVector 3) (qFinal : ℕ → ℕ)
    (hqFinal : ∀ n, 0 < qFinal n)
    (hPositive : 0 < QubitOracle.blochNormSq theta)
    (hInterior : QubitOracle.blochNormSq theta < 1)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (hExtraction : MixedPilotGoodBranchSequentialEnvelopeExtraction
      b theta qFinal) :
    MixedPilotGoodBranchUniformFrameContinuityPremise theta b qFinal :=
  mixedPilotGoodBranchUniformFrameContinuity_of_sequentialExtraction
    b theta qFinal hqFinal hPositive hInterior hSeed hExtraction

end Label

end

end QubitOracle.Paper
