import QubitOracle.Paper.OneQubitMixedLinearEstimatorRisk
import QubitOracle.Paper.OneQubitPolynomialTwoStageSchedule
import QubitOracle.Paper.OneQubitLocalFrameDomainClosure
import QubitOracle.Paper.OneQubitMixedQuadraticLossCore

/-!
# Mixed-qubit pilot-frame risk transfer: deterministic reduction

This file deliberately stops before a fully adaptive expected-risk theorem.
It proves the frame covariance and continuity algebra available from the clean
one-qubit modules.  The missing pilot/final joint-law disintegration and the
uniform-integrability step are encoded only as named `Prop` boundaries; they
are not assumed by any conclusion in this file.

The physical Bures loss is not used.  `mixedInteriorBuresQuadraticLoss` below
is only its local interior quadratic comparator.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace QubitOracle.Paper

noncomputable section

/-- A square frame is orthonormal when its columns have Gram matrix one. -/
def MixedFrameOrthonormal
    (R : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  R.transpose * R = 1

/-- Truth-independent safeguarded controller: use the local Gram--Schmidt
frame when its two denominators are positive, and otherwise use the identity. -/
noncomputable def mixedPilotSelectedLocalFrame
    (b x : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := by
  classical
  exact if LocalContinuousFrameDomain b x then
    localContinuousQubitFrame b x
  else 1

/-- Every pilot-selected frame is orthonormal, including the safeguarded
identity branch. -/
theorem mixedPilotSelectedLocalFrame_axes_orthogonal
    (b x : Fin 3 → ℝ) (k l : Fin 3) :
    QubitOracle.blochDot
        (qubitFrameAxis (mixedPilotSelectedLocalFrame b x) k)
        (qubitFrameAxis (mixedPilotSelectedLocalFrame b x) l) =
      if k = l then 1 else 0 := by
  classical
  by_cases hDomain : LocalContinuousFrameDomain b x
  · simp [mixedPilotSelectedLocalFrame, hDomain,
      localContinuousQubitFrame_axes_orthogonal hDomain]
  · simp [mixedPilotSelectedLocalFrame, hDomain,
      identityQubitFrame_axes_orthogonal]

theorem mixedPilotSelectedLocalFrame_axis_unit
    (b x : Fin 3 → ℝ) (k : Fin 3) :
    QubitOracle.blochNormSq
        (qubitFrameAxis (mixedPilotSelectedLocalFrame b x) k) = 1 := by
  have h := mixedPilotSelectedLocalFrame_axes_orthogonal b x k k
  rw [if_pos rfl, blochDot_self_eq_blochNormSq] at h
  exact h

theorem mixedPilotSelectedLocalFrame_orthonormal
    (b x : Fin 3 → ℝ) :
    MixedFrameOrthonormal (mixedPilotSelectedLocalFrame b x) := by
  unfold MixedFrameOrthonormal
  ext k l
  have h := mixedPilotSelectedLocalFrame_axes_orthogonal b x k l
  simpa [Matrix.mul_apply, Matrix.one_apply, qubitFrameAxis,
    QubitOracle.blochDot] using h

/-- Reconstruction from three signed sample means in the selected frame. -/
def mixedFrameReconstruct
    (R : Matrix (Fin 3) (Fin 3) ℝ) (z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => ∑ k : Fin 3, R i k * z k

/-- Frame-coordinate analysis followed by synthesis is the identity. -/
theorem mixedFrameCoordinates_reconstruct
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : MixedFrameOrthonormal R) (z : Fin 3 → ℝ) :
    qubitFrameCoordinates R (mixedFrameReconstruct R z) = z := by
  have hColumns (k l : Fin 3) :
      QubitOracle.blochDot (qubitFrameAxis R k) (qubitFrameAxis R l) =
        if k = l then 1 else 0 := by
    have happly := congrArg
      (fun M : Matrix (Fin 3) (Fin 3) ℝ => M k l) hR
    simpa [MixedFrameOrthonormal, Matrix.mul_apply, Matrix.one_apply,
      qubitFrameAxis, QubitOracle.blochDot] using happly
  funext k
  calc
    qubitFrameCoordinates R (mixedFrameReconstruct R z) k =
        ∑ l : Fin 3,
          QubitOracle.blochDot (qubitFrameAxis R k)
            (qubitFrameAxis R l) * z l := by
              simp [qubitFrameCoordinates, mixedFrameReconstruct,
                qubitFrameAxis, QubitOracle.blochDot, Fin.sum_univ_succ]
              ring
    _ = ∑ l : Fin 3, (if k = l then 1 else 0) * z l := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [hColumns k l]
    _ = z k := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro l hl hlk
        simp [Ne.symm hlk]
      · simp

private theorem mixedFrame_rows_orthogonal
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : MixedFrameOrthonormal R) (i j : Fin 3) :
    (∑ k : Fin 3, R i k * R j k) = if i = j then 1 else 0 := by
  have hRows : R * R.transpose = 1 :=
    mul_eq_one_comm.mp hR
  have happly := congrArg
    (fun M : Matrix (Fin 3) (Fin 3) ℝ => M i j) hRows
  simpa [Matrix.mul_apply, Matrix.one_apply] using happly

/-- Synthesis after frame-coordinate analysis is also the identity. -/
theorem mixedFrameReconstruct_coordinates
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : MixedFrameOrthonormal R) (x : Fin 3 → ℝ) :
    mixedFrameReconstruct R (qubitFrameCoordinates R x) = x := by
  funext i
  calc
    mixedFrameReconstruct R (qubitFrameCoordinates R x) i =
        ∑ j : Fin 3, (∑ k : Fin 3, R i k * R j k) * x j := by
          simp [mixedFrameReconstruct, qubitFrameCoordinates,
            qubitFrameAxis, QubitOracle.blochDot, Fin.sum_univ_succ]
          ring
    _ = ∑ j : Fin 3, (if i = j then 1 else 0) * x j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [mixedFrame_rows_orthogonal R hR i j]
    _ = x i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j hj hji
        simp [Ne.symm hji]
      · simp

/-- Adjoint covariance of the Euclidean/Bloch pairing.  This identity does not
need orthonormality. -/
theorem mixedFrame_blochDot_reconstruct
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (x z : Fin 3 → ℝ) :
    QubitOracle.blochDot x (mixedFrameReconstruct R z) =
      QubitOracle.blochDot (qubitFrameCoordinates R x) z := by
  simp [mixedFrameReconstruct, qubitFrameCoordinates,
    qubitFrameAxis, QubitOracle.blochDot, Fin.sum_univ_succ]
  ring

/-- An orthonormal frame preserves squared Bloch norm. -/
theorem mixedFrameReconstruct_normSq
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : MixedFrameOrthonormal R) (z : Fin 3 → ℝ) :
    QubitOracle.blochNormSq (mixedFrameReconstruct R z) =
      QubitOracle.blochNormSq z := by
  calc
    QubitOracle.blochNormSq (mixedFrameReconstruct R z) =
        QubitOracle.blochDot (mixedFrameReconstruct R z)
          (mixedFrameReconstruct R z) :=
      (blochDot_self_eq_blochNormSq _).symm
    _ = QubitOracle.blochDot
        (qubitFrameCoordinates R (mixedFrameReconstruct R z)) z :=
      mixedFrame_blochDot_reconstruct R (mixedFrameReconstruct R z) z
    _ = QubitOracle.blochDot z z := by
      rw [mixedFrameCoordinates_reconstruct R hR z]
    _ = QubitOracle.blochNormSq z := blochDot_self_eq_blochNormSq z

theorem mixedFrameCoordinates_normSq
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : MixedFrameOrthonormal R) (theta : Fin 3 → ℝ) :
    QubitOracle.blochNormSq (qubitFrameCoordinates R theta) =
      QubitOracle.blochNormSq theta := by
  calc
    QubitOracle.blochNormSq (qubitFrameCoordinates R theta) =
        QubitOracle.blochNormSq
          (mixedFrameReconstruct R (qubitFrameCoordinates R theta)) :=
      (mixedFrameReconstruct_normSq R hR
        (qubitFrameCoordinates R theta)).symm
    _ = QubitOracle.blochNormSq theta := by
      rw [mixedFrameReconstruct_coordinates R hR theta]

/-- The physical Bloch condition is rotation/frame covariant. -/
theorem mixedFrameCoordinates_physical
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : MixedFrameOrthonormal R) (theta : RLSVector 3)
    (hphysical : PauliPilotPhysicalBloch theta) :
    PauliPilotPhysicalBloch (qubitFrameCoordinates R theta) := by
  unfold PauliPilotPhysicalBloch at hphysical ⊢
  change QubitOracle.blochNormSq (qubitFrameCoordinates R theta) ≤ 1
  rw [mixedFrameCoordinates_normSq R hR theta]
  exact hphysical

/-- Born probabilities in a rotated projective frame are exactly the ordinary
Pauli Born probabilities of the frame-coordinate Bloch vector. -/
theorem mixedFrameBornProbability_covariant
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (theta : RLSVector 3) (k : Fin 3) (outcome : Bool) :
    pauliBornProbability (qubitFrameCoordinates R theta) k outcome =
      (1 + pauliOutcomeSign outcome *
        QubitOracle.blochDot (qubitFrameAxis R k) theta) / 2 := by
  cases outcome <;>
    simp [pauliBornProbability, pauliOutcomeSign, qubitFrameCoordinates,
      sub_eq_add_neg]

/-- Linear reconstruction from the three final signed sample means. -/
def mixedFrameLinearEstimate
    {q : ℕ} (R : Matrix (Fin 3) (Fin 3) ℝ)
    (path : PauliPilotPath q) : RLSVector 3 :=
  mixedFrameReconstruct R (pauliPilotEstimate path)

/-- Exact reconstruction-error covariance identity. -/
theorem mixedFrameLinearEstimate_sub_truth
    {q : ℕ} (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : MixedFrameOrthonormal R)
    (theta : RLSVector 3) (path : PauliPilotPath q) :
    (fun i => mixedFrameLinearEstimate R path i - theta i) =
      mixedFrameReconstruct R
        (fun k => pauliPilotEstimate path k -
          qubitFrameCoordinates R theta k) := by
  have htruth := mixedFrameReconstruct_coordinates R hR theta
  funext i
  rw [← congrFun htruth i]
  simp [mixedFrameLinearEstimate, mixedFrameReconstruct,
    mul_sub, Finset.sum_sub_distrib]

/-! ## Genuine local-frame continuity -/

/-- Once the pilot lies in the local domain, coordinatewise pilot convergence
implies entrywise convergence of the truth-independent selected frame. -/
theorem mixedPilotSelectedLocalFrame_entry_tendsto
    (b : Fin 3 → ℝ) (xHat : ℕ → Fin 3 → ℝ) (theta : Fin 3 → ℝ)
    (hx : ∀ j, Tendsto (fun n => xHat n j) atTop (nhds (theta j)))
    (hTruthDomain : LocalContinuousFrameDomain b theta)
    (hEventuallyDomain : ∀ᶠ n in atTop,
      LocalContinuousFrameDomain b (xHat n))
    (i k : Fin 3) :
    Tendsto (fun n => mixedPilotSelectedLocalFrame b (xHat n) i k)
      atTop (nhds (localContinuousQubitFrame b theta i k)) := by
  have hlocal := localContinuousQubitFrame_entry_tendsto
    b xHat theta hx hTruthDomain i k
  apply hlocal.congr'
  filter_upwards [hEventuallyDomain] with n hn
  simp [mixedPilotSelectedLocalFrame, hn]

/-- The local-domain premise is discharged by the existing denominator-closure
theorem when the truth is nonzero and the seed is nonparallel. -/
theorem mixedPilotSelectedLocalFrame_entry_tendsto_of_coordinatewise
    (b : Fin 3 → ℝ) (xHat : ℕ → Fin 3 → ℝ) (theta : Fin 3 → ℝ)
    (hx : ∀ j, Tendsto (fun n => xHat n j) atTop (nhds (theta j)))
    (hTruthPositive : 0 < QubitOracle.blochNormSq theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (i k : Fin 3) :
    Tendsto (fun n => mixedPilotSelectedLocalFrame b (xHat n) i k)
      atTop (nhds (localContinuousQubitFrame b theta i k)) := by
  have hTruthDomain : LocalContinuousFrameDomain b theta :=
    ⟨hTruthPositive, hSeed⟩
  have hEventuallyDomain : ∀ᶠ n in atTop,
      LocalContinuousFrameDomain b (xHat n) :=
    eventually_localContinuousFrameDomain_of_nonparallel
      b hx hTruthPositive hSeed
  exact mixedPilotSelectedLocalFrame_entry_tendsto
    b xHat theta hx hTruthDomain hEventuallyDomain i k

/-- Consequently every fixed truth coordinate in the selected frame converges
to its coordinate in the truth-level local frame. -/
theorem mixedPilotSelectedFrameCoordinate_tendsto_of_coordinatewise
    (b : Fin 3 → ℝ) (xHat : ℕ → Fin 3 → ℝ) (theta : Fin 3 → ℝ)
    (hx : ∀ j, Tendsto (fun n => xHat n j) atTop (nhds (theta j)))
    (hTruthPositive : 0 < QubitOracle.blochNormSq theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta)
    (k : Fin 3) :
    Tendsto
      (fun n => qubitFrameCoordinates
        (mixedPilotSelectedLocalFrame b (xHat n)) theta k)
      atTop
      (nhds (qubitFrameCoordinates
        (localContinuousQubitFrame b theta) theta k)) := by
  unfold qubitFrameCoordinates QubitOracle.blochDot qubitFrameAxis
  apply tendsto_finset_sum
  intro i hi
  exact
    (mixedPilotSelectedLocalFrame_entry_tendsto_of_coordinatewise
      b xHat theta hx hTruthPositive hSeed i k).mul tendsto_const_nhds

/-! ## Retained canonical endpoint and the honest adaptive boundary -/

/-- The exact fixed-frame calculation retained from
`OneQubitMixedLinearEstimatorRisk`: `q` shots per axis give risk `3/(4q)`. -/
theorem retainedCanonicalMixedLinearEstimatorRisk
    {q : ℕ} (hq : 0 < q) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    pauliPilotFiniteExpectation (q := q)
        (CanonicalMixedOracle.truthAlignedMixedBloch r)
        (fun path : PauliPilotPath q =>
          CanonicalMixedOracle.truthAlignedMixedSquaredBuresQuadratic r
            (fun j => pauliPilotEstimate (q := q) path j -
              CanonicalMixedOracle.truthAlignedMixedBloch r j)) =
      3 / (4 * (q : ℝ)) :=
  CanonicalMixedOracle.pauliPilot_truthAligned_buresRisk_exact
    hq r hr0 hr1

/-- Final-stage conditional quadratic risk after integrating out the `q`
equal-allocation signed sample means, but before averaging over the pilot. -/
def mixedFrameConditionalQuadraticRisk
    {q : ℕ} (theta : RLSVector 3)
    (R : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  pauliPilotFiniteExpectation (q := q) (qubitFrameCoordinates R theta)
    (fun path : PauliPilotPath q =>
      mixedInteriorBuresQuadraticLoss theta
        (fun i => mixedFrameLinearEstimate (q := q) R path i - theta i))

def mixedFrameConditionalScaledQuadraticRisk
    {q : ℕ} (theta : RLSVector 3)
    (R : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  (3 * (q : ℝ)) * mixedFrameConditionalQuadraticRisk (q := q) theta R

/-- Concrete conditional scaled loss for the polynomial pilot and a supplied
positive equal-allocation final block count. -/
def mixedPolynomialPilotConditionalScaledLoss
    (theta b : RLSVector 3) (qFinal : ℕ → ℕ)
    (n : ℕ) (omega : PauliPilotConsistencySampleSpace) : ℝ≥0∞ :=
  ENNReal.ofReal
    (mixedFrameConditionalScaledQuadraticRisk (q := qFinal n) theta
      (mixedPilotSelectedLocalFrame b
        (polynomialPilotEstimator n omega)))

/-- The already-proved exponential polynomial-pilot bad-event control. -/
theorem mixedPilotFrame_badEventProbability_tendsto_zero
    (theta : RLSVector 3) (hphysical : PauliPilotPhysicalBloch theta)
    (hHoeffding : PauliPilotConsistencyHoeffdingContracts theta hphysical) :
    Tendsto
      (fun n => pauliPilotConsistencyMeasure theta
        (polynomialPilotBadEvent theta n))
      atTop (nhds 0) :=
  polynomialPilot_badEventProbability_tendsto_zero
    theta hphysical hHoeffding

/-- Exact missing deterministic uniformization boundary.  The preceding
sequential continuity theorem does not by itself prove this uniform statement
over every outcome in each shrinking good event. -/
def MixedPilotGoodBranchUniformFrameContinuityPremise
    (theta b : RLSVector 3) (qFinal : ℕ → ℕ) : Prop :=
  ∃ envelope : ℕ → ℝ≥0∞,
    Tendsto envelope atTop (nhds 0) ∧
      ∀ᶠ n in atTop, ∀ omega : PauliPilotConsistencySampleSpace,
        omega ∉ polynomialPilotBadEvent theta n →
          ENNReal.ofReal
            |mixedFrameConditionalScaledQuadraticRisk (q := qFinal n) theta
                (mixedPilotSelectedLocalFrame b
                  (polynomialPilotEstimator n omega)) - 9 / 4| ≤
            envelope n

/-- Exact missing joint-law/disintegration boundary.  A fully adaptive
experiment must prove that its risk equals the pilot expectation of the
conditional finite product-law risk; this file does not posit such a law. -/
def MixedPilotFinalJointLawPremise
    (theta b : RLSVector 3) (qFinal : ℕ → ℕ)
    (adaptiveScaledQuadraticRisk : ℕ → ℝ≥0∞) : Prop :=
  ∀ n,
    adaptiveScaledQuadraticRisk n =
      ∫⁻ omega,
        mixedPolynomialPilotConditionalScaledLoss theta b qFinal n omega
        ∂pauliPilotConsistencyMeasure theta

/-- Exact uniform-integrability boundary for passing a pilot-frame convergence
statement to expected quadratic risk.  It is defined, not assumed or proved. -/
def MixedPilotFrameQuadraticUniformIntegrabilityPremise
    (theta b : RLSVector 3) (qFinal : ℕ → ℕ) : Prop :=
  ∀ epsilon : ℝ≥0∞, epsilon ≠ 0 →
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
      ∀ n,
        MeasurableSet
            {omega : PauliPilotConsistencySampleSpace |
              K < mixedPolynomialPilotConditionalScaledLoss
                theta b qFinal n omega} ∧
          (∫⁻ omega,
            {w : PauliPilotConsistencySampleSpace |
                K < mixedPolynomialPilotConditionalScaledLoss
                  theta b qFinal n w}.indicator
              (mixedPolynomialPilotConditionalScaledLoss
                theta b qFinal n) omega
            ∂pauliPilotConsistencyMeasure theta) ≤ epsilon

namespace Label

/-- Honest paper-facing frame covariance reduction.  It is not an adaptive
expected-risk or physical-Bures theorem. -/
theorem lem_SI_mixed_pilot_frame_covariance_qubit_reduction
    (b x : Fin 3 → ℝ) :
    MixedFrameOrthonormal (mixedPilotSelectedLocalFrame b x) :=
  mixedPilotSelectedLocalFrame_orthonormal b x

end Label

end

end QubitOracle.Paper
