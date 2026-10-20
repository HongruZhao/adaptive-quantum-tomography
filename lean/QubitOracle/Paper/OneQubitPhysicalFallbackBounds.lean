import QubitOracle.Paper.OneQubitBoundedChart

/-!
# Deterministic physical-fallback bounds for one qubit

The closed Bloch ball has squared Euclidean diameter at most four.  Therefore
any physical mixed-qubit fallback has a deterministic root-`n` squared-error
bound `4n`, and its `m`-th power gives an envelope for the `2m`-th Euclidean
moment.

For the pure north-pole branch, the safeguarded inverse stereographic chart is
globally bounded: on the regular branch this is the chart theorem from
`OneQubitBoundedChart`, while on the other branch the extension is exactly
zero.  The final bad-event statement is pointwise and contains no probability
or expectation assumption, so it can be passed directly to the bounded
bad-event integration layer in `SafeguardEventProofs`.
-/

namespace QubitOracle

open scoped BigOperators

noncomputable section

/-! ## Diameter of the physical Bloch ball -/

/-- Two physical one-qubit Bloch vectors are at squared Euclidean distance at
most four. -/
theorem blochNormSq_sub_le_four_of_mem_closedBall
    (first second : Fin 3 -> Real)
    (hfirst : blochNormSq first <= 1)
    (hsecond : blochNormSq second <= 1) :
    blochNormSq (fun j => first j - second j) <= 4 := by
  simp [blochNormSq, Fin.sum_univ_succ]
    at hfirst hsecond ⊢
  nlinarith [sq_nonneg (first 0 + second 0),
    sq_nonneg (first 1 + second 1),
    sq_nonneg (first 2 + second 2)]

/-! ## Mixed-qubit root-n fallback envelope -/

/-- Squared Euclidean error after root-`n` scaling.  It is written without a
square root: `n * ||estimate - truth||_2^2`. -/
def mixedRootNFallbackErrorSq
    (n : Nat) (estimate truth : Fin 3 -> Real) : Real :=
  (n : Real) * blochNormSq (fun j => estimate j - truth j)

/-- The physical mixed-qubit root-`n` squared error is bounded by `4n`. -/
theorem mixedRootNFallbackErrorSq_le
    (n : Nat) (estimate truth : Fin 3 -> Real)
    (hestimate : blochNormSq estimate <= 1)
    (htruth : blochNormSq truth <= 1) :
    mixedRootNFallbackErrorSq n estimate truth <= 4 * (n : Real) := by
  have hdistance := blochNormSq_sub_le_four_of_mem_closedBall
    estimate truth hestimate htruth
  unfold mixedRootNFallbackErrorSq
  calc
    (n : Real) * blochNormSq (fun j => estimate j - truth j) <=
        (n : Real) * 4 :=
      mul_le_mul_of_nonneg_left hdistance (Nat.cast_nonneg n)
    _ = 4 * (n : Real) := by ring

/-- The root-`n` squared fallback error is nonnegative. -/
theorem mixedRootNFallbackErrorSq_nonnegative
    (n : Nat) (estimate truth : Fin 3 -> Real) :
    0 <= mixedRootNFallbackErrorSq n estimate truth := by
  unfold mixedRootNFallbackErrorSq blochNormSq
  positivity

/-- Deterministic envelope for the `2m`-th Euclidean moment of a physical
mixed-qubit root-`n` fallback. -/
def mixedRootNFallbackEvenMomentEnvelope (n moment : Nat) : Real :=
  (4 * (n : Real)) ^ moment

/-- Every physical mixed-qubit fallback lies below its deterministic even
moment envelope. -/
theorem mixedRootNFallbackEvenMoment_le
    (n moment : Nat) (estimate truth : Fin 3 -> Real)
    (hestimate : blochNormSq estimate <= 1)
    (htruth : blochNormSq truth <= 1) :
    mixedRootNFallbackErrorSq n estimate truth ^ moment <=
      mixedRootNFallbackEvenMomentEnvelope n moment := by
  unfold mixedRootNFallbackEvenMomentEnvelope
  exact pow_le_pow_left₀
    (mixedRootNFallbackErrorSq_nonnegative n estimate truth)
    (mixedRootNFallbackErrorSq_le n estimate truth hestimate htruth)
    moment

/-! ## Global bounds for the bounded pure-state chart -/

/-- The safeguarded inverse chart has a global coordinate bound on the Bloch
ball.  The regular branch uses the inverse-chart theorem; the other branch is
zero by definition. -/
theorem abs_boundedNorthPoleInverseStereographic_coordinate_le_global
    (eta : Real) (r : Fin 3 -> Real)
    (heta : 0 < eta) (hball : blochNormSq r <= 1) (i : Fin 2) :
    |boundedNorthPoleInverseStereographic eta r i| <= eta⁻¹ := by
  by_cases hregular : eta <= 1 + r 2
  · exact abs_boundedNorthPoleInverseStereographic_coordinate_le
      eta r heta hregular hball i
  · rw [boundedNorthPoleInverseStereographic_eq_zero eta r hregular]
    have hinverse : 0 <= eta⁻¹ := inv_nonneg.mpr heta.le
    simpa using hinverse

/-- The global two-coordinate Euclidean squared-norm bound for the safeguarded
inverse chart. -/
theorem finTwoEuclideanNormSq_boundedNorthPoleInverseStereographic_le_global
    (eta : Real) (r : Fin 3 -> Real)
    (heta : 0 < eta) (hball : blochNormSq r <= 1) :
    finTwoEuclideanNormSq
        (boundedNorthPoleInverseStereographic eta r) <=
      2 * eta⁻¹ ^ 2 := by
  by_cases hregular : eta <= 1 + r 2
  · exact finTwoEuclideanNormSq_boundedNorthPoleInverseStereographic_le
      eta r heta hregular hball
  · rw [boundedNorthPoleInverseStereographic_eq_zero eta r hregular]
    have hright : 0 <= 2 * eta⁻¹ ^ 2 := by positivity
    simpa [finTwoEuclideanNormSq] using hright

/-! ## Pure-qubit root-n bad-event envelope -/

/-- Squared Euclidean north-pole chart error after root-`n` scaling.  The true
north-pole chart coordinate is zero. -/
def pureRootNBoundedChartErrorSq
    (n : Nat) (eta : Real) (fallback : Fin 3 -> Real) : Real :=
  (n : Real) * finTwoEuclideanNormSq
    (boundedNorthPoleInverseStereographic eta fallback)

/-- The pure root-`n` squared chart error is nonnegative. -/
theorem pureRootNBoundedChartErrorSq_nonnegative
    (n : Nat) (eta : Real) (fallback : Fin 3 -> Real) :
    0 <= pureRootNBoundedChartErrorSq n eta fallback := by
  unfold pureRootNBoundedChartErrorSq finTwoEuclideanNormSq
  positivity

/-- A physical pure-qubit fallback has squared root-`n` chart error at most
`2n eta⁻²`. -/
theorem pureRootNBoundedChartErrorSq_le
    (n : Nat) (eta : Real) (fallback : Fin 3 -> Real)
    (heta : 0 < eta) (hphysical : blochNormSq fallback <= 1) :
    pureRootNBoundedChartErrorSq n eta fallback <=
      2 * (n : Real) * eta⁻¹ ^ 2 := by
  have hchart :=
    finTwoEuclideanNormSq_boundedNorthPoleInverseStereographic_le_global
      eta fallback heta hphysical
  unfold pureRootNBoundedChartErrorSq
  calc
    (n : Real) * finTwoEuclideanNormSq
        (boundedNorthPoleInverseStereographic eta fallback) <=
      (n : Real) * (2 * eta⁻¹ ^ 2) :=
        mul_le_mul_of_nonneg_left hchart (Nat.cast_nonneg n)
    _ = 2 * (n : Real) * eta⁻¹ ^ 2 := by ring

/-- Deterministic envelope for the `2m`-th Euclidean moment of the pure
root-`n` bounded-chart fallback. -/
def pureRootNBadEventEvenMomentEnvelope
    (n moment : Nat) (eta : Real) : Real :=
  (2 * (n : Real) * eta⁻¹ ^ 2) ^ moment

/-- The pure bounded-chart fallback lies below its deterministic even-moment
envelope. -/
theorem pureRootNBoundedChartEvenMoment_le
    (n moment : Nat) (eta : Real) (fallback : Fin 3 -> Real)
    (heta : 0 < eta) (hphysical : blochNormSq fallback <= 1) :
    pureRootNBoundedChartErrorSq n eta fallback ^ moment <=
      pureRootNBadEventEvenMomentEnvelope n moment eta := by
  unfold pureRootNBadEventEvenMomentEnvelope
  exact pow_le_pow_left₀
    (pureRootNBoundedChartErrorSq_nonnegative n eta fallback)
    (pureRootNBoundedChartErrorSq_le n eta fallback heta hphysical)
    moment

/-- Pointwise bad-event contribution for later expectation integration. -/
def pureRootNBadEventEvenMoment
    {Omega : Type*} (bad : Set Omega)
    (n moment : Nat) (eta : Real)
    (fallback : Omega -> Fin 3 -> Real) (omega : Omega) : Real := by
  classical
  exact if omega ∈ bad then
    pureRootNBoundedChartErrorSq n eta (fallback omega) ^ moment
  else 0

/-- The bad-event contribution is nonnegative, pointwise. -/
theorem pureRootNBadEventEvenMoment_nonnegative
    {Omega : Type*} (bad : Set Omega)
    (n moment : Nat) (eta : Real)
    (fallback : Omega -> Fin 3 -> Real) (omega : Omega) :
    0 <= pureRootNBadEventEvenMoment
      bad n moment eta fallback omega := by
  classical
  unfold pureRootNBadEventEvenMoment
  split_ifs
  · exact pow_nonneg
      (pureRootNBoundedChartErrorSq_nonnegative n eta (fallback omega)) moment
  · exact le_rfl

/-- Deterministic pure root-`n` bad-event envelope in the pointwise form used
before applying a probability or expectation bound. -/
theorem pureRootNBadEventEvenMoment_le_envelope
    {Omega : Type*} (bad : Set Omega)
    (n moment : Nat) (eta : Real)
    (fallback : Omega -> Fin 3 -> Real)
    (heta : 0 < eta)
    (hphysical : ∀ omega, blochNormSq (fallback omega) <= 1)
    (omega : Omega) :
    pureRootNBadEventEvenMoment bad n moment eta fallback omega <=
      pureRootNBadEventEvenMomentEnvelope n moment eta := by
  classical
  by_cases hbad : omega ∈ bad
  · unfold pureRootNBadEventEvenMoment
    rw [if_pos hbad]
    exact pureRootNBoundedChartEvenMoment_le
      n moment eta (fallback omega) heta (hphysical omega)
  · unfold pureRootNBadEventEvenMoment
    rw [if_neg hbad]
    unfold pureRootNBadEventEvenMomentEnvelope
    positivity

end

end QubitOracle
