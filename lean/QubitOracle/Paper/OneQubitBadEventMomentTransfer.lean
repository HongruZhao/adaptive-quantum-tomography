import QubitOracle.Paper.OneQubitPhysicalFallbackBounds
import QubitOracle.Paper.EventLIntegralCore

/-!
# Bad-event moment transfer for physical one-qubit fallbacks

This module connects the deterministic one-qubit fallback envelopes to the
existing event-integration layer.  Every result is noncircular: the inputs are
pointwise physical-state bounds and a bad-event mass estimate, never the
moment conclusion that is being proved.

For a moment index `m`, the loss below is the `m`-th power of the squared
root-`n` Euclidean error, hence the `2m`-th Euclidean moment.  Polynomial
cancellation is expressed without division:

`n^(m+1) * P(bad n) <= C`

implies

`n * E[loss * 1_(bad n)] <= growth^m * C`.

All powers have natural-number exponents.
-/

namespace QubitOracle.Paper

open MeasureTheory
open scoped ENNReal

noncomputable section

/-! ## General nonnegative event transfer -/

/-- The event-restricted extended expectation of a real nonnegative random
variable.  `ofReal` makes this definition total; the transfer theorem below
records the actual nonnegativity hypothesis on the event. -/
def nonnegativeRealBadEventLIntegral
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (bad : Set Omega) (X : Omega -> Real) : ENNReal :=
  eventLIntegral mu bad (fun omega => ENNReal.ofReal (X omega))

/-- Honest real-to-`lintegral` transfer: a measurable real random variable
which is nonnegative and bounded by `envelope` on a measurable bad event has
bad-event expectation at most `envelope * probability`. -/
theorem nonnegativeRealBadEventLIntegral_le_envelope_mul_probability
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (bad : Set Omega) (hbad : MeasurableSet bad)
    (X : Omega -> Real) (hX : Measurable X) (envelope : Real)
    (hEnvelope : ∀ omega ∈ bad, 0 <= X omega ∧ X omega <= envelope) :
    nonnegativeRealBadEventLIntegral mu bad X <=
      ENNReal.ofReal envelope * mu bad := by
  have _hLossMeasurable :
      Measurable (fun omega => ENNReal.ofReal (X omega)) :=
    hX.ennreal_ofReal
  unfold nonnegativeRealBadEventLIntegral
  exact eventLIntegral_le_envelope_mul_measure
    mu bad hbad (fun omega => ENNReal.ofReal (X omega))
      (ENNReal.ofReal envelope)
      (fun omega homega => ENNReal.ofReal_le_ofReal
        (hEnvelope omega homega).2)

/-- `ofReal` respects multiplication by a natural sample size when the real
factor is nonnegative. -/
theorem ennreal_ofReal_mul_natCast
    (a : Real) (ha : 0 <= a) (n : Nat) :
    ENNReal.ofReal (a * (n : Real)) =
      ENNReal.ofReal a * (n : ENNReal) := by
  rw [ENNReal.ofReal_mul ha]
  norm_num

/-! ## Mixed physical fallback -/

/-- Extended nonnegative `2m`-th moment loss for a mixed physical fallback. -/
def mixedPhysicalFallbackEvenMomentLoss
    {Omega : Type*} (n moment : Nat)
    (fallback : Omega -> Fin 3 -> Real) (truth : Fin 3 -> Real)
    (omega : Omega) : ENNReal :=
  (ENNReal.ofReal
    (QubitOracle.mixedRootNFallbackErrorSq n (fallback omega) truth)) ^ moment

/-- Pointwise mixed physical fallback envelope in `ENNReal`. -/
theorem mixedPhysicalFallbackEvenMomentLoss_le
    {Omega : Type*} (n moment : Nat)
    (fallback : Omega -> Fin 3 -> Real) (truth : Fin 3 -> Real)
    (omega : Omega)
    (hfallback : QubitOracle.blochNormSq (fallback omega) <= 1)
    (htruth : QubitOracle.blochNormSq truth <= 1) :
    mixedPhysicalFallbackEvenMomentLoss n moment fallback truth omega <=
      ((4 : ENNReal) * (n : ENNReal)) ^ moment := by
  unfold mixedPhysicalFallbackEvenMomentLoss
  apply pow_le_pow_left'
  calc
    ENNReal.ofReal
        (QubitOracle.mixedRootNFallbackErrorSq n (fallback omega) truth) <=
      ENNReal.ofReal (4 * (n : Real)) :=
        ENNReal.ofReal_le_ofReal
          (QubitOracle.mixedRootNFallbackErrorSq_le
            n (fallback omega) truth hfallback htruth)
    _ = (4 : ENNReal) * (n : ENNReal) := by
      simpa using ennreal_ofReal_mul_natCast 4 (by norm_num) n

/-- A mixed physical fallback contributes at most `(4n)^m` times the bad-event
probability to its `2m`-th root-`n` moment. -/
theorem mixedPhysicalFallbackBadEventLIntegral_le
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (bad : Set Omega) (hbad : MeasurableSet bad)
    (n moment : Nat)
    (fallback : Omega -> Fin 3 -> Real) (truth : Fin 3 -> Real)
    (hfallback : ∀ omega ∈ bad,
      QubitOracle.blochNormSq (fallback omega) <= 1)
    (htruth : QubitOracle.blochNormSq truth <= 1) :
    eventLIntegral mu bad
        (mixedPhysicalFallbackEvenMomentLoss n moment fallback truth) <=
      ((4 : ENNReal) * (n : ENNReal)) ^ moment * mu bad := by
  exact eventLIntegral_le_envelope_mul_measure
    mu bad hbad
      (mixedPhysicalFallbackEvenMomentLoss n moment fallback truth)
      (((4 : ENNReal) * (n : ENNReal)) ^ moment)
      (fun omega homega => mixedPhysicalFallbackEvenMomentLoss_le
        n moment fallback truth omega (hfallback omega homega) htruth)

/-! ## Pure bounded-chart fallback -/

/-- Extended nonnegative `2m`-th moment loss for the north-pole bounded-chart
fallback. -/
def pureBoundedChartFallbackEvenMomentLoss
    {Omega : Type*} (n moment : Nat) (eta : Real)
    (fallback : Omega -> Fin 3 -> Real) (omega : Omega) : ENNReal :=
  (ENNReal.ofReal
    (QubitOracle.pureRootNBoundedChartErrorSq n eta (fallback omega))) ^ moment

/-- Pointwise pure bounded-chart envelope in `ENNReal`. -/
theorem pureBoundedChartFallbackEvenMomentLoss_le
    {Omega : Type*} (n moment : Nat) (eta : Real)
    (fallback : Omega -> Fin 3 -> Real) (omega : Omega)
    (heta : 0 < eta)
    (hphysical : QubitOracle.blochNormSq (fallback omega) <= 1) :
    pureBoundedChartFallbackEvenMomentLoss n moment eta fallback omega <=
      (ENNReal.ofReal (2 * eta⁻¹ ^ 2) * (n : ENNReal)) ^ moment := by
  unfold pureBoundedChartFallbackEvenMomentLoss
  apply pow_le_pow_left'
  have hgrowth : 0 <= 2 * eta⁻¹ ^ 2 := by positivity
  have hreal :
      QubitOracle.pureRootNBoundedChartErrorSq n eta (fallback omega) <=
        (2 * eta⁻¹ ^ 2) * (n : Real) := by
    calc
      QubitOracle.pureRootNBoundedChartErrorSq n eta (fallback omega) <=
          2 * (n : Real) * eta⁻¹ ^ 2 :=
        QubitOracle.pureRootNBoundedChartErrorSq_le
          n eta (fallback omega) heta hphysical
      _ = (2 * eta⁻¹ ^ 2) * (n : Real) := by ring
  calc
    ENNReal.ofReal
        (QubitOracle.pureRootNBoundedChartErrorSq n eta (fallback omega)) <=
      ENNReal.ofReal ((2 * eta⁻¹ ^ 2) * (n : Real)) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (2 * eta⁻¹ ^ 2) * (n : ENNReal) :=
      ennreal_ofReal_mul_natCast (2 * eta⁻¹ ^ 2) hgrowth n

/-- A pure bounded-chart fallback contributes at most
`(2 eta⁻² n)^m` times the bad-event probability. -/
theorem pureBoundedChartBadEventLIntegral_le
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (bad : Set Omega) (hbad : MeasurableSet bad)
    (n moment : Nat) (eta : Real)
    (fallback : Omega -> Fin 3 -> Real)
    (heta : 0 < eta)
    (hphysical : ∀ omega ∈ bad,
      QubitOracle.blochNormSq (fallback omega) <= 1) :
    eventLIntegral mu bad
        (pureBoundedChartFallbackEvenMomentLoss n moment eta fallback) <=
      (ENNReal.ofReal (2 * eta⁻¹ ^ 2) * (n : ENNReal)) ^ moment *
        mu bad := by
  exact eventLIntegral_le_envelope_mul_measure
    mu bad hbad
      (pureBoundedChartFallbackEvenMomentLoss n moment eta fallback)
      ((ENNReal.ofReal (2 * eta⁻¹ ^ 2) * (n : ENNReal)) ^ moment)
      (fun omega homega => pureBoundedChartFallbackEvenMomentLoss_le
        n moment eta fallback omega heta (hphysical omega homega))

/-! ## Polynomial-tail cancellation -/

/-- Pure algebraic cancellation of `n^moment` growth by a polynomial tail of
order `moment + 1`.  The conclusion is division-free and remains meaningful
at `n = 0`. -/
theorem ennreal_natPower_badEventTail_cancellation
    (n moment : Nat) (growth probability tailConstant : ENNReal)
    (hTail :
      (n : ENNReal) ^ (moment + 1) * probability <= tailConstant) :
    (n : ENNReal) *
        (((growth * (n : ENNReal)) ^ moment) * probability) <=
      growth ^ moment * tailConstant := by
  calc
    (n : ENNReal) *
        (((growth * (n : ENNReal)) ^ moment) * probability) =
      growth ^ moment *
        ((n : ENNReal) ^ (moment + 1) * probability) := by
          rw [mul_pow, pow_succ]
          ac_rfl
    _ <= growth ^ moment * tailConstant :=
      by gcongr

/-- For positive sample size, the preceding weighted estimate also supplies
an explicit uniform unweighted constant. -/
theorem ennreal_natPower_badEventTail_uniform
    (n moment : Nat) (hn : 1 <= n)
    (growth probability tailConstant : ENNReal)
    (hTail :
      (n : ENNReal) ^ (moment + 1) * probability <= tailConstant) :
    ((growth * (n : ENNReal)) ^ moment) * probability <=
      growth ^ moment * tailConstant := by
  have hnENNReal : (1 : ENNReal) <= (n : ENNReal) := by
    exact_mod_cast hn
  calc
    ((growth * (n : ENNReal)) ^ moment) * probability =
        1 * (((growth * (n : ENNReal)) ^ moment) * probability) := by
          rw [one_mul]
    _ <= (n : ENNReal) *
        (((growth * (n : ENNReal)) ^ moment) * probability) :=
      by gcongr
    _ <= growth ^ moment * tailConstant :=
      ennreal_natPower_badEventTail_cancellation
        n moment growth probability tailConstant hTail

/-- A tail condition `n^(m+1) P(bad) <= C` gives the explicit mixed-qubit
weighted bound `n E_bad <= 4^m C`. -/
theorem mixedPhysicalFallbackBadEventLIntegral_polynomialTail
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (bad : Set Omega) (hbad : MeasurableSet bad)
    (n moment : Nat)
    (fallback : Omega -> Fin 3 -> Real) (truth : Fin 3 -> Real)
    (hfallback : ∀ omega ∈ bad,
      QubitOracle.blochNormSq (fallback omega) <= 1)
    (htruth : QubitOracle.blochNormSq truth <= 1)
    (tailConstant : ENNReal)
    (hTail :
      (n : ENNReal) ^ (moment + 1) * mu bad <= tailConstant) :
    (n : ENNReal) *
        eventLIntegral mu bad
          (mixedPhysicalFallbackEvenMomentLoss n moment fallback truth) <=
      (4 : ENNReal) ^ moment * tailConstant := by
  have hIntegral := mixedPhysicalFallbackBadEventLIntegral_le
    mu bad hbad n moment fallback truth hfallback htruth
  calc
    (n : ENNReal) *
        eventLIntegral mu bad
          (mixedPhysicalFallbackEvenMomentLoss n moment fallback truth) <=
      (n : ENNReal) *
        ((((4 : ENNReal) * (n : ENNReal)) ^ moment) * mu bad) :=
      by gcongr
    _ <= (4 : ENNReal) ^ moment * tailConstant :=
      ennreal_natPower_badEventTail_cancellation
        n moment 4 (mu bad) tailConstant hTail

/-- The corresponding explicit mixed-qubit unweighted uniform bound for
`n >= 1`. -/
theorem mixedPhysicalFallbackBadEventLIntegral_uniform
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (bad : Set Omega) (hbad : MeasurableSet bad)
    (n moment : Nat) (hn : 1 <= n)
    (fallback : Omega -> Fin 3 -> Real) (truth : Fin 3 -> Real)
    (hfallback : ∀ omega ∈ bad,
      QubitOracle.blochNormSq (fallback omega) <= 1)
    (htruth : QubitOracle.blochNormSq truth <= 1)
    (tailConstant : ENNReal)
    (hTail :
      (n : ENNReal) ^ (moment + 1) * mu bad <= tailConstant) :
    eventLIntegral mu bad
        (mixedPhysicalFallbackEvenMomentLoss n moment fallback truth) <=
      (4 : ENNReal) ^ moment * tailConstant := by
  have hnENNReal : (1 : ENNReal) <= (n : ENNReal) := by
    exact_mod_cast hn
  calc
    eventLIntegral mu bad
        (mixedPhysicalFallbackEvenMomentLoss n moment fallback truth) =
      1 * eventLIntegral mu bad
        (mixedPhysicalFallbackEvenMomentLoss n moment fallback truth) := by
          rw [one_mul]
    _ <= (n : ENNReal) * eventLIntegral mu bad
        (mixedPhysicalFallbackEvenMomentLoss n moment fallback truth) :=
      by gcongr
    _ <= (4 : ENNReal) ^ moment * tailConstant :=
      mixedPhysicalFallbackBadEventLIntegral_polynomialTail
        mu bad hbad n moment fallback truth hfallback htruth
          tailConstant hTail

/-- A tail condition `n^(m+1) P(bad) <= C` gives the explicit pure-chart
weighted bound `n E_bad <= (2 eta⁻²)^m C`. -/
theorem pureBoundedChartBadEventLIntegral_polynomialTail
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (bad : Set Omega) (hbad : MeasurableSet bad)
    (n moment : Nat) (eta : Real)
    (fallback : Omega -> Fin 3 -> Real)
    (heta : 0 < eta)
    (hphysical : ∀ omega ∈ bad,
      QubitOracle.blochNormSq (fallback omega) <= 1)
    (tailConstant : ENNReal)
    (hTail :
      (n : ENNReal) ^ (moment + 1) * mu bad <= tailConstant) :
    (n : ENNReal) *
        eventLIntegral mu bad
          (pureBoundedChartFallbackEvenMomentLoss
            n moment eta fallback) <=
      ENNReal.ofReal (2 * eta⁻¹ ^ 2) ^ moment * tailConstant := by
  have hIntegral := pureBoundedChartBadEventLIntegral_le
    mu bad hbad n moment eta fallback heta hphysical
  calc
    (n : ENNReal) *
        eventLIntegral mu bad
          (pureBoundedChartFallbackEvenMomentLoss
            n moment eta fallback) <=
      (n : ENNReal) *
        (((ENNReal.ofReal (2 * eta⁻¹ ^ 2) * (n : ENNReal)) ^ moment) *
          mu bad) :=
      by gcongr
    _ <= ENNReal.ofReal (2 * eta⁻¹ ^ 2) ^ moment * tailConstant :=
      ennreal_natPower_badEventTail_cancellation
        n moment (ENNReal.ofReal (2 * eta⁻¹ ^ 2))
          (mu bad) tailConstant hTail

/-- The corresponding explicit pure-chart unweighted uniform bound for
`n >= 1`. -/
theorem pureBoundedChartBadEventLIntegral_uniform
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (bad : Set Omega) (hbad : MeasurableSet bad)
    (n moment : Nat) (hn : 1 <= n) (eta : Real)
    (fallback : Omega -> Fin 3 -> Real)
    (heta : 0 < eta)
    (hphysical : ∀ omega ∈ bad,
      QubitOracle.blochNormSq (fallback omega) <= 1)
    (tailConstant : ENNReal)
    (hTail :
      (n : ENNReal) ^ (moment + 1) * mu bad <= tailConstant) :
    eventLIntegral mu bad
        (pureBoundedChartFallbackEvenMomentLoss n moment eta fallback) <=
      ENNReal.ofReal (2 * eta⁻¹ ^ 2) ^ moment * tailConstant := by
  have hnENNReal : (1 : ENNReal) <= (n : ENNReal) := by
    exact_mod_cast hn
  calc
    eventLIntegral mu bad
        (pureBoundedChartFallbackEvenMomentLoss n moment eta fallback) =
      1 * eventLIntegral mu bad
        (pureBoundedChartFallbackEvenMomentLoss n moment eta fallback) := by
          rw [one_mul]
    _ <= (n : ENNReal) * eventLIntegral mu bad
        (pureBoundedChartFallbackEvenMomentLoss n moment eta fallback) :=
      by gcongr
    _ <= ENNReal.ofReal (2 * eta⁻¹ ^ 2) ^ moment * tailConstant :=
      pureBoundedChartBadEventLIntegral_polynomialTail
        mu bad hbad n moment eta fallback heta hphysical
          tailConstant hTail

end

end QubitOracle.Paper
