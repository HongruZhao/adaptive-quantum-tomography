import Mathlib

/-!
# Event-restricted nonnegative integration

This module contains only elementary measure-theoretic tools.  It is kept
separate from the asymptotic MLE, LAN, and minimax developments so finite
one-qubit risk bounds do not inherit unrelated statistical assumptions.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

/-- Contribution of a nonnegative loss restricted to an event. -/
def eventLIntegral
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (s : Set Omega) (loss : Omega -> ENNReal) : ENNReal :=
  ∫⁻ omega, s.indicator loss omega ∂mu

/-- If a loss is bounded by `B` on an event, its event contribution is at
most `B` times the mass of that event. -/
theorem eventLIntegral_le_envelope_mul_measure
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (s : Set Omega) (hs : MeasurableSet s)
    (loss : Omega -> ENNReal) (B : ENNReal)
    (hEnvelope : ∀ omega ∈ s, loss omega <= B) :
    eventLIntegral mu s loss <= B * mu s := by
  calc
    eventLIntegral mu s loss <=
        ∫⁻ omega, s.indicator (fun _ => B) omega ∂mu := by
      apply lintegral_mono
      intro omega
      by_cases homega : omega ∈ s
      · simp [Set.indicator_of_mem homega, hEnvelope omega homega]
      · simp [Set.indicator, homega]
    _ = B * mu s := lintegral_indicator_const hs B

/-- Quantitative event-probability and envelope estimates force the event
contribution to vanish. -/
theorem eventLIntegral_tendsto_zero_of_envelope_probability
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Nat -> Measure Omega) (bad : Nat -> Set Omega)
    (loss : Nat -> Omega -> ENNReal) (B p : Nat -> ENNReal)
    (hbad : forall n, MeasurableSet (bad n))
    (hEnvelope : ∀ n omega, omega ∈ bad n -> loss n omega <= B n)
    (hProbability : forall n, mu n (bad n) <= p n)
    (hRate : Tendsto (fun n => B n * p n) atTop (nhds 0)) :
    Tendsto (fun n => eventLIntegral (mu n) (bad n) (loss n))
      atTop (nhds 0) := by
  refine Tendsto.squeeze tendsto_const_nhds hRate ?_ ?_
  · intro n
    exact bot_le
  · intro n
    calc
      eventLIntegral (mu n) (bad n) (loss n) <=
          B n * mu n (bad n) :=
        eventLIntegral_le_envelope_mul_measure
          (mu n) (bad n) (hbad n) (loss n) (B n) (hEnvelope n)
      _ <= B n * p n := by gcongr; exact hProbability n

end

end QubitOracle.Paper
