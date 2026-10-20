import QubitOracle.Paper.HybridPathDomination

/-!
# Full-support response laws imply adaptive-path domination

For a discrete response space, a reference law that gives every singleton positive
mass dominates every other law.  Applied pointwise to an adaptive response kernel,
this discharges `HybridResponseDominatedByBase`; the finite-prefix/common-tail theorem
then gives domination of the complete Ionescu-Tulcea trajectory law.

The statement is deliberately separated from protocol-specific probability-floor
proofs.  Mixed full-rank qubits and regular pure-state rounds can use those floor
lemmas to supply `hbase` below.
-/

open MeasureTheory ProbabilityTheory

namespace QubitOracle.Paper

universe u v w

/-- A measure assigning positive mass to every singleton dominates every measure. -/
theorem measure_absolutelyContinuous_of_singleton_pos
    {Omega : Type u} [MeasurableSpace Omega]
    (mu nu : Measure Omega)
    (hpos : forall x : Omega, 0 < nu {x}) :
    mu.AbsolutelyContinuous nu := by
  refine Measure.AbsolutelyContinuous.mk ?_
  intro s _hs hnull
  have hs : s = (∅ : Set Omega) := by
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    have hle : nu {x} <= nu s :=
      measure_mono (Set.singleton_subset_iff.mpr hx)
    rw [hnull] at hle
    exact (not_le_of_gt (hpos x)) hle
  simp [hs]

/-- Pointwise full support of the base response discharges one-step response domination. -/
theorem responseDominatedAt_of_base_singleton_pos
    {H : Type u} {Action : Type w} {Outcome : Type v}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    (protocol : PredictableAdaptiveProtocol H Action Outcome)
    {h h0 : H}
    (hbase : forall action outcome,
      0 < (protocol.response h0 action) {outcome}) :
    ResponseDominatedAt protocol h h0 := by
  intro action
  exact measure_absolutelyContinuous_of_singleton_pos
    (protocol.response h action) (protocol.response h0 action) (hbase action)

/-- A full-support base response law discharges the hybrid response premise uniformly. -/
theorem hybridResponseDominatedByBase_of_base_singleton_pos
    {D : Type*} [Fintype D]
    {Theta : Type u} {Action : Type w} {Outcome : Type}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (localize : Nat -> LANParameter D -> Theta)
    (theta0 : Theta)
    (hbase : forall action outcome,
      0 < (protocol.response theta0 action) {outcome}) :
    HybridResponseDominatedByBase protocol localize theta0 := by
  intro n h
  exact responseDominatedAt_of_base_singleton_pos protocol hbase

/-- Full-support base responses imply domination of every localized infinite path law. -/
theorem hybridFullPathDominatedByBase_of_base_singleton_pos
    {D : Type*} [Fintype D]
    {Theta : Type u} {Action : Type w} {Outcome : Type}
    [MeasurableSpace Action] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [Countable Outcome]
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (localize : Nat -> LANParameter D -> Theta)
    (theta0 : Theta)
    (hbase : forall action outcome,
      0 < (protocol.response theta0 action) {outcome}) :
    HybridFullPathDominatedByBase protocol localize theta0 :=
  hybridFullPathDominatedByBase_of_responseDomination protocol localize theta0
    (hybridResponseDominatedByBase_of_base_singleton_pos
      protocol localize theta0 hbase)

end QubitOracle.Paper
