import QubitOracle.Paper.CompactLimitTransfer

/-!
# Compact identified-fiber transfer in probability

This is the convergence-in-probability analogue of
`tendsto_of_compact_identified_fiber`.  It is useful when a controller has an
unidentified compact nuisance component: convergence of an identifying scalar
still forces convergence of every continuous quantity that is constant on the
identified fiber.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory Set

noncomputable section

/-- Compactness upgrades pointwise continuity on an identified fiber to a
uniform implication near that fiber. -/
theorem compact_identified_fiber_uniform
    {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
    (K : Set X) (hK : IsCompact K)
    (g : X -> Z) (hgContinuous : Continuous g) (z : Z)
    (f : X -> Y) (y : Y)
    (hfiber : forall x, x ∈ K -> g x = z -> ContinuousAt f x ∧ f x = y) :
    forall epsilon, 0 < epsilon -> exists delta, 0 < delta ∧
      forall x, x ∈ K -> dist (g x) z < delta -> dist (f x) y < epsilon := by
  intro epsilon hepsilon
  by_contra hfailure
  push_neg at hfailure
  classical
  choose u huK hgu hfu using fun n : Nat =>
    hfailure (1 / ((n : Real) + 1)) (by positivity)
  have hgtendsto : Tendsto (fun n => g (u n)) atTop (nhds z) := by
    apply tendsto_iff_dist_tendsto_zero.2
    exact squeeze_zero (fun _ => dist_nonneg)
      (fun n => (hgu n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  have hftendsto : Tendsto (fun n => f (u n)) atTop (nhds y) :=
    tendsto_of_compact_identified_fiber K hK u huK g hgContinuous z
      hgtendsto f y hfiber
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hftendsto) epsilon hepsilon
  exact (not_lt_of_ge (hfu N)) (hN N le_rfl)

/-- Continuous identified-fiber quantities preserve convergence in
probability for random sequences constrained to a compact set. -/
theorem tendstoInMeasure_of_compact_identified_fiber
    {Omega X Y Z : Type*} [MeasurableSpace Omega]
    [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
    (mu : Measure Omega)
    (K : Set X) (hK : IsCompact K)
    (u : Nat -> Omega -> X) (hu : forall n omega, u n omega ∈ K)
    (g : X -> Z) (hgContinuous : Continuous g) (z : Z)
    (hg : TendstoInMeasure mu (fun n omega => g (u n omega))
      atTop (fun _ => z))
    (f : X -> Y) (y : Y)
    (hfiber : forall x, x ∈ K -> g x = z -> ContinuousAt f x ∧ f x = y) :
    TendstoInMeasure mu (fun n omega => f (u n omega))
      atTop (fun _ => y) := by
  rw [tendstoInMeasure_iff_dist] at hg ⊢
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, huniform⟩ :=
    compact_identified_fiber_uniform K hK g hgContinuous z f y hfiber
      epsilon hepsilon
  have hbase := hg delta hdelta
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hbase (fun _ => bot_le) ?_
  intro n
  apply measure_mono
  intro omega homega
  simp only [Set.mem_ofPred_eq] at homega ⊢
  by_contra hclose
  exact (not_lt_of_ge homega)
    (huniform (u n omega) (hu n omega) (lt_of_not_ge hclose))

end

end QubitOracle.Paper
