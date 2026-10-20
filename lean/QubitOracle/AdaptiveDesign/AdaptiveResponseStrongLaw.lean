import QubitOracle.Paper.AdaptiveTrajectoryExperiment
import QubitOracle.Paper.BoundedMartingaleAzumaStrongLaw
/-!
# Bounded response strong law on the actual adaptive experiment

The action is a genuine history-dependent argument of the Born response
kernel. A bounded scalar response centered under every action has vanishing
empirical mean almost surely on that protocol's Ionescu--Tulcea path law.
The action space need not be finite or countable; the observed outcome space
is finite. This is the probabilistic bridge needed for the multilevel
all-observation ridge estimator.
-/

namespace QubitOracle.AdaptiveDesign.AdaptiveResponseStrongLaw

open Filter MeasureTheory ProbabilityTheory QubitOracle.Paper
open scoped BigOperators Topology

noncomputable section

variable {Theta Action Outcome : Type*}
variable [MeasurableSpace Action] [MeasurableSpace Outcome]
variable [Fintype Outcome] [MeasurableSingletonClass Outcome]
variable [StandardBorelSpace Outcome] [Nonempty Outcome]

abbrev Prefix (n : ℕ) := (i : Finset.Iic n) → AdaptiveOutcomeProcess Outcome i

/-- The centered response actually observed at a global shot, with the
measurement chosen only from its strict past. -/
def actualResponse
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (centered : Action → Outcome → ℝ) (n : ℕ)
    (path : AdaptiveInfinitePath Outcome) : ℝ :=
  centered (protocol.design n (adaptiveInfinitePathPrefix n path)) (path n)

def prefixResponse
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (centered : Action → Outcome → ℝ) (n : ℕ)
    (pref : Prefix (Outcome := Outcome) n) : ℝ :=
  centered
    (protocol.design n
      ⟨List.ofFn fun i : Fin n => pref ⟨i.1, Finset.mem_Iic.mpr i.2.le⟩⟩)
    (pref ⟨n, Finset.mem_Iic.mpr le_rfl⟩)

theorem actualResponse_eq_prefix
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (centered : Action → Outcome → ℝ) (n : ℕ) :
    actualResponse protocol centered n =
      (prefixResponse protocol centered n).comp (Preorder.frestrictLe n) := by
  funext path
  cases n with
  | zero => rfl
  | succ n => rfl

theorem actualResponse_stronglyMeasurable_piLE
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome)
    (centered : Action → Outcome → ℝ) (n : ℕ) :
    StronglyMeasurable[MeasureTheory.Filtration.piLE n]
      (actualResponse protocol centered n) := by
  rw [actualResponse_eq_prefix, MeasureTheory.Filtration.piLE_eq_comap_frestrictLe]
  exact ((measurable_of_countable (prefixResponse protocol centered n)).comp
    (Measurable.of_comap_le le_rfl)).stronglyMeasurable

theorem actualResponse_integrable
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta)
    (centered : Action → Outcome → ℝ) (C : ℝ)
    (hbound : ∀ action outcome, ‖centered action outcome‖ ≤ C) (n : ℕ) :
    Integrable (actualResponse protocol centered n)
      (adaptiveInfiniteTrajectoryMeasure protocol theta) := by
  apply Integrable.of_bound
    ((actualResponse_stronglyMeasurable_piLE protocol centered n).mono
      (MeasureTheory.Filtration.piLE.le n)).aestronglyMeasurable C
  filter_upwards [] with path
  exact hbound _ _

/-- Conditional centering is derived from the exact action-dependent kernel;
it is not assumed as a property of a separately supplied stochastic process. -/
theorem actualResponse_condExp_zero
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta)
    (centered : Action → Outcome → ℝ)
    (hcenter : ∀ action, ∫ y, centered action y ∂protocol.response theta action = 0)
    (C : ℝ) (hbound : ∀ action outcome, ‖centered action outcome‖ ≤ C) (n : ℕ) :
    (adaptiveInfiniteTrajectoryMeasure protocol theta)[
      actualResponse protocol centered (n + 1) | MeasureTheory.Filtration.piLE n]
      =ᵐ[adaptiveInfiniteTrajectoryMeasure protocol theta] 0 := by
  rw [MeasureTheory.Filtration.piLE_eq_comap_frestrictLe]
  let μ := adaptiveInfiniteTrajectoryMeasure protocol theta
  let X : AdaptiveInfinitePath Outcome → Prefix (Outcome := Outcome) n :=
    Preorder.frestrictLe n
  let Ynext := fun path : AdaptiveInfinitePath Outcome => path (n + 1)
  let f := fun z : Prefix (Outcome := Outcome) n × Outcome =>
    centered (protocol.design (n + 1) (iicToAdaptiveTrajectory z.1)) z.2
  have hX : Measurable X := Preorder.measurable_frestrictLe n
  have hYnext : Measurable Ynext := measurable_pi_apply (n + 1)
  have hf : StronglyMeasurable f := (measurable_of_countable f).stronglyMeasurable
  have hfInt : Integrable (fun path => f (X path, Ynext path)) μ :=
    actualResponse_integrable protocol theta centered C hbound (n + 1)
  have hCondExp := condExp_prod_ae_eq_integral_condDistrib
    hX hYnext.aemeasurable hf hfInt
  have hCondPrefix :
      condDistrib Ynext X μ =ᵐ[μ.map X] adaptiveIonescuStepKernel protocol theta n := by
    exact adaptiveInfiniteTrajectory_conditionalStep protocol theta n
  have hCondPath := (ae_map_iff hX.aemeasurable
    (Set.Finite.measurableSet (Set.toFinite
      {pref | (condDistrib Ynext X μ) pref =
        adaptiveIonescuStepKernel protocol theta n pref}))).mp hCondPrefix
  have hZero :
      (fun path => ∫ y, f (X path, y) ∂(condDistrib Ynext X μ) (X path))
        =ᵐ[μ] 0 := by
    filter_upwards [hCondPath] with path hpath
    rw [hpath]
    exact hcenter _
  exact hCondExp.trans hZero

/-- Every bounded scalar response centered under each physical action obeys
the strong law on the actual adaptive Born path. This includes actions frozen
inside arbitrary predetermined batches. -/
theorem actualResponse_average_ae_tendsto_zero
    (protocol : PredictableAdaptiveProtocol Theta Action Outcome) (theta : Theta)
    (centered : Action → Outcome → ℝ)
    (hcenter : ∀ action, ∫ y, centered action y ∂protocol.response theta action = 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ action outcome, ‖centered action outcome‖ ≤ C) :
    ∀ᵐ path ∂adaptiveInfiniteTrajectoryMeasure protocol theta,
      Tendsto
        (fun n : ℕ => (n : ℝ)⁻¹ *
          ∑ t ∈ Finset.range n, actualResponse protocol centered t path)
        atTop (𝓝 0) := by
  let μ := adaptiveInfiniteTrajectoryMeasure protocol theta
  let shifted : ℕ → AdaptiveInfinitePath Outcome → ℝ
    | 0, _ => 0
    | n + 1, path => actualResponse protocol centered (n + 1) path
  have hadapted : StronglyAdapted MeasureTheory.Filtration.piLE shifted := by
    intro n
    cases n with
    | zero => exact stronglyMeasurable_const
    | succ n => exact actualResponse_stronglyMeasurable_piLE protocol centered (n + 1)
  have hzero : shifted 0 = 0 := rfl
  have hcentered (n : ℕ) : μ[shifted (n + 1) | MeasureTheory.Filtration.piLE n] =ᵐ[μ] 0 :=
    actualResponse_condExp_zero protocol theta centered hcenter C hbound n
  have hbounded (n : ℕ) (path : AdaptiveInfinitePath Outcome) : ‖shifted n path‖ ≤ C := by
    cases n with
    | zero => simpa [shifted] using hC
    | succ n => exact hbound _ _
  have hraw := boundedMartingaleDifference_average_ae_tendsto_zero
    μ MeasureTheory.Filtration.piLE shifted hadapted hzero hcentered C hC hbounded
  have hsum (n : ℕ) (path : AdaptiveInfinitePath Outcome) :
      (∑ t ∈ Finset.range n, actualResponse protocol centered t path) =
        (∑ t ∈ Finset.range (n + 1), shifted t path) +
          (actualResponse protocol centered 0 path - actualResponse protocol centered n path) := by
    have hleft := Finset.sum_range_succ
      (fun t => actualResponse protocol centered t path) n
    have hright := Finset.sum_range_succ'
      (fun t => actualResponse protocol centered t path) n
    rw [Finset.sum_range_succ']
    simp only [shifted, add_zero]
    linarith
  filter_upwards [hraw] with path hpath
  have hendpoint : Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ *
        (actualResponse protocol centered 0 path - actualResponse protocol centered n path))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm
      (fun n => ?_)
      (by simpa [div_eq_mul_inv, mul_comm] using
        tendsto_const_div_atTop_nhds_zero_nat (2 * C))
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg n))
    calc
      ‖actualResponse protocol centered 0 path - actualResponse protocol centered n path‖ ≤
          ‖actualResponse protocol centered 0 path‖ + ‖actualResponse protocol centered n path‖ :=
        norm_sub_le _ _
      _ ≤ C + C := add_le_add (hbound _ _) (hbound _ _)
      _ = C * 2 := by ring
  simpa only [hsum, mul_add, add_zero] using hpath.add hendpoint

end

end QubitOracle.AdaptiveDesign.AdaptiveResponseStrongLaw
