import QubitOracle.Paper.OneQubitGeneralScheduleAdaptiveScorePrimitives

/-!
# Conditional score identities on the concrete arbitrary-batch path

The Ionescu--Tulcea conditional-distribution theorem is specialized here to
the exact Born kernel.  The result is an actual Mathlib conditional
expectation statement, not a finite-tree surrogate.
-/

namespace QubitOracle.Paper

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

local instance generalScheduleScoreMeasurableSpaceBinaryOutcome :
    MeasurableSpace BinaryOutcome := ⊤

local instance generalScheduleScoreNonemptyBinaryOutcome :
    Nonempty BinaryOutcome := ⟨.plus⟩

/-- Every coordinate of a three-dimensional Euclidean vector is bounded by
its norm.  Kept local to avoid importing an incompatible legacy instance. -/
private theorem generalSchedule_abs_apply_le_norm
    (x : EuclideanSpace Real (Fin 3)) (j : Fin 3) :
    |x j| ≤ ‖x‖ := by
  have hCoordinate :
      ‖x j‖ ^ 2 ≤ ∑ k : Fin 3, ‖x k‖ ^ 2 := by
    exact Finset.single_le_sum
      (fun k _ => sq_nonneg (‖x k‖)) (Finset.mem_univ j)
  have hSquare : |x j| ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simpa only [Real.norm_eq_abs] using hCoordinate
  nlinarith [abs_nonneg (x j), norm_nonneg x]

/-- A finite prefix through coordinate `k`. -/
abbrev GeneralSchedulePrefix (k : Nat) :=
  (i : ↥(Finset.Iic k)) → AdaptiveOutcomeProcess BinaryOutcome i.1

/-- The axis selected for shot `k+1` from a prefix through shot `k`. -/
def generalSchedulePrefixAxis
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 → Real)
    (k : Nat) (pref : GeneralSchedulePrefix k) : Fin 3 → Real :=
  generalScheduleHistoryAxis schedule b (k + 1)
    (iicToAdaptiveTrajectory pref)

theorem generalSchedulePrefixAxis_normSq
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 → Real)
    (k : Nat) (pref : GeneralSchedulePrefix k) :
    QubitOracle.blochNormSq (generalSchedulePrefixAxis schedule b k pref) = 1 := by
  exact generalScheduleHistoryAxis_normSq schedule b (k + 1)
    (iicToAdaptiveTrajectory pref)

theorem generalSchedulePrefixProjection_sq_lt_one
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 → Real)
    (theta : OneQubitPhysicalParameter)
    (hInterior : QubitOracle.blochNormSq theta.1 < 1)
    (k : Nat) (pref : GeneralSchedulePrefix k) :
    QubitOracle.blochDot theta.1
        (generalSchedulePrefixAxis schedule b k pref) ^ 2 < 1 := by
  calc
    QubitOracle.blochDot theta.1
          (generalSchedulePrefixAxis schedule b k pref) ^ 2
        ≤ QubitOracle.blochNormSq theta.1 *
            QubitOracle.blochNormSq
              (generalSchedulePrefixAxis schedule b k pref) :=
      blochDot_sq_le_normSq_mul_normSq theta.1
        (generalSchedulePrefixAxis schedule b k pref)
    _ = QubitOracle.blochNormSq theta.1 := by
      rw [generalSchedulePrefixAxis_normSq]
      ring
    _ < 1 := hInterior

/-- A two-constructor sum can be expanded without relying on constructor
ordering in the generated `Fintype` instance. -/
theorem sum_binaryOutcome (f : BinaryOutcome → Real) :
    (∑ y, f y) = f .plus + f .minus := by
  have hUniv : (Finset.univ : Finset BinaryOutcome) = {.plus, .minus} := by
    ext y
    cases y <;> simp
  rw [show (∑ y, f y) =
      ∑ y ∈ (Finset.univ : Finset BinaryOutcome), f y by simp]
  rw [hUniv]
  simp

/-- Exact singleton mass of the conditional kernel appearing in the
Ionescu--Tulcea path theorem. -/
theorem generalScheduleIonescuStepKernel_singleton
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 → Real)
    (theta : OneQubitPhysicalParameter) (k : Nat)
    (pref : GeneralSchedulePrefix k) (y : BinaryOutcome) :
    (adaptiveIonescuStepKernel
        (generalScheduleAdaptiveBornProtocol schedule b) theta k pref) {y} =
      ENNReal.ofReal
        (binaryBornProbability
          (QubitOracle.blochDot theta.1
            (generalSchedulePrefixAxis schedule b k pref)) y) := by
  change
    (adaptiveStepKernel (generalScheduleAdaptiveBornProtocol schedule b)
        theta (k + 1) (iicToAdaptiveTrajectory pref)) {y} = _
  simpa [generalSchedulePrefixAxis, QubitOracle.blochDot, mul_comm] using
    (generalScheduleAdaptiveBornProtocol_conditional_mass
      schedule b theta (k + 1) (iicToAdaptiveTrajectory pref) y)

theorem generalSchedulePrefixBornProbability_nonnegative
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 → Real)
    (theta : OneQubitPhysicalParameter) (k : Nat)
    (pref : GeneralSchedulePrefix k) (y : BinaryOutcome) :
    0 ≤ binaryBornProbability
      (QubitOracle.blochDot theta.1
        (generalSchedulePrefixAxis schedule b k pref)) y := by
  let axis : MixedMeasurementAxis :=
    ⟨generalSchedulePrefixAxis schedule b k pref,
      (generalSchedulePrefixAxis_normSq schedule b k pref).le⟩
  have h := generalAxisBornProbability_nonnegative theta axis y
  simpa [axis, generalAxisBornProjection, QubitOracle.blochDot, mul_comm] using h

/-- Integration of a prospective score coordinate against the exact next-step
kernel is zero. -/
theorem integral_generalScheduleIonescuScore_eq_zero
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 → Real)
    (theta : OneQubitPhysicalParameter)
    (hInterior : QubitOracle.blochNormSq theta.1 < 1)
    (k : Nat) (pref : GeneralSchedulePrefix k) (j : Fin 3) :
    ∫ y,
        generalScheduleProspectiveScoreVector theta
          (generalSchedulePrefixAxis schedule b k pref) y j
      ∂(adaptiveIonescuStepKernel
        (generalScheduleAdaptiveBornProtocol schedule b) theta k pref) = 0 := by
  letI : IsMarkovKernel
      (adaptiveIonescuStepKernel
        (generalScheduleAdaptiveBornProtocol schedule b) theta k) :=
    adaptiveIonescuStepKernel_isMarkov
      (generalScheduleAdaptiveBornProtocol schedule b) theta k
  rw [integral_fintype Integrable.of_finite]
  rw [sum_binaryOutcome]
  simp only [smul_eq_mul, Measure.real_def,
    generalScheduleIonescuStepKernel_singleton]
  rw [ENNReal.toReal_ofReal
      (generalSchedulePrefixBornProbability_nonnegative
        schedule b theta k pref .plus),
    ENNReal.toReal_ofReal
      (generalSchedulePrefixBornProbability_nonnegative
        schedule b theta k pref .minus)]
  exact generalScheduleProspectiveScore_mean_zero theta
    (generalSchedulePrefixAxis schedule b k pref)
    (generalSchedulePrefixProjection_sq_lt_one
      schedule b theta hInterior k pref) j

/-- Integration of a score outer-product entry against the exact next-step
kernel equals the selected-axis Fisher entry. -/
theorem integral_generalScheduleIonescuScoreProduct_eq_fisher
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 → Real)
    (theta : OneQubitPhysicalParameter)
    (hInterior : QubitOracle.blochNormSq theta.1 < 1)
    (k : Nat) (pref : GeneralSchedulePrefix k) (i j : Fin 3) :
    ∫ y,
        generalScheduleProspectiveScoreVector theta
            (generalSchedulePrefixAxis schedule b k pref) y i *
          generalScheduleProspectiveScoreVector theta
            (generalSchedulePrefixAxis schedule b k pref) y j
      ∂(adaptiveIonescuStepKernel
        (generalScheduleAdaptiveBornProtocol schedule b) theta k pref) =
      QubitOracle.mixedAxisFisher theta.1
        (generalSchedulePrefixAxis schedule b k pref) i j := by
  letI : IsMarkovKernel
      (adaptiveIonescuStepKernel
        (generalScheduleAdaptiveBornProtocol schedule b) theta k) :=
    adaptiveIonescuStepKernel_isMarkov
      (generalScheduleAdaptiveBornProtocol schedule b) theta k
  rw [integral_fintype Integrable.of_finite]
  rw [sum_binaryOutcome]
  simp only [smul_eq_mul, Measure.real_def,
    generalScheduleIonescuStepKernel_singleton]
  rw [ENNReal.toReal_ofReal
      (generalSchedulePrefixBornProbability_nonnegative
        schedule b theta k pref .plus),
    ENNReal.toReal_ofReal
      (generalSchedulePrefixBornProbability_nonnegative
        schedule b theta k pref .minus)]
  simpa [mul_assoc] using
    generalScheduleProspectiveScore_secondMoment_eq_fisher theta
    (generalSchedulePrefixAxis schedule b k pref)
    (generalSchedulePrefixProjection_sq_lt_one
      schedule b theta hInterior k pref) i j

/-- Scalar coordinate process of the literal path score. -/
def generalScheduleActualScoreCoordinate
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 → Real)
    (theta : OneQubitPhysicalParameter) (n : Nat) (j : Fin 3) :
    AdaptiveInfinitePath BinaryOutcome → Real :=
  fun path => generalScheduleActualScoreVector schedule b theta path n j

/-- Each score coordinate is measurable because it factors through a finite
observed prefix and one binary coordinate. -/
theorem generalScheduleActualScoreCoordinate_measurable
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 → Real)
    (theta : OneQubitPhysicalParameter) (n : Nat) (j : Fin 3) :
    Measurable (generalScheduleActualScoreCoordinate schedule b theta n j) := by
  cases n with
  | zero =>
      let f0 := fun y : BinaryOutcome =>
        generalScheduleProspectiveScoreVector theta
          (generalScheduleHistoryAxis schedule b 0 AdaptiveTrajectory.empty) y j
      have hf0 : Measurable f0 := measurable_of_countable f0
      have hcoord : Measurable
          (fun path : AdaptiveInfinitePath BinaryOutcome => path 0) :=
        measurable_pi_apply 0
      change Measurable (fun path : AdaptiveInfinitePath BinaryOutcome =>
        f0 (path 0))
      exact hf0.comp hcoord
  | succ k =>
      let f := fun z : GeneralSchedulePrefix k × BinaryOutcome =>
        generalScheduleProspectiveScoreVector theta
          (generalSchedulePrefixAxis schedule b k z.1) z.2 j
      have hf : Measurable f := measurable_of_countable f
      have hpair : Measurable
          (fun path : AdaptiveInfinitePath BinaryOutcome =>
            (Preorder.frestrictLe k path, path (k + 1))) :=
        (Preorder.measurable_frestrictLe k).prodMk
          (measurable_pi_apply (k + 1))
      change Measurable (fun path : AdaptiveInfinitePath BinaryOutcome =>
        f (Preorder.frestrictLe k path, path (k + 1)))
      exact hf.comp hpair

theorem generalScheduleActualScoreCoordinate_integrable
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 → Real)
    (theta : OneQubitPhysicalParameter)
    (hInterior : QubitOracle.blochNormSq theta.1 < 1)
    (n : Nat) (j : Fin 3) :
    Integrable (generalScheduleActualScoreCoordinate schedule b theta n j)
      (generalScheduleAdaptiveBornPathMeasure schedule b theta) := by
  let mu := generalScheduleAdaptiveBornPathMeasure schedule b theta
  apply Integrable.of_bound
    (generalScheduleActualScoreCoordinate_measurable
      schedule b theta n j).aestronglyMeasurable
    ((1 - blochNorm theta.1)⁻¹)
  filter_upwards [] with path
  rw [Real.norm_eq_abs]
  exact (generalSchedule_abs_apply_le_norm
      (generalScheduleActualScoreVector schedule b theta path n) j).trans
    (generalScheduleActualScoreVector_norm_le schedule b theta path n
      (blochNorm theta.1) le_rfl
      (blochNorm_lt_one_of_normSq_lt_one theta.1 hInterior))

/-- Products of two concrete score coordinates are integrable on every closed
interior truth point. -/
theorem generalScheduleActualScoreProduct_integrable
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 → Real)
    (theta : OneQubitPhysicalParameter)
    (hInterior : QubitOracle.blochNormSq theta.1 < 1)
    (n : Nat) (i j : Fin 3) :
    Integrable
      (fun path =>
        generalScheduleActualScoreCoordinate schedule b theta n i path *
        generalScheduleActualScoreCoordinate schedule b theta n j path)
      (generalScheduleAdaptiveBornPathMeasure schedule b theta) := by
  let K := (1 - blochNorm theta.1)⁻¹
  have hK : 0 ≤ K := by
    exact (inv_pos.mpr
      (sub_pos.mpr
        (blochNorm_lt_one_of_normSq_lt_one theta.1 hInterior))).le
  have hMeasurable : Measurable
      (fun path =>
        generalScheduleActualScoreCoordinate schedule b theta n i path *
        generalScheduleActualScoreCoordinate schedule b theta n j path) :=
    (generalScheduleActualScoreCoordinate_measurable
      schedule b theta n i).mul
      (generalScheduleActualScoreCoordinate_measurable
        schedule b theta n j)
  apply Integrable.of_bound hMeasurable.aestronglyMeasurable (K * K)
  filter_upwards [] with path
  have hi :
      |generalScheduleActualScoreCoordinate schedule b theta n i path| ≤ K :=
    (generalSchedule_abs_apply_le_norm
      (generalScheduleActualScoreVector schedule b theta path n) i).trans
      (generalScheduleActualScoreVector_norm_le schedule b theta path n
        (blochNorm theta.1) le_rfl
        (blochNorm_lt_one_of_normSq_lt_one theta.1 hInterior))
  have hj :
      |generalScheduleActualScoreCoordinate schedule b theta n j path| ≤ K :=
    (generalSchedule_abs_apply_le_norm
      (generalScheduleActualScoreVector schedule b theta path n) j).trans
      (generalScheduleActualScoreVector_norm_le schedule b theta path n
        (blochNorm theta.1) le_rfl
        (blochNorm_lt_one_of_normSq_lt_one theta.1 hInterior))
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul hi hj (abs_nonneg _) hK

/-- The next actual score coordinate is a martingale difference for the
natural coordinate filtration. -/
theorem generalScheduleActualScoreCoordinate_condExp_zero
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 → Real)
    (theta : OneQubitPhysicalParameter)
    (hInterior : QubitOracle.blochNormSq theta.1 < 1)
    (k : Nat) (j : Fin 3) :
    (generalScheduleAdaptiveBornPathMeasure schedule b theta)[
        generalScheduleActualScoreCoordinate schedule b theta (k + 1) j |
        (MeasureTheory.Filtration.piLE k :
          MeasurableSpace (AdaptiveInfinitePath BinaryOutcome))]
      =ᵐ[generalScheduleAdaptiveBornPathMeasure schedule b theta] 0 := by
  rw [MeasureTheory.Filtration.piLE_eq_comap_frestrictLe]
  let mu := generalScheduleAdaptiveBornPathMeasure schedule b theta
  let X : AdaptiveInfinitePath BinaryOutcome → GeneralSchedulePrefix k :=
    Preorder.frestrictLe k
  let Ynext := fun path : AdaptiveInfinitePath BinaryOutcome => path (k + 1)
  let f := fun z : GeneralSchedulePrefix k × BinaryOutcome =>
    generalScheduleProspectiveScoreVector theta
      (generalSchedulePrefixAxis schedule b k z.1) z.2 j
  have hX : Measurable X := Preorder.measurable_frestrictLe k
  have hYnext : Measurable Ynext := measurable_pi_apply (k + 1)
  have hf : StronglyMeasurable f :=
    (measurable_of_countable f).stronglyMeasurable
  have hfInt : Integrable (fun path => f (X path, Ynext path)) mu := by
    change Integrable
      (generalScheduleActualScoreCoordinate schedule b theta (k + 1) j)
      (generalScheduleAdaptiveBornPathMeasure schedule b theta)
    exact generalScheduleActualScoreCoordinate_integrable
      schedule b theta hInterior (k + 1) j
  have hCondExp := ProbabilityTheory.condExp_prod_ae_eq_integral_condDistrib
    hX hYnext.aemeasurable hf hfInt
  have hCondPrefix :
      (ProbabilityTheory.condDistrib Ynext X mu) =ᵐ[mu.map X]
        adaptiveIonescuStepKernel
          (generalScheduleAdaptiveBornProtocol schedule b) theta k := by
    simpa [mu, X, Ynext, generalScheduleAdaptiveBornPathMeasure] using
      (adaptiveInfiniteTrajectory_conditionalStep
        (generalScheduleAdaptiveBornProtocol schedule b) theta k)
  have hCondPath :=
    (MeasureTheory.ae_map_iff hX.aemeasurable
      (Set.Finite.measurableSet
        (Set.toFinite
          {pref |
            (ProbabilityTheory.condDistrib Ynext X mu) pref =
              adaptiveIonescuStepKernel
                (generalScheduleAdaptiveBornProtocol schedule b) theta k pref}))).mp
      hCondPrefix
  have hZero :
      (fun path =>
        ∫ y, f (X path, y)
          ∂(ProbabilityTheory.condDistrib Ynext X mu) (X path))
        =ᵐ[mu] 0 := by
    filter_upwards [hCondPath] with path hpath
    rw [hpath]
    exact integral_generalScheduleIonescuScore_eq_zero
      schedule b theta hInterior k (X path) j
  have hFinal := hCondExp.trans hZero
  have hScoreFunction :
      (fun path => f (X path, Ynext path)) =
        generalScheduleActualScoreCoordinate
          schedule b theta (k + 1) j := by
    funext path
    rfl
  rw [hScoreFunction] at hFinal
  simpa [mu, X, generalScheduleAdaptiveBornPathMeasure] using hFinal

/-- The conditional covariance of the next concrete score is exactly the
adaptive Fisher matrix selected from the observed prefix. -/
theorem generalScheduleActualScoreProduct_condExp_eq_fisher
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 → Real)
    (theta : OneQubitPhysicalParameter)
    (hInterior : QubitOracle.blochNormSq theta.1 < 1)
    (k : Nat) (i j : Fin 3) :
    (generalScheduleAdaptiveBornPathMeasure schedule b theta)[
        (fun path =>
          generalScheduleActualScoreCoordinate schedule b theta (k + 1) i path *
          generalScheduleActualScoreCoordinate schedule b theta (k + 1) j path) |
        (MeasureTheory.Filtration.piLE k :
          MeasurableSpace (AdaptiveInfinitePath BinaryOutcome))]
      =ᵐ[generalScheduleAdaptiveBornPathMeasure schedule b theta]
        fun path => QubitOracle.mixedAxisFisher theta.1
          (generalScheduleActualAxis schedule b path (k + 1)) i j := by
  rw [MeasureTheory.Filtration.piLE_eq_comap_frestrictLe]
  let mu := generalScheduleAdaptiveBornPathMeasure schedule b theta
  let X : AdaptiveInfinitePath BinaryOutcome → GeneralSchedulePrefix k :=
    Preorder.frestrictLe k
  let Ynext := fun path : AdaptiveInfinitePath BinaryOutcome => path (k + 1)
  let f := fun z : GeneralSchedulePrefix k × BinaryOutcome =>
    generalScheduleProspectiveScoreVector theta
        (generalSchedulePrefixAxis schedule b k z.1) z.2 i *
      generalScheduleProspectiveScoreVector theta
        (generalSchedulePrefixAxis schedule b k z.1) z.2 j
  have hX : Measurable X := Preorder.measurable_frestrictLe k
  have hYnext : Measurable Ynext := measurable_pi_apply (k + 1)
  have hf : StronglyMeasurable f :=
    (measurable_of_countable f).stronglyMeasurable
  have hfInt : Integrable (fun path => f (X path, Ynext path)) mu := by
    change Integrable
      (fun path =>
        generalScheduleActualScoreCoordinate schedule b theta (k + 1) i path *
        generalScheduleActualScoreCoordinate schedule b theta (k + 1) j path)
      (generalScheduleAdaptiveBornPathMeasure schedule b theta)
    exact generalScheduleActualScoreProduct_integrable
      schedule b theta hInterior (k + 1) i j
  have hCondExp := ProbabilityTheory.condExp_prod_ae_eq_integral_condDistrib
    hX hYnext.aemeasurable hf hfInt
  have hCondPrefix :
      (ProbabilityTheory.condDistrib Ynext X mu) =ᵐ[mu.map X]
        adaptiveIonescuStepKernel
          (generalScheduleAdaptiveBornProtocol schedule b) theta k := by
    simpa [mu, X, Ynext, generalScheduleAdaptiveBornPathMeasure] using
      (adaptiveInfiniteTrajectory_conditionalStep
        (generalScheduleAdaptiveBornProtocol schedule b) theta k)
  have hCondPath :=
    (MeasureTheory.ae_map_iff hX.aemeasurable
      (Set.Finite.measurableSet
        (Set.toFinite
          {pref |
            (ProbabilityTheory.condDistrib Ynext X mu) pref =
              adaptiveIonescuStepKernel
                (generalScheduleAdaptiveBornProtocol schedule b) theta k pref}))).mp
      hCondPrefix
  have hFisher :
      (fun path =>
        ∫ y, f (X path, y)
          ∂(ProbabilityTheory.condDistrib Ynext X mu) (X path))
        =ᵐ[mu]
      fun path => QubitOracle.mixedAxisFisher theta.1
        (generalScheduleActualAxis schedule b path (k + 1)) i j := by
    filter_upwards [hCondPath] with path hpath
    rw [hpath]
    exact integral_generalScheduleIonescuScoreProduct_eq_fisher
      schedule b theta hInterior k (X path) i j
  have hFinal := hCondExp.trans hFisher
  simpa [mu, X, Ynext, f, generalScheduleAdaptiveBornPathMeasure,
    generalScheduleActualScoreCoordinate, generalScheduleActualScoreVector,
    generalScheduleActualAxis, generalSchedulePrefixAxis,
    generalScheduleProspectiveScoreVector, adaptiveInfinitePathPrefix] using hFinal

end

end QubitOracle.Paper
