import QubitOracle.Paper.OneQubitGeneralScheduleAdaptiveScoreCondExp
import QubitOracle.Paper.OneQubitGeneralSchedulePilotShotOrdering

/-!
# Conditional response identities on the arbitrary-schedule Born path

For every literal shot, the signed binary response minus its predictable Born
mean is a bounded martingale difference.  At the globally enumerated Pauli
pilot shots this specializes to `Y-theta_j`, which is the noise used by the
pooled pilot controller.
-/

namespace QubitOracle.Paper

open MeasureTheory ProbabilityTheory

noncomputable section

local instance generalScheduleResponseMeasurableSpaceBinaryOutcome :
    MeasurableSpace BinaryOutcome := ⊤

local instance generalScheduleResponseNonemptyBinaryOutcome :
    Nonempty BinaryOutcome := ⟨.plus⟩

/-- One signed response centered by its Born mean for a prospective axis. -/
def generalScheduleProspectiveResponseNoise
    (theta : OneQubitPhysicalParameter) (axis : Fin 3 -> Real)
    (y : BinaryOutcome) : Real :=
  y.sign - QubitOracle.blochDot theta.1 axis

/-- The prospective response noise integrates to zero against the exact
Ionescu--Tulcea next-step kernel. -/
theorem integral_generalScheduleIonescuResponseNoise_eq_zero
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 -> Real)
    (theta : OneQubitPhysicalParameter) (k : Nat)
    (pref : GeneralSchedulePrefix k) :
    ∫ y, generalScheduleProspectiveResponseNoise theta
        (generalSchedulePrefixAxis schedule b k pref) y
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
  simp [generalScheduleProspectiveResponseNoise, binaryBornProbability,
    BinaryOutcome.sign]
  ring

/-- Raw response noise at a literal global shot of the realized path. -/
def generalScheduleActualResponseNoise
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 -> Real)
    (theta : OneQubitPhysicalParameter) (n : Nat) :
    AdaptiveInfinitePath BinaryOutcome -> Real :=
  fun path => generalScheduleProspectiveResponseNoise theta
    (generalScheduleActualAxis schedule b path n) (path n)

/-- Raw response noise depends measurably on a finite prefix and the current
binary coordinate. -/
theorem generalScheduleActualResponseNoise_measurable
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 -> Real)
    (theta : OneQubitPhysicalParameter) (n : Nat) :
    Measurable (generalScheduleActualResponseNoise schedule b theta n) := by
  cases n with
  | zero =>
      let f0 := fun y : BinaryOutcome =>
        generalScheduleProspectiveResponseNoise theta
          (generalScheduleHistoryAxis schedule b 0 AdaptiveTrajectory.empty) y
      have hf0 : Measurable f0 := measurable_of_countable f0
      have hcoord : Measurable
          (fun path : AdaptiveInfinitePath BinaryOutcome => path 0) :=
        measurable_pi_apply 0
      change Measurable (fun path : AdaptiveInfinitePath BinaryOutcome =>
        f0 (path 0))
      exact hf0.comp hcoord
  | succ k =>
      let f := fun z : GeneralSchedulePrefix k × BinaryOutcome =>
        generalScheduleProspectiveResponseNoise theta
          (generalSchedulePrefixAxis schedule b k z.1) z.2
      have hf : Measurable f := measurable_of_countable f
      have hpair : Measurable
          (fun path : AdaptiveInfinitePath BinaryOutcome =>
            (Preorder.frestrictLe k path, path (k + 1))) :=
        (Preorder.measurable_frestrictLe k).prodMk
          (measurable_pi_apply (k + 1))
      change Measurable (fun path : AdaptiveInfinitePath BinaryOutcome =>
        f (Preorder.frestrictLe k path, path (k + 1)))
      exact hf.comp hpair

/-- At every interior truth point, raw response noise is pointwise bounded by
two. -/
theorem generalScheduleActualResponseNoise_norm_le_two
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 -> Real)
    (theta : OneQubitPhysicalParameter)
    (hInterior : QubitOracle.blochNormSq theta.1 < 1)
    (n : Nat) (path : AdaptiveInfinitePath BinaryOutcome) :
    ‖generalScheduleActualResponseNoise schedule b theta n path‖ <= 2 := by
  let t := QubitOracle.blochDot theta.1
    (generalScheduleActualAxis schedule b path n)
  have htSq : t ^ 2 < 1 := by
    exact generalScheduleActualProjection_sq_lt_one
      schedule b theta hInterior path n
  have ht : |t| <= 1 := by
    have htUpper : t <= 1 := by
      nlinarith [sq_nonneg (t - 1)]
    have htLower : -1 <= t := by
      nlinarith [sq_nonneg (t + 1)]
    exact abs_le.2 ⟨htLower, htUpper⟩
  have hy : |(path n).sign| = 1 := by
    cases path n <;> simp [BinaryOutcome.sign]
  change |(path n).sign - t| <= 2
  calc
    |(path n).sign - t| <= |(path n).sign| + |t| := abs_sub _ _
    _ <= 1 + 1 := by rw [hy]; exact add_le_add le_rfl ht
    _ = 2 := by norm_num

theorem generalScheduleActualResponseNoise_integrable
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 -> Real)
    (theta : OneQubitPhysicalParameter)
    (hInterior : QubitOracle.blochNormSq theta.1 < 1) (n : Nat) :
    Integrable (generalScheduleActualResponseNoise schedule b theta n)
      (generalScheduleAdaptiveBornPathMeasure schedule b theta) := by
  apply Integrable.of_bound
    (generalScheduleActualResponseNoise_measurable
      schedule b theta n).aestronglyMeasurable 2
  filter_upwards [] with path
  exact generalScheduleActualResponseNoise_norm_le_two
    schedule b theta hInterior n path

/-- The next raw response noise is conditionally centered for the natural
coordinate filtration of the literal adaptive path. -/
theorem generalScheduleActualResponseNoise_condExp_zero
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 -> Real)
    (theta : OneQubitPhysicalParameter)
    (hInterior : QubitOracle.blochNormSq theta.1 < 1) (k : Nat) :
    (generalScheduleAdaptiveBornPathMeasure schedule b theta)[
        generalScheduleActualResponseNoise schedule b theta (k + 1) |
        (MeasureTheory.Filtration.piLE k :
          MeasurableSpace (AdaptiveInfinitePath BinaryOutcome))]
      =ᵐ[generalScheduleAdaptiveBornPathMeasure schedule b theta] 0 := by
  rw [MeasureTheory.Filtration.piLE_eq_comap_frestrictLe]
  let mu := generalScheduleAdaptiveBornPathMeasure schedule b theta
  let X : AdaptiveInfinitePath BinaryOutcome -> GeneralSchedulePrefix k :=
    Preorder.frestrictLe k
  let Ynext := fun path : AdaptiveInfinitePath BinaryOutcome => path (k + 1)
  let f := fun z : GeneralSchedulePrefix k × BinaryOutcome =>
    generalScheduleProspectiveResponseNoise theta
      (generalSchedulePrefixAxis schedule b k z.1) z.2
  have hX : Measurable X := Preorder.measurable_frestrictLe k
  have hYnext : Measurable Ynext := measurable_pi_apply (k + 1)
  have hf : StronglyMeasurable f :=
    (measurable_of_countable f).stronglyMeasurable
  have hfInt : Integrable (fun path => f (X path, Ynext path)) mu := by
    change Integrable
      (generalScheduleActualResponseNoise schedule b theta (k + 1))
      (generalScheduleAdaptiveBornPathMeasure schedule b theta)
    exact generalScheduleActualResponseNoise_integrable
      schedule b theta hInterior (k + 1)
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
    exact integral_generalScheduleIonescuResponseNoise_eq_zero
      schedule b theta k (X path)
  have hFinal := hCondExp.trans hZero
  have hResponseFunction :
      (fun path => f (X path, Ynext path)) =
        generalScheduleActualResponseNoise schedule b theta (k + 1) := by
    funext path
    rfl
  rw [hResponseFunction] at hFinal
  simpa [mu, X, generalScheduleAdaptiveBornPathMeasure] using hFinal

/-- Centered response at global pilot-block rank `r` and Pauli coordinate
`j`. -/
def generalSchedulePilotNoise
    (schedule : CumulativePauliPilotBatchSchedule)
    (theta : OneQubitPhysicalParameter) (r : Nat) (j : Fin 3) :
    AdaptiveInfinitePath BinaryOutcome -> Real :=
  fun path =>
    (path (generalSchedulePilotShotRank schedule
      (generalSchedulePilotBlockOfRank schedule r) j)).sign - theta.1 j

/-- The pilot noise is exactly the generic response noise at that literal
shot. -/
theorem generalScheduleActualResponseNoise_pilotShot
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 -> Real)
    (theta : OneQubitPhysicalParameter) (r : Nat) (j : Fin 3) :
    generalScheduleActualResponseNoise schedule b theta
      (generalSchedulePilotShotRank schedule
        (generalSchedulePilotBlockOfRank schedule r) j) =
      generalSchedulePilotNoise schedule theta r j := by
  funext path
  simp [generalScheduleActualResponseNoise,
    generalScheduleProspectiveResponseNoise, generalScheduleActualAxis,
    generalSchedulePilotNoise, generalScheduleHistoryAxis_pilotShot,
    blochDot_qubitPauliCoordinateAxis]

theorem generalSchedulePilotNoise_measurable
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 -> Real)
    (theta : OneQubitPhysicalParameter) (r : Nat) (j : Fin 3) :
    Measurable (generalSchedulePilotNoise schedule theta r j) := by
  rw [<- generalScheduleActualResponseNoise_pilotShot schedule b theta r j]
  exact generalScheduleActualResponseNoise_measurable schedule b theta _

theorem generalSchedulePilotNoise_norm_le_two
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 -> Real)
    (theta : OneQubitPhysicalParameter)
    (hInterior : QubitOracle.blochNormSq theta.1 < 1)
    (r : Nat) (j : Fin 3) (path : AdaptiveInfinitePath BinaryOutcome) :
    ‖generalSchedulePilotNoise schedule theta r j path‖ <= 2 := by
  rw [<- generalScheduleActualResponseNoise_pilotShot schedule b theta r j]
  exact generalScheduleActualResponseNoise_norm_le_two
    schedule b theta hInterior _ path

/-- Immediate-history conditional centering of each pilot noise after the
first globally decoded pilot block. -/
theorem generalSchedulePilotNoise_condExp_immediate
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 -> Real)
    (theta : OneQubitPhysicalParameter)
    (hInterior : QubitOracle.blochNormSq theta.1 < 1)
    (r : Nat) (j : Fin 3) :
    let t := generalSchedulePilotShotRank schedule
      (generalSchedulePilotBlockOfRank schedule (r + 1)) j
    (generalScheduleAdaptiveBornPathMeasure schedule b theta)[
        generalSchedulePilotNoise schedule theta (r + 1) j |
        (MeasureTheory.Filtration.piLE (t - 1) :
          MeasurableSpace (AdaptiveInfinitePath BinaryOutcome))]
      =ᵐ[generalScheduleAdaptiveBornPathMeasure schedule b theta] 0 := by
  dsimp only
  let t := generalSchedulePilotShotRank schedule
    (generalSchedulePilotBlockOfRank schedule (r + 1)) j
  have htPos : 0 < t :=
    generalSchedulePilotShotRank_blockOfRank_succ_pos schedule r j
  have ht : t - 1 + 1 = t := Nat.sub_add_cancel (by omega)
  have h := generalScheduleActualResponseNoise_condExp_zero
    schedule b theta hInterior (t - 1)
  rw [ht] at h
  rw [generalScheduleActualResponseNoise_pilotShot
    schedule b theta (r + 1) j] at h
  exact h

end

end QubitOracle.Paper
