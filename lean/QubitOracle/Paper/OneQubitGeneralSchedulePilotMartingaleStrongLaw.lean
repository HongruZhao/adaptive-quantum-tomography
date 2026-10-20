import QubitOracle.Paper.OneQubitGeneralScheduleAdaptiveResponseCondExp
import QubitOracle.Paper.BoundedMartingaleAzumaStrongLaw

/-!
# Strong law for the actual arbitrary-schedule pilot subsequence

The physical pilot shots may be arbitrarily sparse.  We therefore compress
the natural path filtration to the strictly increasing pilot-shot times and
apply the source-free bounded martingale-difference strong law at pilot-block
scale, not at total-observation scale.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

noncomputable section

local instance generalSchedulePilotSLLNMeasurableSpaceBinaryOutcome :
    MeasurableSpace BinaryOutcome := ⊤

local instance generalSchedulePilotSLLNNonemptyBinaryOutcome :
    Nonempty BinaryOutcome := ⟨.plus⟩

/-- Literal shot time of global pilot-block rank `r` in coordinate `j`. -/
def generalSchedulePilotShotTime
    (schedule : CumulativePauliPilotBatchSchedule) (j : Fin 3)
    (r : Nat) : Nat :=
  generalSchedulePilotShotRank schedule
    (generalSchedulePilotBlockOfRank schedule r) j

theorem generalSchedulePilotShotTime_strictMono
    (schedule : CumulativePauliPilotBatchSchedule) (j : Fin 3) :
    StrictMono (generalSchedulePilotShotTime schedule j) := by
  exact generalSchedulePilotShotRank_blockOfRank_strictMono schedule j

/-- The pilot-block filtration reveals the literal path through the shot time
of the current global pilot block. -/
def generalSchedulePilotFiltration
    (schedule : CumulativePauliPilotBatchSchedule) (j : Fin 3) :
    Filtration Nat
      (inferInstance : MeasurableSpace
        (AdaptiveInfinitePath BinaryOutcome)) where
  seq r := MeasureTheory.Filtration.piLE
    (generalSchedulePilotShotTime schedule j r)
  mono' := by
    intro r s hrs
    exact MeasureTheory.Filtration.piLE.mono
      ((generalSchedulePilotShotTime_strictMono schedule j).monotone hrs)
  le' := fun r => MeasureTheory.Filtration.piLE.le
    (generalSchedulePilotShotTime schedule j r)

/-- A pilot noise is strongly measurable at its compressed pilot time. -/
theorem generalSchedulePilotNoise_stronglyMeasurable_piLE
    (schedule : CumulativePauliPilotBatchSchedule)
    (theta : OneQubitPhysicalParameter) (r : Nat) (j : Fin 3) :
    StronglyMeasurable[
      MeasureTheory.Filtration.piLE
        (generalSchedulePilotShotTime schedule j r)]
      (generalSchedulePilotNoise schedule theta r j) := by
  let t := generalSchedulePilotShotTime schedule j r
  let g : ((i : ↥(Finset.Iic t)) ->
      AdaptiveOutcomeProcess BinaryOutcome i.1) -> Real :=
    fun pref => (pref ⟨t, Finset.mem_Iic.mpr le_rfl⟩).sign - theta.1 j
  have hfactor :
      generalSchedulePilotNoise schedule theta r j =
        g.comp (Preorder.frestrictLe t) := by
    funext path
    rfl
  rw [MeasureTheory.Filtration.piLE_eq_comap_frestrictLe]
  rw [hfactor]
  have hg : Measurable g := measurable_of_countable g
  exact (hg.comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable

/-- Shifted pilot-noise sequence in the convention required by the bounded
martingale strong law.  Rank zero is omitted here and restored later by a
vanishing endpoint correction. -/
def generalSchedulePilotNoiseSequence
    (schedule : CumulativePauliPilotBatchSchedule)
    (theta : OneQubitPhysicalParameter) (j : Fin 3) :
    Nat -> AdaptiveInfinitePath BinaryOutcome -> Real
  | 0, _ => 0
  | r + 1, path => generalSchedulePilotNoise schedule theta (r + 1) j path

theorem generalSchedulePilotNoiseSequence_stronglyAdapted
    (schedule : CumulativePauliPilotBatchSchedule)
    (theta : OneQubitPhysicalParameter) (j : Fin 3) :
    StronglyAdapted (generalSchedulePilotFiltration schedule j)
      (generalSchedulePilotNoiseSequence schedule theta j) := by
  intro r
  cases r with
  | zero => exact stronglyMeasurable_const
  | succ r =>
      change StronglyMeasurable[
        MeasureTheory.Filtration.piLE
          (generalSchedulePilotShotTime schedule j (r + 1))]
        (generalSchedulePilotNoise schedule theta (r + 1) j)
      exact generalSchedulePilotNoise_stronglyMeasurable_piLE
        schedule theta (r + 1) j

/-- Conditional centering survives compression from immediate physical time
to the preceding pilot time by the tower property. -/
theorem generalSchedulePilotNoiseSequence_condExp_zero
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 -> Real)
    (theta : OneQubitPhysicalParameter)
    (hInterior : QubitOracle.blochNormSq theta.1 < 1)
    (r : Nat) (j : Fin 3) :
    (generalScheduleAdaptiveBornPathMeasure schedule b theta)[
        generalSchedulePilotNoiseSequence schedule theta j (r + 1) |
        generalSchedulePilotFiltration schedule j r]
      =ᵐ[generalScheduleAdaptiveBornPathMeasure schedule b theta] 0 := by
  let mu := generalScheduleAdaptiveBornPathMeasure schedule b theta
  let tPrev := generalSchedulePilotShotTime schedule j r
  let tNext := generalSchedulePilotShotTime schedule j (r + 1)
  have htime : tPrev < tNext :=
    generalSchedulePilotShotTime_strictMono schedule j (Nat.lt_succ_self r)
  have hle : tPrev <= tNext - 1 := by omega
  have hImmediate :
      mu[generalSchedulePilotNoise schedule theta (r + 1) j |
        (MeasureTheory.Filtration.piLE (tNext - 1) :
          MeasurableSpace (AdaptiveInfinitePath BinaryOutcome))] =ᵐ[mu] 0 := by
    simpa [mu, tNext, generalSchedulePilotShotTime] using
      generalSchedulePilotNoise_condExp_immediate
        schedule b theta hInterior r j
  have hTower := condExp_condExp_of_le
    (MeasureTheory.Filtration.piLE.mono hle)
    (MeasureTheory.Filtration.piLE.le (tNext - 1))
    (μ := mu)
    (f := generalSchedulePilotNoise schedule theta (r + 1) j)
  change
    mu[generalSchedulePilotNoise schedule theta (r + 1) j |
      MeasureTheory.Filtration.piLE tPrev] =ᵐ[mu] 0
  calc
    mu[generalSchedulePilotNoise schedule theta (r + 1) j |
        MeasureTheory.Filtration.piLE tPrev] =ᵐ[mu]
      mu[mu[generalSchedulePilotNoise schedule theta (r + 1) j |
          MeasureTheory.Filtration.piLE (tNext - 1)] |
        MeasureTheory.Filtration.piLE tPrev] := hTower.symm
    _ =ᵐ[mu]
      mu[(0 : AdaptiveInfinitePath BinaryOutcome -> Real) |
        MeasureTheory.Filtration.piLE tPrev] :=
      condExp_congr_ae hImmediate
    _ =ᵐ[mu] 0 := by rw [condExp_zero]

/-- Source-free strong law for the shifted actual pilot subsequence. -/
theorem generalSchedulePilotNoiseSequence_average_ae_tendsto_zero
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 -> Real)
    (theta : OneQubitPhysicalParameter)
    (hInterior : QubitOracle.blochNormSq theta.1 < 1)
    (j : Fin 3) :
    ∀ᵐ path ∂generalScheduleAdaptiveBornPathMeasure schedule b theta,
      Tendsto
        (fun N : Nat => (N : Real)⁻¹ *
          ∑ r ∈ Finset.range (N + 1),
            generalSchedulePilotNoiseSequence schedule theta j r path)
        atTop (nhds 0) := by
  let mu := generalScheduleAdaptiveBornPathMeasure schedule b theta
  letI : IsProbabilityMeasure mu :=
    generalScheduleAdaptiveBornPathMeasure_isProbability schedule b theta
  exact boundedMartingaleDifference_average_ae_tendsto_zero
    mu (generalSchedulePilotFiltration schedule j)
    (generalSchedulePilotNoiseSequence schedule theta j)
    (generalSchedulePilotNoiseSequence_stronglyAdapted schedule theta j)
    (by funext path; rfl)
    (fun r => generalSchedulePilotNoiseSequence_condExp_zero
      schedule b theta hInterior r j)
    2 (by norm_num)
    (by
      intro r path
      cases r with
      | zero => simp [generalSchedulePilotNoiseSequence]
      | succ r =>
          exact generalSchedulePilotNoise_norm_le_two
            schedule b theta hInterior (r + 1) j path)

end

end QubitOracle.Paper
