import QubitOracle.Paper.OneQubitGeneralSchedulePilotMartingaleStrongLaw

/-!
# Ordinary pilot-rank average on the actual adaptive path

The compressed Azuma strong law omits rank zero to avoid a special initial
conditional-expectation case.  Here the omitted first term and the shifted
last term are restored by an explicit bounded endpoint correction.
-/

namespace QubitOracle.Paper

open Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- Average of the first `N` actual centered Pauli pilot responses. -/
def generalSchedulePilotNoiseAverage
    (schedule : CumulativePauliPilotBatchSchedule)
    (theta : OneQubitPhysicalParameter) (j : Fin 3)
    (path : AdaptiveInfinitePath BinaryOutcome) (N : Nat) : Real :=
  (N : Real)⁻¹ *
    ∑ r ∈ Finset.range N, generalSchedulePilotNoise schedule theta r j path

/-- Shifted average delivered directly by the compressed martingale strong
law. -/
def generalScheduleShiftedPilotNoiseAverage
    (schedule : CumulativePauliPilotBatchSchedule)
    (theta : OneQubitPhysicalParameter) (j : Fin 3)
    (path : AdaptiveInfinitePath BinaryOutcome) (N : Nat) : Real :=
  (N : Real)⁻¹ *
    ∑ r ∈ Finset.range (N + 1),
      generalSchedulePilotNoiseSequence schedule theta j r path

theorem generalSchedulePilotNoiseSequence_sum_eq_shifted
    (schedule : CumulativePauliPilotBatchSchedule)
    (theta : OneQubitPhysicalParameter) (j : Fin 3)
    (path : AdaptiveInfinitePath BinaryOutcome) (N : Nat) :
    (∑ r ∈ Finset.range (N + 1),
        generalSchedulePilotNoiseSequence schedule theta j r path) =
      ∑ r ∈ Finset.range N,
        generalSchedulePilotNoise schedule theta (r + 1) j path := by
  rw [Finset.sum_range_succ']
  simp [generalSchedulePilotNoiseSequence]

/-- Difference between the ordinary and shifted pilot averages. -/
def generalSchedulePilotEndpointCorrection
    (schedule : CumulativePauliPilotBatchSchedule)
    (theta : OneQubitPhysicalParameter) (j : Fin 3)
    (path : AdaptiveInfinitePath BinaryOutcome) (N : Nat) : Real :=
  (N : Real)⁻¹ *
    (generalSchedulePilotNoise schedule theta 0 j path -
      generalSchedulePilotNoise schedule theta N j path)

theorem generalSchedulePilotEndpointCorrection_norm_le
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 -> Real)
    (theta : OneQubitPhysicalParameter)
    (hInterior : QubitOracle.blochNormSq theta.1 < 1)
    (j : Fin 3) (path : AdaptiveInfinitePath BinaryOutcome) (N : Nat) :
    ‖generalSchedulePilotEndpointCorrection
      schedule theta j path N‖ <= 4 * (N : Real)⁻¹ := by
  have h0 : |generalSchedulePilotNoise schedule theta 0 j path| <= 2 := by
    simpa [Real.norm_eq_abs] using
      generalSchedulePilotNoise_norm_le_two
        schedule b theta hInterior 0 j path
  have hN : |generalSchedulePilotNoise schedule theta N j path| <= 2 := by
    simpa [Real.norm_eq_abs] using
      generalSchedulePilotNoise_norm_le_two
        schedule b theta hInterior N j path
  have hdiff :
      |generalSchedulePilotNoise schedule theta 0 j path -
        generalSchedulePilotNoise schedule theta N j path| <= 4 := by
    calc
      |generalSchedulePilotNoise schedule theta 0 j path -
          generalSchedulePilotNoise schedule theta N j path| <=
        |generalSchedulePilotNoise schedule theta 0 j path| +
          |generalSchedulePilotNoise schedule theta N j path| := abs_sub _ _
      _ <= 2 + 2 := add_le_add h0 hN
      _ = 4 := by norm_num
  have hinv : 0 <= (N : Real)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg N)
  unfold generalSchedulePilotEndpointCorrection
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hinv]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hdiff hinv

theorem generalSchedulePilotEndpointCorrection_tendsto_zero
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 -> Real)
    (theta : OneQubitPhysicalParameter)
    (hInterior : QubitOracle.blochNormSq theta.1 < 1)
    (j : Fin 3) (path : AdaptiveInfinitePath BinaryOutcome) :
    Tendsto
      (generalSchedulePilotEndpointCorrection schedule theta j path)
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun N => norm_nonneg _
  · exact Filter.Eventually.of_forall fun N =>
      generalSchedulePilotEndpointCorrection_norm_le
        schedule b theta hInterior j path N
  · have hinv : Tendsto (fun N : Nat => (N : Real)⁻¹)
        atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hinv :
        Tendsto (fun N : Nat => 4 * (N : Real)⁻¹)
          atTop (nhds (4 * 0)))

/-- Exact endpoint-correction identity between the ordinary and shifted
averages. -/
theorem generalSchedulePilotNoiseAverage_eq_shifted_add_endpoint
    (schedule : CumulativePauliPilotBatchSchedule)
    (theta : OneQubitPhysicalParameter) (j : Fin 3)
    (path : AdaptiveInfinitePath BinaryOutcome) (N : Nat) :
    generalSchedulePilotNoiseAverage schedule theta j path N =
      generalScheduleShiftedPilotNoiseAverage schedule theta j path N +
        generalSchedulePilotEndpointCorrection schedule theta j path N := by
  have hfirst := Finset.sum_range_succ'
    (fun r => generalSchedulePilotNoise schedule theta r j path) N
  have hlast := Finset.sum_range_succ
    (fun r => generalSchedulePilotNoise schedule theta r j path) N
  have hsum :
      (∑ r ∈ Finset.range N,
          generalSchedulePilotNoise schedule theta r j path) =
        (∑ r ∈ Finset.range N,
          generalSchedulePilotNoise schedule theta (r + 1) j path) +
        generalSchedulePilotNoise schedule theta 0 j path -
        generalSchedulePilotNoise schedule theta N j path := by
    linarith
  unfold generalSchedulePilotNoiseAverage
    generalScheduleShiftedPilotNoiseAverage
    generalSchedulePilotEndpointCorrection
  rw [generalSchedulePilotNoiseSequence_sum_eq_shifted]
  rw [hsum]
  ring

/-- Almost-sure strong law for the ordinary first-`N` pilot average on the
same literal adaptive Born trajectory. -/
theorem generalSchedulePilotNoiseAverage_ae_tendsto_zero
    (schedule : CumulativePauliPilotBatchSchedule) (b : Fin 3 -> Real)
    (theta : OneQubitPhysicalParameter)
    (hInterior : QubitOracle.blochNormSq theta.1 < 1)
    (j : Fin 3) :
    ∀ᵐ path ∂generalScheduleAdaptiveBornPathMeasure schedule b theta,
      Tendsto
        (generalSchedulePilotNoiseAverage schedule theta j path)
        atTop (nhds 0) := by
  filter_upwards
      [generalSchedulePilotNoiseSequence_average_ae_tendsto_zero
        schedule b theta hInterior j] with path hshifted
  have hshifted' : Tendsto
      (generalScheduleShiftedPilotNoiseAverage schedule theta j path)
      atTop (nhds 0) := by
    change Tendsto
      (fun N : Nat => (N : Real)⁻¹ *
        ∑ r ∈ Finset.range (N + 1),
          generalSchedulePilotNoiseSequence schedule theta j r path)
      atTop (nhds 0)
    exact hshifted
  have hendpoint := generalSchedulePilotEndpointCorrection_tendsto_zero
    schedule b theta hInterior j path
  have hadd := hshifted'.add hendpoint
  have hfun :
      generalSchedulePilotNoiseAverage schedule theta j path =
        fun N =>
          generalScheduleShiftedPilotNoiseAverage schedule theta j path N +
            generalSchedulePilotEndpointCorrection schedule theta j path N := by
    funext N
    exact generalSchedulePilotNoiseAverage_eq_shifted_add_endpoint
      schedule theta j path N
  rw [hfun]
  simpa using hadd

end

end QubitOracle.Paper
