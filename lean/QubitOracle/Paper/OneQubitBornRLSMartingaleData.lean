import QubitOracle.Paper.ConditionalHoeffdingRLSBridge
import QubitOracle.Paper.ProtocolRegularity
import QubitOracle.Paper.QubitRLSReduction

namespace QubitOracle.Paper

open MeasureTheory ProbabilityTheory Set

noncomputable section

/-- Physical Bloch states and physical projective axes have overlap at most one. -/
theorem abs_blochDot_le_one_of_physical_axis
    (theta axis : Fin 3 → ℝ)
    (hTheta : QubitOracle.blochNormSq theta ≤ 1)
    (hAxis : QubitOracle.blochNormSq axis ≤ 1) :
    |QubitOracle.blochDot axis theta| ≤ 1 := by
  have hOverlap := abs_blochDot_le_blochNorm theta axis hAxis
  have hNorm : blochNorm theta ≤ 1 := by
    rw [blochNorm]
    calc
      Real.sqrt (QubitOracle.blochNormSq theta) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hTheta
      _ = 1 := Real.sqrt_one
  rw [show QubitOracle.blochDot axis theta = QubitOracle.blochDot theta axis by
    exact dotProduct_comm axis theta]
  exact hOverlap.trans hNorm

/-- Signed binary response used by the clean one-qubit RLS bridge. -/
def oneQubitRLSObservation
    {Omega : Type*}
    (outcome : ℕ → Omega → QubitRLSOutcome) : ℕ → Omega → ℝ :=
  fun k omega => qubitRLSOutcomeSign (outcome k omega)

/-- Source-compatible binary Born regression noise; time zero is unused and set to zero. -/
def oneQubitRLSNoise
    {Omega : Type*}
    (theta : Fin 3 → ℝ)
    (axis : ℕ → Omega → Fin 3 → ℝ)
    (outcome : ℕ → Omega → QubitRLSOutcome) : ℕ → Omega → ℝ
  | 0, _ => 0
  | k + 1, omega => qubitRLSScalarNoise theta (axis k omega) (outcome (k + 1) omega)

@[simp] theorem oneQubitRLSNoise_zero
    {Omega : Type*}
    (theta : Fin 3 → ℝ)
    (axis : ℕ → Omega → Fin 3 → ℝ)
    (outcome : ℕ → Omega → QubitRLSOutcome)
    (omega : Omega) :
    oneQubitRLSNoise theta axis outcome 0 omega = 0 := rfl

@[simp] theorem oneQubitRLSNoise_succ
    {Omega : Type*}
    (theta : Fin 3 → ℝ)
    (axis : ℕ → Omega → Fin 3 → ℝ)
    (outcome : ℕ → Omega → QubitRLSOutcome)
    (k : ℕ) (omega : Omega) :
    oneQubitRLSNoise theta axis outcome (k + 1) omega =
      qubitRLSScalarNoise theta (axis k omega) (outcome (k + 1) omega) := rfl

/-- The signed Born response is exactly linear signal plus the clean RLS noise. -/
theorem oneQubitRLS_linearObservation
    {Omega : Type*}
    (theta : Fin 3 → ℝ)
    (axis : ℕ → Omega → Fin 3 → ℝ)
    (outcome : ℕ → Omega → QubitRLSOutcome)
    (k : ℕ) :
    oneQubitRLSObservation outcome (k + 1) =
      fun omega => (axis k omega) ⬝ᵥ theta + oneQubitRLSNoise theta axis outcome (k + 1) omega := by
  funext omega
  simp only [oneQubitRLSObservation, oneQubitRLSNoise_succ]
  rw [show (axis k omega) ⬝ᵥ theta = QubitOracle.blochDot (axis k omega) theta by rfl]
  unfold qubitRLSScalarNoise
  ring

/-- Minimal probability-space premises left after the internal Hoeffding reduction. -/
structure BinaryQubitRLSReducedProbabilityPremises
    (Omega : Type*)
    [mOmega : MeasurableSpace Omega]
    [StandardBorelSpace Omega]
    (mu : Measure Omega)
    [IsProbabilityMeasure mu]
    (theta : Fin 3 → ℝ)
    (axis : ℕ → Omega → Fin 3 → ℝ)
    (outcome : ℕ → Omega → QubitRLSOutcome) where
  filtration : Filtration ℕ mOmega
  axisAdapted : Adapted filtration axis
  noiseAdapted : Adapted filtration (oneQubitRLSNoise theta axis outcome)
  noiseMeasurable : ∀ k, Measurable[mOmega] (oneQubitRLSNoise theta axis outcome k)
  martingaleDifference : ∀ k,
    mu[oneQubitRLSNoise theta axis outcome (k + 1) | filtration k] =ᵐ[mu] 0
  physicalAxis : ∀ k omega, QubitOracle.blochNormSq (axis k omega) ≤ 1

namespace BinaryQubitRLSReducedProbabilityPremises

/-- The reduced physical premises produce exact APS data at the safe scale `R = 2`. -/
def toSelfNormalizedMartingaleData
    {Omega : Type*}
    [mOmega : MeasurableSpace Omega]
    [StandardBorelSpace Omega]
    {mu : Measure Omega}
    [IsProbabilityMeasure mu]
    {theta : Fin 3 → ℝ}
    {axis : ℕ → Omega → Fin 3 → ℝ}
    {outcome : ℕ → Omega → QubitRLSOutcome}
    (h : BinaryQubitRLSReducedProbabilityPremises Omega mu theta axis outcome)
    (hTheta : QubitOracle.blochNormSq theta ≤ 1) :
    SourceFaithfulSelfNormalized.SelfNormalizedMartingaleData Omega 3 mu 2 := by
  apply selfNormalizedMartingaleData_of_boundedCenteredNoise
    h.filtration axis (oneQubitRLSNoise theta axis outcome)
    h.axisAdapted h.noiseAdapted h.noiseMeasurable
  · intro k
    cases k with
    | zero =>
        filter_upwards [] with omega
        norm_num
    | succ k =>
        filter_upwards [] with omega
        exact abs_le.mp (abs_qubitRLSScalarNoise_le_two
          theta (axis k omega) (outcome (k + 1) omega)
          (abs_blochDot_le_one_of_physical_axis theta (axis k omega)
            hTheta (h.physicalAxis k omega)))
  · exact h.martingaleDifference

/-- The source linear observation equation is pointwise and hence almost sure. -/
theorem linearObservation_ae
    {Omega : Type*}
    [mOmega : MeasurableSpace Omega]
    [StandardBorelSpace Omega]
    {mu : Measure Omega}
    [IsProbabilityMeasure mu]
    {theta : Fin 3 → ℝ}
    {axis : ℕ → Omega → Fin 3 → ℝ}
    {outcome : ℕ → Omega → QubitRLSOutcome}
    (h : BinaryQubitRLSReducedProbabilityPremises Omega mu theta axis outcome)
    (hTheta : QubitOracle.blochNormSq theta ≤ 1)
    (k : ℕ) :
    oneQubitRLSObservation outcome (k + 1) =ᵐ[mu]
      fun omega =>
        (h.toSelfNormalizedMartingaleData hTheta).regressor k omega ⬝ᵥ theta +
          (h.toSelfNormalizedMartingaleData hTheta).noise (k + 1) omega := by
  exact Filter.Eventually.of_forall fun omega =>
    congrFun (oneQubitRLS_linearObservation theta axis outcome k) omega

end BinaryQubitRLSReducedProbabilityPremises

end

end QubitOracle.Paper
