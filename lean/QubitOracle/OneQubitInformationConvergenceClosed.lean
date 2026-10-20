import QubitOracle.OneQubitFiniteCoordinateCMT

/-!
# Closed one-qubit information convergence in probability

The finite-coordinate continuous-mapping premise from the preceding source
candidate is now discharged.  The mixed and pure endpoints below assume only
coordinatewise pilot consistency in probability, the physical truth
conditions, and nondegeneracy of the local continuous frame.
-/

open Filter MeasureTheory

namespace QubitOracle

open Paper

/-- The mixed directional controller requires a nonzero interior Bloch truth.
The strict lower bound excludes the maximally mixed state, where no preferred
truth direction exists; the strict upper bound is the physical interiority
condition used by the Bernoulli Fisher denominators. -/
def MixedNonzeroInteriorTruth (theta : Fin 3 → ℝ) : Prop :=
  0 < blochNormSq theta ∧ blochNormSq theta < 1

/-- Closed mixed endpoint.  Information convergence is a conclusion, not a
premise. -/
theorem mixedLocalInformation_entrywise_convergesInProbability_closed
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (b theta : Fin 3 → ℝ) (xHat : ℕ → Ω → Fin 3 → ℝ)
    (hPilot : BlochCoordinatewiseConvergesInProbability μ xHat theta)
    (hTruth : MixedNonzeroInteriorTruth theta)
    (hSeed : LocalFrameSeedNonparallelAt b theta) :
    MatrixEntrywiseEpsilonConvergesInProbability μ
      (fun n ω => mixedLocalSafeguardedPerObservationInformation
        b theta (xHat n ω))
      (mixedOraclePerObservationInformation theta) := by
  obtain ⟨hRadialPositive, hInterior⟩ := hTruth
  have hTangentPositive :
      0 < blochNormSq (localFrameFirstResidual b theta) := by
    simpa only [LocalFrameSeedNonparallelAt] using hSeed
  exact mixedLocalInformation_entrywise_convergesInProbability
    μ (finiteCoordinateContinuousMappingProbabilityContract μ)
    b theta xHat hPilot hInterior hRadialPositive hTangentPositive

/-- Closed pure endpoint.  Unit truth supplies the positive radial denominator;
the nonparallel seed supplies the positive Gram--Schmidt denominator. -/
theorem pureLocalInformation_entrywise_convergesInProbability_closed
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (b r : Fin 3 → ℝ) (xHat : ℕ → Ω → Fin 3 → ℝ)
    (hPilot : BlochCoordinatewiseConvergesInProbability μ xHat r)
    (hTruthUnit : blochNormSq r = 1)
    (hSeed : LocalFrameSeedNonparallelAt b r) :
    MatrixEntrywiseEpsilonConvergesInProbability μ
      (fun n ω => pureLocalSafeguardedPerObservationInformation
        b r (xHat n ω))
      (pureOraclePerObservationInformation r) := by
  have hRadialPositive : 0 < blochNormSq r := by
    simpa [hTruthUnit] using (show (0 : ℝ) < 1 from zero_lt_one)
  have hTangentPositive :
      0 < blochNormSq (localFrameFirstResidual b r) := by
    simpa only [LocalFrameSeedNonparallelAt] using hSeed
  exact pureLocalInformation_entrywise_convergesInProbability
    μ (finiteCoordinateContinuousMappingProbabilityContract μ)
    b r xHat hPilot hTruthUnit hRadialPositive hTangentPositive

namespace Label

/-- Combined paper-facing mixed/pure endpoint on one probability space.  Its
premises contain neither information convergence nor a continuous-mapping
contract. -/
theorem eq_SI_information_convergence_in_probability_closed_qubit
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (mixedSeed pureSeed mixedTruth pureTruth : Fin 3 → ℝ)
    (mixedHat pureHat : ℕ → Ω → Fin 3 → ℝ)
    (hMixedPilot : BlochCoordinatewiseConvergesInProbability
      μ mixedHat mixedTruth)
    (hPurePilot : BlochCoordinatewiseConvergesInProbability
      μ pureHat pureTruth)
    (hMixedTruth : MixedNonzeroInteriorTruth mixedTruth)
    (hPureTruthUnit : blochNormSq pureTruth = 1)
    (hMixedSeed : LocalFrameSeedNonparallelAt mixedSeed mixedTruth)
    (hPureSeed : LocalFrameSeedNonparallelAt pureSeed pureTruth) :
    MatrixEntrywiseEpsilonConvergesInProbability μ
        (fun n ω => mixedLocalSafeguardedPerObservationInformation
          mixedSeed mixedTruth (mixedHat n ω))
        (mixedOraclePerObservationInformation mixedTruth) ∧
      MatrixEntrywiseEpsilonConvergesInProbability μ
        (fun n ω => pureLocalSafeguardedPerObservationInformation
          pureSeed pureTruth (pureHat n ω))
        (pureOraclePerObservationInformation pureTruth) := by
  exact ⟨
    mixedLocalInformation_entrywise_convergesInProbability_closed
      μ mixedSeed mixedTruth mixedHat hMixedPilot hMixedTruth hMixedSeed,
    pureLocalInformation_entrywise_convergesInProbability_closed
      μ pureSeed pureTruth pureHat hPurePilot hPureTruthUnit hPureSeed⟩

end Label
end QubitOracle
